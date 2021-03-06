------ MODULE CallHistory ------

EXTENDS Sequences, Integers, TLC

CONSTANTS Calls
CONSTANTS Crashes
CONSTANTS Timeout

set ++ x == set \union {x}
Add(dict, key, val) == dict @@ (key :> val)
Remove(dict, key) == [i \in DOMAIN dict \ {key} |-> dict[i]]

(*--algorithm CallHistory

variables
    queue = <<>>,
    commited = 0,
    shutdownProcessor = FALSE,
    failed = {},
    store = {};
define

    \* {1, 3}, 0 -> 0
    \* {2, 3}, 0 -> 0
    \* {1, 2, 3}, 0 -> 3
    CommitOffset(set, current) ==
        LET first == current + 1 IN
        IF /\ first \in set
           /\ \A i \in {j \in set: j > first}: i-1 \in set
        THEN CHOOSE i \in set: i+1 \notin set
        ELSE current

    AllCallsProcessed == <>[](Calls \ failed = store)

    Success == AllCallsProcessed

end define;

fair process Call \in Calls
begin CallSetup:
    queue := Append(queue, [id |-> self, action |-> "setup"]);
CallComplete:
    either
        queue := Append(queue, [id |-> self, action |-> "complete"]);
    or
        skip;
    end either;
end process;

fair process Shutdown = "Shutdown"
begin SignalShutdown:
    when \A c \in Calls: pc[c] = "Done";
    shutdownProcessor := TRUE;
end process;

fair process Processor = "Processor"
variables
    wip = <<>>,
    processed = {},
    crashes = 0,
    now = 0,
    offset = commited + 1;
begin Process:
    while TRUE do
        now := now + 1;
        either
            when Len(queue) >= offset;
ProcessCDR:
            with cdr = queue[offset]
            do
                if cdr.id \notin DOMAIN wip /\ cdr.action = "setup" then
                    wip := Add(wip, cdr.id, [start |-> now, offset |-> offset]);
                elsif cdr.id \in DOMAIN wip /\ cdr.action = "complete" then
                    processed := processed ++ wip[cdr.id].offset ++ offset;
                    wip := Remove(wip, cdr.id);
                    commited := CommitOffset(processed, commited);
                    store := store ++ cdr.id;
                end if;
            end with;
            offset := offset + 1;
        or
            when shutdownProcessor /\ wip = <<>> /\ offset > Len(queue);
            goto Done;
        or
            when /\ shutdownProcessor
                 /\ offset > Len(queue)
                 /\ wip /= <<>>
                 /\ \A id \in DOMAIN wip: (now - wip[id].start) < Timeout;
            skip;
        or
            when \E id \in DOMAIN wip: (now - wip[id].start) >= Timeout;
Cleanup:
            with
                id = CHOOSE id \in DOMAIN wip: (now - wip[id].start) >= Timeout,
                off = wip[id].offset
            do
                processed := processed ++ off;
                wip := Remove(wip, id);
                commited := CommitOffset(processed, commited);
                failed := failed ++ id;
            end with;
        or
            when crashes < Crashes;
Crash:
            crashes := crashes + 1 ||
            processed := {} ||
            offset := commited + 1 ||
            wip := <<>>;
        end either;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "80d6174b" /\ chksum(tla) = "a3da86fb")
VARIABLES queue, commited, shutdownProcessor, failed, store, pc

(* define statement *)
CommitOffset(set, current) ==
    LET first == current + 1 IN
    IF /\ first \in set
       /\ \A i \in {j \in set: j > first}: i-1 \in set
    THEN CHOOSE i \in set: i+1 \notin set
    ELSE current

AllCallsProcessed == <>[](Calls \ failed = store)

Success == AllCallsProcessed

VARIABLES wip, processed, crashes, now, offset

vars == << queue, commited, shutdownProcessor, failed, store, pc, wip, 
           processed, crashes, now, offset >>

ProcSet == (Calls) \cup {"Shutdown"} \cup {"Processor"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ commited = 0
        /\ shutdownProcessor = FALSE
        /\ failed = {}
        /\ store = {}
        (* Process Processor *)
        /\ wip = <<>>
        /\ processed = {}
        /\ crashes = 0
        /\ now = 0
        /\ offset = commited + 1
        /\ pc = [self \in ProcSet |-> CASE self \in Calls -> "CallSetup"
                                        [] self = "Shutdown" -> "SignalShutdown"
                                        [] self = "Processor" -> "Process"]

CallSetup(self) == /\ pc[self] = "CallSetup"
                   /\ queue' = Append(queue, [id |-> self, action |-> "setup"])
                   /\ pc' = [pc EXCEPT ![self] = "CallComplete"]
                   /\ UNCHANGED << commited, shutdownProcessor, failed, store, 
                                   wip, processed, crashes, now, offset >>

CallComplete(self) == /\ pc[self] = "CallComplete"
                      /\ \/ /\ queue' = Append(queue, [id |-> self, action |-> "complete"])
                         \/ /\ TRUE
                            /\ queue' = queue
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << commited, shutdownProcessor, failed, 
                                      store, wip, processed, crashes, now, 
                                      offset >>

Call(self) == CallSetup(self) \/ CallComplete(self)

SignalShutdown == /\ pc["Shutdown"] = "SignalShutdown"
                  /\ \A c \in Calls: pc[c] = "Done"
                  /\ shutdownProcessor' = TRUE
                  /\ pc' = [pc EXCEPT !["Shutdown"] = "Done"]
                  /\ UNCHANGED << queue, commited, failed, store, wip, 
                                  processed, crashes, now, offset >>

Shutdown == SignalShutdown

Process == /\ pc["Processor"] = "Process"
           /\ now' = now + 1
           /\ \/ /\ Len(queue) >= offset
                 /\ pc' = [pc EXCEPT !["Processor"] = "ProcessCDR"]
              \/ /\ shutdownProcessor /\ wip = <<>> /\ offset > Len(queue)
                 /\ pc' = [pc EXCEPT !["Processor"] = "Done"]
              \/ /\ /\ shutdownProcessor
                    /\ offset > Len(queue)
                    /\ wip /= <<>>
                    /\ \A id \in DOMAIN wip: (now' - wip[id].start) < Timeout
                 /\ TRUE
                 /\ pc' = [pc EXCEPT !["Processor"] = "Process"]
              \/ /\ \E id \in DOMAIN wip: (now' - wip[id].start) >= Timeout
                 /\ pc' = [pc EXCEPT !["Processor"] = "Cleanup"]
              \/ /\ crashes < Crashes
                 /\ pc' = [pc EXCEPT !["Processor"] = "Crash"]
           /\ UNCHANGED << queue, commited, shutdownProcessor, failed, store, 
                           wip, processed, crashes, offset >>

ProcessCDR == /\ pc["Processor"] = "ProcessCDR"
              /\ LET cdr == queue[offset] IN
                   IF cdr.id \notin DOMAIN wip /\ cdr.action = "setup"
                      THEN /\ wip' = Add(wip, cdr.id, [start |-> now, offset |-> offset])
                           /\ UNCHANGED << commited, store, processed >>
                      ELSE /\ IF cdr.id \in DOMAIN wip /\ cdr.action = "complete"
                                 THEN /\ processed' = processed ++ wip[cdr.id].offset ++ offset
                                      /\ wip' = Remove(wip, cdr.id)
                                      /\ commited' = CommitOffset(processed', commited)
                                      /\ store' = store ++ cdr.id
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << commited, store, wip, 
                                                      processed >>
              /\ offset' = offset + 1
              /\ pc' = [pc EXCEPT !["Processor"] = "Process"]
              /\ UNCHANGED << queue, shutdownProcessor, failed, crashes, now >>

Cleanup == /\ pc["Processor"] = "Cleanup"
           /\ LET id == CHOOSE id \in DOMAIN wip: (now - wip[id].start) >= Timeout IN
                LET off == wip[id].offset IN
                  /\ processed' = processed ++ off
                  /\ wip' = Remove(wip, id)
                  /\ commited' = CommitOffset(processed', commited)
                  /\ failed' = failed ++ id
           /\ pc' = [pc EXCEPT !["Processor"] = "Process"]
           /\ UNCHANGED << queue, shutdownProcessor, store, crashes, now, 
                           offset >>

Crash == /\ pc["Processor"] = "Crash"
         /\ /\ crashes' = crashes + 1
            /\ offset' = commited + 1
            /\ processed' = {}
            /\ wip' = <<>>
         /\ pc' = [pc EXCEPT !["Processor"] = "Process"]
         /\ UNCHANGED << queue, commited, shutdownProcessor, failed, store, 
                         now >>

Processor == Process \/ ProcessCDR \/ Cleanup \/ Crash

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Shutdown \/ Processor
           \/ (\E self \in Calls: Call(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Calls : WF_vars(Call(self))
        /\ WF_vars(Shutdown)
        /\ WF_vars(Processor)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

============================
