------ MODULE CallHistory ------

EXTENDS Sequences, Integers, TLC

CONSTANTS Calls
CONSTANTS Crashes

set ++ x == set \union {x}
Add(dict, key, val) == dict @@ (key :> val)
Remove(dict, key) == [i \in DOMAIN dict \ {key} |-> dict[i]]

(*--algorithm CallHistory

variables
    queue = <<>>,
    commited = 0,
    shutdownProcessor = FALSE,
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

    AllCallsProcessed == <>[](Calls = store)

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
    offset = commited + 1;
begin Process:
    while TRUE do
        either
            when Len(queue) >= offset;
ProcessCDR:
            with cdr = queue[offset]
            do
                if cdr.id \notin DOMAIN wip /\ cdr.action = "setup" then
                    wip := Add(wip, cdr.id, [offset |-> offset]);
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
\* BEGIN TRANSLATION (chksum(pcal) = "67458a95" /\ chksum(tla) = "feccaaa4")
VARIABLES queue, commited, shutdownProcessor, store, pc

(* define statement *)
CommitOffset(set, current) ==
    LET first == current + 1 IN
    IF /\ first \in set
       /\ \A i \in {j \in set: j > first}: i-1 \in set
    THEN CHOOSE i \in set: i+1 \notin set
    ELSE current

AllCallsProcessed == <>[](Calls = store)

Success == AllCallsProcessed

VARIABLES wip, processed, crashes, offset

vars == << queue, commited, shutdownProcessor, store, pc, wip, processed, 
           crashes, offset >>

ProcSet == (Calls) \cup {"Shutdown"} \cup {"Processor"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ commited = 0
        /\ shutdownProcessor = FALSE
        /\ store = {}
        (* Process Processor *)
        /\ wip = <<>>
        /\ processed = {}
        /\ crashes = 0
        /\ offset = commited + 1
        /\ pc = [self \in ProcSet |-> CASE self \in Calls -> "CallSetup"
                                        [] self = "Shutdown" -> "SignalShutdown"
                                        [] self = "Processor" -> "Process"]

CallSetup(self) == /\ pc[self] = "CallSetup"
                   /\ queue' = Append(queue, [id |-> self, action |-> "setup"])
                   /\ pc' = [pc EXCEPT ![self] = "CallComplete"]
                   /\ UNCHANGED << commited, shutdownProcessor, store, wip, 
                                   processed, crashes, offset >>

CallComplete(self) == /\ pc[self] = "CallComplete"
                      /\ \/ /\ queue' = Append(queue, [id |-> self, action |-> "complete"])
                         \/ /\ TRUE
                            /\ queue' = queue
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << commited, shutdownProcessor, store, wip, 
                                      processed, crashes, offset >>

Call(self) == CallSetup(self) \/ CallComplete(self)

SignalShutdown == /\ pc["Shutdown"] = "SignalShutdown"
                  /\ \A c \in Calls: pc[c] = "Done"
                  /\ shutdownProcessor' = TRUE
                  /\ pc' = [pc EXCEPT !["Shutdown"] = "Done"]
                  /\ UNCHANGED << queue, commited, store, wip, processed, 
                                  crashes, offset >>

Shutdown == SignalShutdown

Process == /\ pc["Processor"] = "Process"
           /\ \/ /\ Len(queue) >= offset
                 /\ pc' = [pc EXCEPT !["Processor"] = "ProcessCDR"]
              \/ /\ shutdownProcessor /\ wip = <<>> /\ offset > Len(queue)
                 /\ pc' = [pc EXCEPT !["Processor"] = "Done"]
              \/ /\ crashes < Crashes
                 /\ pc' = [pc EXCEPT !["Processor"] = "Crash"]
           /\ UNCHANGED << queue, commited, shutdownProcessor, store, wip, 
                           processed, crashes, offset >>

ProcessCDR == /\ pc["Processor"] = "ProcessCDR"
              /\ LET cdr == queue[offset] IN
                   IF cdr.id \notin DOMAIN wip /\ cdr.action = "setup"
                      THEN /\ wip' = Add(wip, cdr.id, [offset |-> offset])
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
              /\ UNCHANGED << queue, shutdownProcessor, crashes >>

Crash == /\ pc["Processor"] = "Crash"
         /\ /\ crashes' = crashes + 1
            /\ offset' = commited + 1
            /\ processed' = {}
            /\ wip' = <<>>
         /\ pc' = [pc EXCEPT !["Processor"] = "Process"]
         /\ UNCHANGED << queue, commited, shutdownProcessor, store >>

Processor == Process \/ ProcessCDR \/ Crash

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
