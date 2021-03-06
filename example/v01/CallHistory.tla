------ MODULE CallHistory ------

EXTENDS Sequences, Integers, TLC

CONSTANTS Calls

Add(dict, key, val) == dict @@ (key :> val)
Remove(dict, key) == [i \in DOMAIN dict \ {key} |-> dict[i]]

(*--algorithm CallHistory

variables
    queue = <<>>,
    commited = 0,
    store = <<>>;
define

    AllCallsProcessed == <>[](
        \A i \in Calls:
           Len(SelectSeq(store, LAMBDA j: j = i)) = 1
    )

    Success == AllCallsProcessed

end define;

fair process Call \in Calls
begin CallSetup:
    queue := Append(queue, [id |-> self, action |-> "setup"]);
CallComplete:
    queue := Append(queue, [id |-> self, action |-> "complete"]);
end process;

fair process Processor = "Processor"
variables
    wip = <<>>,
    offset = commited + 1;
begin Process:
    while TRUE do
        when Len(queue) >= offset;
ProcessCDR:
        with cdr = queue[offset]
        do
            if cdr.id \notin DOMAIN wip /\ cdr.action = "setup" then
                wip := Add(wip, cdr.id, [offset |-> offset]);
            elsif cdr.id \in DOMAIN wip /\ cdr.action = "complete" then
                wip := Remove(wip, cdr.id);
                store := Append(store, cdr.id);
            end if;
        end with;
        commited := offset;
        offset := offset + 1;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "763e1c28" /\ chksum(tla) = "9bb4bed3")
VARIABLES queue, commited, store, pc

(* define statement *)
AllCallsProcessed == <>[](
    \A i \in Calls:
       Len(SelectSeq(store, LAMBDA j: j = i)) = 1
)

Success == AllCallsProcessed

VARIABLES wip, offset

vars == << queue, commited, store, pc, wip, offset >>

ProcSet == (Calls) \cup {"Processor"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ commited = 0
        /\ store = <<>>
        (* Process Processor *)
        /\ wip = <<>>
        /\ offset = commited + 1
        /\ pc = [self \in ProcSet |-> CASE self \in Calls -> "CallSetup"
                                        [] self = "Processor" -> "Process"]

CallSetup(self) == /\ pc[self] = "CallSetup"
                   /\ queue' = Append(queue, [id |-> self, action |-> "setup"])
                   /\ pc' = [pc EXCEPT ![self] = "CallComplete"]
                   /\ UNCHANGED << commited, store, wip, offset >>

CallComplete(self) == /\ pc[self] = "CallComplete"
                      /\ queue' = Append(queue, [id |-> self, action |-> "complete"])
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << commited, store, wip, offset >>

Call(self) == CallSetup(self) \/ CallComplete(self)

Process == /\ pc["Processor"] = "Process"
           /\ Len(queue) >= offset
           /\ pc' = [pc EXCEPT !["Processor"] = "ProcessCDR"]
           /\ UNCHANGED << queue, commited, store, wip, offset >>

ProcessCDR == /\ pc["Processor"] = "ProcessCDR"
              /\ LET cdr == queue[offset] IN
                   IF cdr.id \notin DOMAIN wip /\ cdr.action = "setup"
                      THEN /\ wip' = Add(wip, cdr.id, [offset |-> offset])
                           /\ store' = store
                      ELSE /\ IF cdr.id \in DOMAIN wip /\ cdr.action = "complete"
                                 THEN /\ wip' = Remove(wip, cdr.id)
                                      /\ store' = Append(store, cdr.id)
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << store, wip >>
              /\ commited' = offset
              /\ offset' = offset + 1
              /\ pc' = [pc EXCEPT !["Processor"] = "Process"]
              /\ queue' = queue

Processor == Process \/ ProcessCDR

Next == Processor
           \/ (\E self \in Calls: Call(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Calls : WF_vars(Call(self))
        /\ WF_vars(Processor)

\* END TRANSLATION

============================
