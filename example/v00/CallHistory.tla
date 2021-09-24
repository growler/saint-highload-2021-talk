------ MODULE CallHistory ------

EXTENDS Sequences, Integers, TLC

CONSTANTS Calls

(*--algorithm CallHistory

variables
    queue = <<>>,
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
    skip;
end process;

fair process Processor = "Processor"
begin Process:
    while TRUE do
ProcessCDR:
        skip;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ce3de917" /\ chksum(tla) = "7dc5f998")
VARIABLES queue, store, pc

(* define statement *)
AllCallsProcessed == <>[](
    \A i \in Calls:
       Len(SelectSeq(store, LAMBDA j: j = i)) = 1
)

Success == AllCallsProcessed


vars == << queue, store, pc >>

ProcSet == (Calls) \cup {"Processor"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ store = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in Calls -> "CallSetup"
                                        [] self = "Processor" -> "Process"]

CallSetup(self) == /\ pc[self] = "CallSetup"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << queue, store >>

Call(self) == CallSetup(self)

Process == /\ pc["Processor"] = "Process"
           /\ pc' = [pc EXCEPT !["Processor"] = "ProcessCDR"]
           /\ UNCHANGED << queue, store >>

ProcessCDR == /\ pc["Processor"] = "ProcessCDR"
              /\ TRUE
              /\ pc' = [pc EXCEPT !["Processor"] = "Process"]
              /\ UNCHANGED << queue, store >>

Processor == Process \/ ProcessCDR

Next == Processor
           \/ (\E self \in Calls: Call(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Calls : WF_vars(Call(self))
        /\ WF_vars(Processor)

\* END TRANSLATION

============================
