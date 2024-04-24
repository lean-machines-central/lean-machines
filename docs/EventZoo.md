
The Event Zoo
=============

Basic deterministic events
--------------------------

[✓] **Initialization events**  (`EventSystems.Event.Ordinary`)

 - type : `InitEvent M α β`
 - elements : `guard`, `init`
 - constructor : `newInitEvent <spec>`
 - PO : `safety`

[✓] **Ordinary events**  (`EventSystems.Event.Ordinary`)

 - type : `OrdinaryEvent M α β`
 - elements : `guard`, `action`
 - constructor : `newEvent <spec>`
 - PO : `safety`

[✓] **Anticipated events** (`EventSystems.Event.Convergent`)

 - type : `AnticipatedEvent v M α β`
 - constructor : `newAnticipatedEvent <spec>`
 - PO : `safety`, `variant` (preorder), `nonIncreasing`

[✓] **Convergent events** (`EventSystems.Event.Convergent`)

 - type : `ConvergentEvent v M α β`
 - constructor : `newConvergentEvent <spec>`
 - PO : `safety`, `variant` (well founded), `convergence`

Basic non-deterministic events
------------------------------

[✓] **Initialization non-deterministic events**  (`EventSystems.NonDet.Ordinary`)

 - type : `InitNDEvent M α β`
 - elements : `guard`, `init`
 - constructor : `newInitNDEvent <spec>`
 - PO : `safety`, `feasibility`

[✓] **Ordinary non-deterministic events**  (`EventSystems.NonDet.Ordinary`)

 - type : `OrdinaryNDEvent M α β`
 - elements : `guard`, `effect`
 - constructor : `newNDEvent <spec>`
 - PO : `safety`, `feasibility`

[✓] **Anticipated non-deterministic events** (`EventSystems.NonDet.Convergent`)

 - type : `AnticipatedNDEvent v M α β`
 - elements : `guard`, `effect`
 - constructor : `newAnticipatedNDEvent <spec>`
 - PO : `safety`, , `feasibility`, `variant` (preorder), `nonIncreasing`

[✓] **Convergent non-deterministic events** (`EventSystems.NonDet.Convergent`)

 - type : `ConvergentNDEvent v M α β`
 - elements : `guard`, `effect`
 - constructor : `newConvergentNDEvent <spec>`
 - PO : `safety`, `feasibility`, `variant` (well founded), `convergence`

Refined deterministic events (relational refinement)
----------------------------------------------------

[✓] **Initialization refined events**  (`EventSystems.Refinement.Relational.Basic`)

 - type : `InitREvent AM M α β`
 - elements : `guard`, `init`, `abstract : InitEvent AM α β`
 - constructor : `newInitREvent <spec>`
 - PO : `safety`, `strengthening`, `simulation`

[✓] **Ordinary refined events**  (`EventSystems.Refinement.Relational.Basic`)

 - type : `OrdinaryREvent AM M α β`
 - elements : `guard`, `action`, `abstract : OrdinaryEvent AM α β
 - constructor : `newREvent <spec>`
 - PO : `safety`, `strengthening`, `simulation`

[✓] **Anticipated refined events** (`EventSystems.Refinement.Relational.Convergent`)

 - type : `AnticipatedREvent v AM M α β`
 - elements : `guard`, `action`, `abstract : OrdinaryEvent AM α β | AnticipatedEvent v AM α β`
 - constructors : `newAnticipatedfromOrdinary <spec>` | `newAnticipatedfromAnticipated <spec>` 
 - PO : `safety`, `strengthening`, `simulation`, `variant` (preorder), `nonIncreasing`

[✓] **Convergent refined events** (`EventSystems.Refinement.Relational.Convergent`)

 - type : `ConvergentREvent v AM M α β`
 - elements : `guard`, `action`, `abstract : _Event AM α β`
 - constructor : `newConvergentREvent <spec>`
 - PO : `safety`, `strengthening`, `simulation`, `variant` (well founded), `convergence`

[✓] **Abstract refined events**  (`EventSystems.Refinement.Relational.Abstract`)

(reuse of abstract events at the concrete level)

[✓] **New concrete events**  (`EventSystems.Refinement.Relational.Concrete`)

(new events at the concrete level, refining `skip`)


