
import EventSystems.Event.Basic
import EventSystems.Refinement.Strong.Basic

class BiRefinement {ACTX : outParam (Type u₁)} (AM)
                 {CTX : outParam (Type u₂)} (M)
                 [Machine ACTX AM] [Machine CTX M] extends SRefinement AM M where

  unlift_lift  (m m' : M):
    Machine.invariant m
    → unlift m (lift m') = m'
