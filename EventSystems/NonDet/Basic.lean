
import EventSystems.Basic

structure _NDEvent (M) [Machine CTX M] (α) (β : Type)
  extends _EventRoot M α where

  action: M → α → M → Prop
  output: M → α → β → Prop

def _NDEvent_fromEvent [Machine CTX M] (ev : _Event M α β) : _NDEvent M α β :=
{
  guard := ev.guard
  action := fun m x m'' => let (_, m') := ev.action m x
                          m'' = m'
  output := fun m x z => let (y, _) := ev.action m x
                         z = y
}
