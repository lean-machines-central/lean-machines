
@[simp]
def List.allI (xs : List α) (idx : Nat) (pred : Nat → α → Bool) : Bool :=
  match xs with
  | [] => true
  | (x::xs) => (pred idx x) && (List.allI xs (idx + 1) pred)

@[simp]
def List.addLast (xs : List α) (x : α) : List α :=
  match xs with
  | [] => [x]
  | (y::ys) => y :: addLast ys x
