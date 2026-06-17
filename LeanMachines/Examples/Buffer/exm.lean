


def length (l : List α) : Nat :=
  match l with
  | _ :: xs => 1 + length xs
  | [] => 0

example : length [1,2] = length [2,3] :=
by
  simp[length]
