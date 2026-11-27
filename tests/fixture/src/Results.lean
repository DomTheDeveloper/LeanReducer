module
public import Init

public section

theorem addZero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih
