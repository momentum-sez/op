-- Op Core — Lean scaffold.
-- Placeholder for the mechanized core calculus.
-- The target obligations are listed in formal/README.md.

inductive OpSort
  | unit
  | bool
  | int
  | str
  | entityRef
  | jurisdictionRef
  | moneyAmount
  | contentDigest
  | callbackEvent
  deriving Repr, DecidableEq

theorem op_sort_refl (s : OpSort) : s = s := rfl
