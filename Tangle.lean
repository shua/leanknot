import Basic
open Brick

-- a wall is a tangle if, for every two rows of bricks,
-- the number of outputs from the first row matches the number of inputs from the second row
def isTangle : Wall → Prop
  | [] => true
  | [_] => true
  | bs::bs'::w => bs.codomain = bs'.domain ∧ isTangle (bs'::w)

def Tangle := { w : Wall // isTangle w }

namespace Tangle
def domain (t : Tangle) : Nat := match t.val with
  | [] => 0
  | bs::_ => bs.domain
def codomain (t : Tangle) : Nat := match t.val with
  | [] => 0
  | bs::w => ((bs::w).getLast List.noConfusion).codomain

theorem tangle_slice_begin_is_tangle (t : Tangle) (i : Nat) : isTangle (Wall.sliceBegin t.val i) := by
  sorry

end Tangle


namespace Equivalence
theorem verts_domain_eq_n { n : Nat } : Bricks.domain (vert_bricks n) = n := by
  induction n with
  | zero => simp
  | succ n' h =>
      simp [vert_bricks]
      rewrite [←vert_bricks, h, Brick.domain]
      -- don't know how to simplify '(match true with |true => a |false => b)' to 'a'
      simp
      apply Nat.add_comm
theorem verts_codomain_eq_n { n : Nat } : Bricks.codomain (vert_bricks n) = n := by
  induction n with
  | zero => simp
  | succ n' h =>
      simp [vert_bricks]
      rewrite [←vert_bricks, h, Brick.codomain]
      -- don't know how to simplify '(match true with |true => a |false => b)' to 'a'
      simp
      apply Nat.add_comm

theorem piso_tangle_inv : { a b : Wall } → PlanarIsotopic a b → (isTangle a = isTangle b) := by
  intro a b m
  induction m <;> simp [isTangle]
  case symm h => exact Eq.symm h
  case trans h₁ h₂ => exact Eq.trans h₁ h₂
  case slide => rewrite [verts_domain_eq_n, verts_codomain_eq_n]; simp


theorem rmove_tangle_inv : { a b : Wall } → ReidemeisterMove a b → (isTangle a = isTangle b) := by
  intro a b m
  induction m <;> simp [isTangle]
  case symm h => exact Eq.symm h
  case trans h₁ h₂ => exact Eq.trans h₁ h₂

theorem homot_tangle_inv : {a b : Wall} → Homotopic a b → isTangle a = isTangle b := by
  intro a b homt
  induction homt with
  | planar m => exact piso_tangle_inv m
  | rmove m => exact rmove_tangle_inv m
  | _ => sorry -- I have failed you :(

end Equivalence

