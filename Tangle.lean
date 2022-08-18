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
  | bs::_w => bs.domain
def codomain (t : Tangle) : Nat := match t.val with
  | [] => 0
  | bs::w => ((bs::w).getLast List.noConfusion).codomain

theorem tangle_slice_begin_is_tangle (t : Tangle) (i : Nat) : isTangle (Wall.sliceBegin t.val i) := by
  sorry

end Tangle

namespace PlanarIsotopy
open PlanarIsotopy

theorem verts_domain_eq_n { n : Nat } : Bricks.domain (vert_bricks n) = n := by
  induction n <;> rw [vert_bricks, Bricks.domain, List.map, List.foldr]
  case succ n' h =>
      rewrite [←Bricks.domain, h, Brick.domain]
      -- don't know how to simplify '(match true with |true => a |false => b)' to 'a'
      simp
      apply Nat.add_comm
theorem verts_codomain_eq_n { n : Nat } : Bricks.codomain (vert_bricks n) = n := by
  induction n <;> rw [vert_bricks, Bricks.codomain, List.map, List.foldr]
  case succ n' h =>
      rewrite [←Bricks.codomain, h, Brick.codomain]
      -- don't know how to simplify '(match true with |true => a |false => b)' to 'a'
      simp
      apply Nat.add_comm

theorem tangle_invariant : { a b : Wall } → Map a b → (isTangle a = isTangle b) := by
  intro a b m
  induction m
  case inv h => apply Eq.symm h
  case compose h₁ h₂ => apply Eq.trans h₁ h₂
  case stretch =>
    -- I wish I knew how to simplify Vert.domain to 1 instead of the big match, without using simp
    simp [isTangle, verts_domain_eq_n, verts_codomain_eq_n]
  all_goals { simp [isTangle] }

end PlanarIsotopy

namespace Reidemeister
theorem tangle_invariant : { a b : Wall } → Move a b → (isTangle a ↔ isTangle b) := by
  intro a b m
  induction m
  case rev h => apply Iff.symm h
  case compose h₁ h₂ => apply Iff.trans h₁ h₂
  all_goals { simp [isTangle] }

end Reidemeister


def Brick.threadEquiv : Brick → Nat → Nat → List (Int × Int)
  | Vert, i, o => [⟨o, -i⟩]
  | Cup, i, _o => [⟨-i, -(i.succ)⟩]
  | Cap, _i, o => [⟨o, o.succ⟩]
  | Over, i, o => [⟨o, -(i.succ)⟩, ⟨o.succ, -i⟩]
  | Under, i, o => [⟨o, -(i.succ)⟩, ⟨o.succ, -i⟩]

structure Bricks.threadEquivAcc where
  i: Nat
  o: Nat
  equiv: List (Int × Int)
def Bricks.threadEquivFold (b : Brick) (acc : Bricks.threadEquivAcc) : Bricks.threadEquivAcc :=
  Bricks.threadEquivAcc.mk (acc.i + b.domain) (acc.o + b.codomain) (acc.equiv.append (b.threadEquiv acc.i acc.o))
/-- returns a list of equivalencies between all threads in the domain and codomain
threads in the domain are counted up from 0, and threads in the codomain are counted down from -1 -/
def Bricks.threadEquiv (bs : Bricks) : List (Int × Int) :=
  (List.foldr Bricks.threadEquivFold (Bricks.threadEquivAcc.mk 0 1 []) bs).equiv

structure Brick.threadEquiv2Acc (ID : Type) where
  i: List ID
  o: List ID
  equiv: List (ID × ID)
def Brick.threadEquiv2 {ID : Type} (b : Brick) (acc : Brick.threadEquiv2Acc ID) (enough : b.domain ≤ acc.i.length ∧ b.codomain ≤ acc.o.length) : Brick.threadEquiv2Acc ID :=
  match b, enough with
    | Vert, h =>
      let i := acc.i[0]'(And.left h)
      let o := acc.o[0]'(And.right h)
      Brick.threadEquiv2Acc.mk (acc.i.drop 1) (acc.o.drop 1) (⟨i, o⟩ :: acc.equiv)
    | Cup, h =>
      let i1 := acc.i[0]'(@Nat.lt_trans 0 1 acc.i.length (by simp) (And.left h))
      let i2 := acc.i[1]'(And.left h)
      Brick.threadEquiv2Acc.mk (acc.i.drop 2) acc.o (⟨i1, i2⟩ :: acc.equiv)
    | Cap, h =>
      let o1 := acc.o[0]'(@Nat.lt_trans 0 1 acc.o.length (by simp) (And.right h))
      let o2 := acc.o[1]'(And.right h)
      Brick.threadEquiv2Acc.mk acc.i (acc.o.drop 2) (⟨o1, o2⟩ :: acc.equiv)
    | Over, h =>
      let i1 := acc.i[0]'(@Nat.lt_trans 0 1 acc.i.length (by simp) (And.left h))
      let i2 := acc.i[1]'(And.left h)
      let o1 := acc.o[0]'(@Nat.lt_trans 0 1 acc.o.length (by simp) (And.right h))
      let o2 := acc.o[1]'(And.right h)
      Brick.threadEquiv2Acc.mk (acc.i.drop 2) (acc.o.drop 2) (⟨i1, o2⟩ :: ⟨i2, o1⟩ :: acc.equiv)
    | Under, h =>
      let i1 := acc.i[0]'(@Nat.lt_trans 0 1 acc.i.length (by simp) (And.left h))
      let i2 := acc.i[1]'(And.left h)
      let o1 := acc.o[0]'(@Nat.lt_trans 0 1 acc.o.length (by simp) (And.right h))
      let o2 := acc.o[1]'(And.right h)
      Brick.threadEquiv2Acc.mk (acc.i.drop 2) (acc.o.drop 2) (⟨i1, o2⟩ :: ⟨i2, o1⟩ :: acc.equiv)

theorem Bricks.head_domain_le_domain (bs : Bricks) (b : Brick) : b.domain ≤ Bricks.domain (b::bs) := by
  cases b
  <;> rw [Bricks.domain, List.map, List.foldr]
  <;> apply Nat.le_add_right
theorem Bricks.head_codomain_le_codomain (bs : Bricks) (b : Brick) : b.codomain ≤ Bricks.codomain (b::bs) := by
  cases b
  <;> rw [Bricks.codomain, List.map, List.foldr]
  <;> apply Nat.le_add_right
theorem Bricks.tail_domain_le_domain (bs : Bricks) (b : Brick) : bs.domain ≤ Bricks.domain (b::bs) := by
  cases b
  <;> rw [Bricks.domain, Bricks.domain, ←Bricks.domain, List.map, List.foldr, ←Bricks.domain]
  <;> apply Nat.le_add_left
theorem Bricks.tail_codomain_le_codomain (bs : Bricks) (b : Brick) : bs.codomain ≤ Bricks.codomain (b::bs) := by
  cases b
  <;> rw [Bricks.codomain, Bricks.codomain, ←Bricks.codomain, List.map, List.foldr, ←Bricks.codomain]
  <;> apply Nat.le_add_left


theorem Bricks.threadEquiv2_enough_head_enough
  {ID : Type} {bs : Bricks} {b : Brick} {acc : Brick.threadEquiv2Acc ID}
  (enough : (Bricks.domain (b::bs)) ≤ acc.i.length ∧ (Bricks.codomain (b::bs)) ≤ acc.o.length)
  : b.domain ≤ acc.i.length ∧ b.codomain ≤ acc.o.length
  := And.intro
    (Nat.le_trans (Bricks.head_domain_le_domain bs b) enough.left)
    (Nat.le_trans (Bricks.head_codomain_le_codomain bs b) enough.right)
theorem Bricks.threadEquiv2_preserves_len
  {ID : Type} (bs : Bricks) (b : Brick) (acc : Brick.threadEquiv2Acc ID) 
  (enough : (Bricks.domain (b::bs)) ≤ acc.i.length ∧ (Bricks.codomain (b::bs)) ≤ acc.o.length)
  : bs.domain ≤ (b.threadEquiv2 acc (Bricks.threadEquiv2_enough_head_enough enough)).i.length
    ∧ bs.codomain ≤ (b.threadEquiv2 acc (Bricks.threadEquiv2_enough_head_enough enough)).o.length :=
  have add_le_length_le_drop {α : Type} {n m : Nat} {l : List α} (le_plus : m + n ≤ l.length) : n ≤ (l.drop m).length := by
      sorry

  And.intro
    (by
      have enough := enough.left
      rw [threadEquiv2]
      have add_le_length : (b.domain) + (domain bs) ≤ acc.i.length := by
        rw [domain, List.map, List.foldr, ←domain] at enough
        assumption
      cases b <;> simp <;> apply add_le_length_le_drop add_le_length
    )
    (by
      have enough := enough.right
      rw [threadEquiv2]
      have add_le_length : (b.codomain) + (codomain bs) ≤ acc.o.length := by
        rw [codomain, List.map, List.foldr, ←codomain] at enough
        assumption
      cases b <;> simp <;> apply add_le_length_le_drop add_le_length
    )

namespace Tangle
theorem bricks_domain_is_monotonic : ∀ b : Brick, ∀ bs : Bricks, b.domain ≤ Bricks.domain (b::bs) := by
  intro b bs
  induction bs
  case nil =>
    rw [Bricks.domain, List.map, List.map, List.foldr, List.foldr, Nat.add]
    apply Nat.le_of_eq
    rfl
  case cons b' bs' h =>
    have h' : Bricks.domain (b::bs') ≤ Bricks.domain (b::b'::bs') := by
      repeat rw [Bricks.domain]
      repeat rw [List.map]
      repeat rw [List.foldr]
      simp
      rw [←(Nat.add_assoc _ (Brick.domain b') _), Nat.add_comm _ (Brick.domain b'), Nat.add_assoc]
      apply Nat.le_add_left
    apply Nat.le_trans h h'


-- don't know how to calculate this yet
/-- thread count is to tangle as link number is to links -/
def threadCount (t : Tangle) : Nat := sorry

end Tangle
