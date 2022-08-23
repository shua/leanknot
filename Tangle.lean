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

structure Graph (α : Type) [BEq α] where
  V: List α
  E: List (α × α)
  deriving Repr

namespace Graph
def from_edges {α : Type} [BEq α] (e : List (α × α)) : Graph α :=
  Graph.mk (e.foldr (fun n ns =>
      let ns := ite (ns.contains n.fst) ns (n.fst::ns)
      ite (ns.contains n.snd) ns (n.snd::ns)
    ) []) e

structure Acc where
  N: Nat
  I: List Nat
  O: List Nat
  E: List (Nat × Nat)
  deriving Repr

-- specialized List.zip which carries proof that lengths are equal
def zip_eq (a b : List Nat) (leneq : a.length = b.length) : List (Nat × Nat) := match a, b with
  | [], [] => []
  | a::a', b::b' => 
      have leneq' : a'.length = b'.length := by
        simp [List.length] at leneq
        assumption
      (Prod.mk a b)::(zip_eq a' b' leneq')

def stack (acc acc': Acc) (iolen: acc.O.length = acc'.I.length) : Acc :=
  Acc.mk
    (Nat.max acc.N acc'.N)
    acc.I
    acc'.O
    (((zip_eq acc.O acc'.I iolen).append acc.E).append acc'.E)

theorem stack_length_eq {acc acc' : Acc} {iolen : acc.O.length = acc'.I.length} :
  (stack acc acc' iolen).I.length = acc.I.length ∧ (stack acc acc' iolen).O.length = acc'.O.length := by
  rewrite [stack]
  simp

def acc_brick : Brick → Acc → Acc
  | Vert,  ⟨n, i, o, e⟩ => ⟨n+2, n::i,        (n+1)::o,        ⟨n, n+1⟩::e⟩
  | Cap,   ⟨n, i, o, e⟩ => ⟨n+2, i,           (n+1)::n::o,     ⟨n, n+1⟩::e⟩
  | Cup,   ⟨n, i, o, e⟩ => ⟨n+2, (n+1)::n::i, o,               ⟨n, n+1⟩::e⟩
  | Over,  ⟨n, i, o, e⟩ => ⟨n+4, (n+1)::n::i, (n+3)::(n+2)::o, ⟨n, n+3⟩::⟨n+1, n+2⟩::e⟩
  | Under, ⟨n, i, o, e⟩ => ⟨n+4, (n+1)::n::i, (n+3)::(n+2)::o, ⟨n, n+3⟩::⟨n+1, n+2⟩::e⟩

def acc_bricks (bs: Bricks) (acc: Acc) : Acc := match bs with
  | [] => acc
  | b::bs => acc_brick b (acc_bricks bs acc)


theorem acc_brick_io {b : Brick} {acc : Acc} :
      ((acc_brick b acc).I.length = acc.I.length + b.domain)
    ∧ ((acc_brick b acc).O.length = acc.O.length + b.codomain) := by
  cases b <;> simp [acc_brick, Brick.domain, Brick.codomain]

theorem acc_bricks_io {bs : Bricks} {acc : Acc} :
      ((acc_bricks bs acc).I.length = acc.I.length + bs.domain)
    ∧ ((acc_bricks bs acc).O.length = acc.O.length + bs.codomain) := by
  induction bs
  case nil => simp [acc_bricks, Bricks.domain, Bricks.codomain, List.foldr]
  case cons hd tl hind =>
    simp [acc_bricks, List.length, Bricks.domain, Bricks.codomain, List.foldr]
    rewrite [←Bricks.domain, ←Bricks.codomain]
    apply And.intro
    case left =>
      rewrite [Nat.add_comm hd.domain _, ←Nat.add_assoc]
      rewrite [acc_brick_io.left, hind.left]
      rfl
    case right =>
      rewrite [Nat.add_comm hd.codomain _, ←Nat.add_assoc]
      rewrite [acc_brick_io.right, hind.right]
      rfl


def acc_tangle_aux (bs : Bricks) (w : Wall) (ht : isTangle (bs::w)) (acc : Acc) (domeq : bs.domain = acc.O.length) : Acc := match w, ht with
  | [], _ =>
      let acc' := acc_bricks bs (Acc.mk acc.N [] [] [])
      have hs: acc.O.length = acc'.I.length := by
        rewrite [acc_bricks_io.left, List.length, domeq, Nat.add_comm, Nat.add_zero]
        exact Eq.refl _
      stack acc acc' hs
  | bs'::w, ht =>
      let acc' := acc_bricks bs (Acc.mk acc.N [] [] [])
      have hs: acc.O.length = acc'.I.length := by
        rewrite [acc_bricks_io.left, List.length, domeq, Nat.add_comm, Nat.add_zero]
        exact Eq.refl _
      let acc := stack acc acc' hs
      have hs' : bs'.domain = acc.O.length := by
        have codomeq : bs.codomain = acc.O.length := by
          rewrite [stack_length_eq.right, acc_bricks_io.right]
          simp
        rw [isTangle] at ht
        rw [←ht.left]
        exact codomeq
      have ht' : isTangle (bs'::w) := by
        rw [isTangle] at ht
        exact ht.right
      acc_tangle_aux bs' w ht' acc hs'
def acc_tangle : (t: Tangle) → (acc: Acc) → (domeq: t.domain = acc.O.length) → Acc
  | ⟨[], _⟩, acc, _ => acc
  | ⟨bs::w, prop⟩, acc, domeq => acc_tangle_aux bs w prop acc domeq


#eval [0, 1, 2].partition (fun n => n ≥ 1)
-- merges inhabited lists
def reduceAux {α : Type} [BEq α] (v : List (α × List α)) : List (α × α) → List (α × List α)
  | [] => v
  | ⟨a, b⟩::e =>
      let vnew := v.partition (fun vs => (vs.snd.contains a) ∨ (vs.snd.contains b))
      let vnew := match vnew.fst with
        | [] => vnew.snd
        | hd::tl => ⟨hd.fst, (hd::tl).foldr (fun x acc => x.snd.append acc) []⟩::vnew.snd
      reduceAux vnew e
def reduce {α : Type} [BEq α] (g : Graph α) : Graph α :=
  let v' := reduceAux (g.V.map (fun v => ⟨v, [v]⟩)) g.E
  let v' := v'.map Prod.fst
  Graph.mk v' []

namespace Example
def g : Graph Nat := Graph.from_edges [⟨0, 1⟩]
#eval g
#eval Graph.reduceAux (g.V.map (fun v => ⟨v, [v]⟩)) g.E
#eval Graph.reduce g
end Example

end Graph


namespace Nat
def sequence : Nat → List Nat
  | 0 => []
  | n+1 => n::(sequence n)

theorem sequence_length_eq_n {n : Nat} : (sequence n).length = n := by
  induction n
  case zero =>
    rewrite [sequence, List.length]
    exact Eq.refl _
  case succ n ind =>
    rewrite [sequence, List.length, Nat.succ_eq_add_one, ind]
    exact Eq.refl _
end Nat


namespace Tangle
/-- thread count is to tangle as link number is to links -/
def thread_count (t : Tangle) : Nat :=
  let acc0 : Graph.Acc := ⟨0, [], Nat.sequence t.domain, []⟩
  let acc := Graph.acc_tangle t acc0 (Eq.symm Nat.sequence_length_eq_n)
  let ind_graph := Graph.reduce (Graph.from_edges acc.E)
  ind_graph.V.length


namespace Example
def ltrefoil : Tangle :=
  let trefoil : Wall := [
    [Cap],
    [Vert, Cap, Vert],
    [Over, Over],
    [Vert, Under, Vert],
    [Cup, Cup]
  ]
  ⟨trefoil, by simp [isTangle]⟩

#eval Nat.sequence ltrefoil.domain
#eval Graph.acc_tangle ltrefoil ⟨0, [], Nat.sequence ltrefoil.domain, []⟩ (Eq.symm Nat.sequence_length_eq_n)
#eval Graph.reduce (Graph.from_edges [⟨0,1⟩, ⟨1,2⟩, ⟨2,0⟩])
#eval Graph.reduce (Graph.from_edges (Graph.acc_tangle ltrefoil ⟨0, [], Nat.sequence ltrefoil.domain, []⟩ (Eq.symm Nat.sequence_length_eq_n)).E)
#eval thread_count ltrefoil


def hopf_link : Tangle :=
  let hopf_link : Wall := [
    [Cap, Cap],
    [Vert, Over, Vert],
    [Vert, Over, Vert],
    [Cup, Cup]
  ]
  ⟨hopf_link, by simp [isTangle]⟩

#eval thread_count hopf_link
end Example

end Tangle


