import Basic
import Tangle
open Brick

structure Graph (α : Type) where
  V: List α
  E: List (α × α)
  deriving Repr

namespace Graph
def from_edges {α : Type} [BEq α] (e : List (α × α)) : Graph α :=
  Graph.mk
    (e.foldr (fun n ns =>
        match (ns.elem n.fst, ns.elem n.snd) with
        | (true, true) => ns
        | (false, true) => n.fst::ns
        | (true, false) => n.snd::ns
        | (false, false) => n.snd::n.fst::ns
      )
      [])
    e

def contains_vert [BEq α] (g : Graph α) : α → Bool := g.V.elem
def contains_edge_directed [BEq α] (g : Graph α) : (α × α) → Bool := g.E.elem
def contains_edge [BEq α] (g : Graph α) (a b : α) : Bool :=
  (g.contains_edge_directed (a, b)) ∨ (g.contains_edge_directed (b, a))

def add_vert [BEq α] (g : Graph α) (v : α) : Graph α :=
  match (g.V.elem v) with
  | true => g
  | false => Graph.mk (v::g.V) g.E

def add_edge [BEq α] (g : Graph α) (a b : α) : Graph α :=
  match g.contains_edge a b with
  | false =>
      let V := match (g.V.elem a), (g.V.elem b) with
        | true, true => g.V
        | true, false => b::g.V
        | false, true => a::g.V
        | false, false => b::a::g.V
      Graph.mk V ((a, b)::g.E)
  | _ => g


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


def subgraphsAux {α : Type} [BEq α] (gs : List (Graph α)) : List (α × α) → List (Graph α)
  | [] => gs
  | (a, b)::e =>
      let vnew := match gs.partition (fun vs => (vs.contains_vert a) ∨ (vs.contains_vert b)) with
        | ([], eqGrps) => (Graph.mk [a,b] [(a,b)])::eqGrps
        | (g::gs', gs) => ((gs'.foldr (fun g' g => Graph.mk (g'.V.append g.V) (g'.E.append g.E)) g).add_edge a b)::gs
      subgraphsAux vnew e
/-- partitions a graph into its independent subgraphs -/
def subgraphs {α : Type} [BEq α] (g : Graph α) : List (Graph α) :=
  subgraphsAux (g.V.map (fun v => Graph.mk [v] [])) g.E

theorem ind_subgraph_idempotent [BEq α] {g : Graph α} :
  (hlen : 0 < (subgraphs g).length)
  → subgraphs ((subgraphs g)[0]) = [(subgraphs g)[0]] := sorry

namespace Example
def g : Graph Nat := Graph.from_edges [⟨0, 1⟩]
#eval g
#eval Graph.subgraphsAux (g.V.map (fun v => Graph.mk [v] [])) g.E
#eval Graph.subgraphs g
end Example

end Graph


theorem List.iota_length_eq_n {n : Nat} : (List.iota n).length = n := by
  induction n
  case zero =>
    rewrite [List.iota, List.length]
    exact Eq.refl _
  case succ n ind =>
    rewrite [List.iota, List.length, Nat.succ_eq_add_one, ind]
    exact Eq.refl _

namespace Tangle
/-- thread count is to tangle as link number is to links -/
def thread_count (t : Tangle) : Nat :=
  let acc0 : Graph.Acc := ⟨0, [], List.iota t.domain, []⟩
  let acc := Graph.acc_tangle t acc0 (Eq.symm List.iota_length_eq_n)
  -- graph from edges
  let g := Graph.from_edges acc.E
  -- add any dangling verts, shouldn't happen with tangles?
  let g := (acc.I.append acc.O).foldr (fun v g => g.add_vert v) g
  (g.subgraphs).length


namespace Example
def unknot : Tangle :=
  let unknot : Wall := [
    [Cap],
    [Cup]
  ]
  ⟨unknot, by simp [isTangle]⟩

#eval thread_count unknot


def ltrefoil : Tangle :=
  let trefoil : Wall := [
    [Cap],
    [Vert, Cap, Vert],
    [Over, Over],
    [Vert, Under, Vert],
    [Cup, Cup]
  ]
  ⟨trefoil, by simp [isTangle]⟩

#eval List.iota ltrefoil.domain
#eval Graph.acc_tangle ltrefoil ⟨0, [], List.iota ltrefoil.domain, []⟩ (Eq.symm List.iota_length_eq_n)
#eval Graph.subgraphs (Graph.from_edges [⟨0,1⟩, ⟨1,2⟩, ⟨2,0⟩])
#eval Graph.subgraphs (Graph.from_edges (Graph.acc_tangle ltrefoil ⟨0, [], List.iota ltrefoil.domain, []⟩ (Eq.symm List.iota_length_eq_n)).E)
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

