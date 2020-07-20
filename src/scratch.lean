import tangle
import data.vector

namespace tangle

/- define internal change
something like
example (a b : wall) (row col : ℕ) : (is_tangle a ∧ planar_isotopy.map c d ∧ (replace a (row col) c d) = b) → is_tangle b
-/
def replace (w : wall) (row col : ℕ) (a b : wall) : (is_tangle w ∧ is_tangle a ∧ is_tangle b) → wall :=
	sorry

end tangle


namespace link

/- define knot
maybe create permutation groups from top to bottom
each brick remaps and creates or closes perm group
if only one perm group at the end, then it's a knot
-/

-- should I be using l : list (fin N)?
def permutation (N : ℕ) := { l : list ℕ // l.length = N ∧ ∀ n : ℕ, n < N → l.any (λ n', n = n') = tt }

namespace permutation
namespace id
lemma range_n_length_eq_n : ∀ n, (list.range n).length = n := sorry
lemma range_n_contains_all_lt_n : ∀ N n, n < N → (list.range N).any (λ n', n = n') = tt := sorry
end id
def id {N} : permutation N := ⟨list.range N, ⟨id.range_n_length_eq_n N, id.range_n_contains_all_lt_n N⟩⟩

namespace append
variables {N M : ℕ}
variables (l₁ l₂ : list ℕ)
lemma len_append_is_sum_len_addends : (l₁.append l₂).length = l₁.length + l₂.length := sorry
lemma len_permappend_is_sum_len_addends (hl₁len : l₁.length = N) (hl₂len : l₂.length = M): (l₁.append (l₂.map (nat.add N))).length = N + M := begin
	intros,
	rw len_append_is_sum_len_addends,
	have hlenmap : ∀ (l : list ℕ) α (f : ℕ -> α), (l.map f).length = l.length, begin
		intro l, induction l,
		case list.nil {
			intro α, intro f, rw [list.map], refl
		},
		case list.cons {
			intro α, intro f,
			rw [list.map, list.length, list.length, l_ih],
		}
	end,
	rw [hlenmap, hl₁len, hl₂len],
end
end append

def append {N M} : permutation N → permutation M → permutation (N + M)
| ⟨ln, ⟨lnlen, lnelems⟩⟩ ⟨lm, ⟨lmlen, lmelems⟩⟩ := 
	⟨ln.append (lm.map (nat.add N)), ⟨
		permutation.append.len_permappend_is_sum_len_addends ln lm lnlen lmlen,
		sorry
	⟩⟩

namespace swap
variables {N : ℕ}
variables (l : list ℕ) {hllen : l.length = N} {hlelems : ∀ n, n < N → l.any (λ n', n = n') = tt}
def list_swap (l : list ℕ) (hllen : l.length = N) : (fin N) → (fin N) → list ℕ := sorry
-- likely list.update_nth is what we're looking for...
lemma list_swap_len : ∀ (i j : fin N), (list_swap l hllen i j).length = N := sorry
lemma list_swap_elems : ∀ (i j : fin N), ∀ n, n < N → (list_swap l hllen i j).any (λ n', n = n') = tt := sorry
end swap

def swap {N} (i j : fin N) : permutation N → permutation N
| ⟨ln, ⟨lnlen, lnelems⟩⟩ := ⟨permutation.swap.list_swap ln lnlen i j, ⟨permutation.swap.list_swap_len ln i j, permutation.swap.list_swap_elems ln i j⟩⟩

namespace compose
variables {N : ℕ}
variables (l₁ l₂ : list ℕ) {hl₁len : l₁.length = N} {hl₂len : l₂.length = N}
def list_compose (l₁ l₂ : list ℕ) (h₁len : l₁.length = N) (hl₂len : l₂.length = N): list ℕ := sorry
lemma list_compose_len : (list_compose l₁ l₂ hl₁len hl₂len).length = N := sorry
lemma list_compose_elems : ∀ (n : ℕ), n < N → ((list_compose l₁ l₂ hl₁len hl₂len).any (λ n', n = n')) = tt := sorry
end compose

def compose {N} : permutation N → permutation N → permutation N
| ⟨l₁, ⟨l₁len, l₁elems⟩⟩ ⟨l₂, ⟨l₂len, l₂elems⟩⟩ :=
	⟨permutation.compose.list_compose l₁ l₂ l₁len l₂len, ⟨
		permutation.compose.list_compose_len l₁ l₂,
		permutation.compose.list_compose_elems l₁ l₂⟩⟩

end permutation

-- define links in terms of permutations
/- with each layer/brick, there are three options
1. introduce threads (cap)
2. close threads (cup)
3. permute threads (vert, over, undr)

I think it'd be useful to keep track of permutation groups, and think of a tangle as
`domain + 2*caps = codomain + 2*cups`
with permutation size = `domain + 2*caps`
there will be a cap list which maps n to n
and a cup list which maps m to m

finally linking number is # closed groups from the cap list and cup list of a link (domain = codomain = 0)
and knot is linking number = 1
-/

open brick

theorem tangle_begin_eq_end : ∀ t : tangle, t.domain + 2 * wall.capnumber t.val = t.codomain + 2 * wall.cupnumber t.val := begin
	intro t,
	induction ht : t,
	induction val,
	case list.nil {
		have hniltangle : ¬ is_tangle list.nil, begin
			rw [is_tangle], contradiction
		end,
		from absurd property hniltangle
	},
	case list.cons {
		induction val_tl,
		case list.nil {
			induction val_hd,
			case list.nil {
				simp,
			},
			case list.cons {
				-- ⟨[bs], _⟩.domain + 2 * wall.capnumber [bs] = ⟨[bs], _⟩.codomain + 2 * wall.cupnumber [bs]
				-- is_tangle ⟨[b::bs], _⟩
				-- ⟨[b::bs], _⟩.domain + 2 * wall.capnumber [b::bs] = ⟨[b::bs], _⟩.codomain + 2 * wall.cupnumber [b::bs]
				-- I think cases on b?
				induction val_hd_hd,
				case brick.Vert {
					simp, sorry
				},
				all_goals { sorry }
			}
		},
		sorry
	}
end

end link

namespace bricks
open brick
def ravel : (ℕ × list (list ℕ) × list ℕ) → (list brick) → ℕ × list (list ℕ) × list ℕ
-- tangle cases
| inpt [] := inpt
| (Nin, eqin, n::inpts)    (Vert::bs) := let (Nout, eqout, outpts) := ravel (Nin, eqin, inpts) bs in (Nout, eqout, n::outpts)
| (Nin, eqin, a::b::inpts) (Over::bs) := let (Nout, eqout, outpts) := ravel (Nin, eqin, inpts) bs in (Nout, eqout, b::a::outpts)
| (Nin, eqin, a::b::inpts) (Undr::bs) := let (Nout, eqout, outpts) := ravel (Nin, eqin, inpts) bs in (Nout, eqout, b::a::outpts)
| (Nin, eqin, inpts)       (Cap::bs)  := let (Nout, eqout, outpts) := ravel (nat.succ Nin, eqin, inpts) bs in (Nout, eqout, Nin::Nin::outpts)
| (Nin, eqin, a::b::inpts) (Cup::bs)  :=                              ravel (Nin, [a,b]::eqin, inpts) bs
-- general cases
| (Nin, eqin, [])          (Vert::bs) := let (Nout, eqout, outpts) := ravel ((nat.succ Nin), eqin, []) bs in (Nout, eqout, Nin::outpts)
| (Nin, eqin, [])          (Cup::bs)  :=                              ravel ((nat.succ Nin), eqin, []) bs
| (Nin, eqin, [])          (Over::bs) := let (Nout, eqout, outpts) := ravel (Nin + 2, eqin, [])        bs in (Nout, eqout, (nat.succ Nin)::Nin::outpts)
| (Nin, eqin, [])          (Undr::bs) := let (Nout, eqout, outpts) := ravel (Nin + 2, eqin, [])        bs in (Nout, eqout, (nat.succ Nin)::Nin::outpts)
| (Nin, eqin, [n])         (Cup::bs)  :=                              ravel ((nat.succ Nin), [Nin,n]::eqin, []) bs
| (Nin, eqin, [n])         (Over::bs) := let (Nout, eqout, outpts) := ravel (nat.succ Nin, eqin, [])   bs in (Nout, eqout, Nin::n::outpts)
| (Nin, eqin, [n])         (Undr::bs) := let (Nout, eqout, outpts) := ravel (nat.succ Nin, eqin, [])   bs in (Nout, eqout, Nin::n::outpts)

end bricks
namespace wall
def ravel : wall → (ℕ × list (list ℕ) × list ℕ) → ℕ × list (list ℕ) × list ℕ
| []      inpts := inpts
| (bs::w) inpts := ravel w (bricks.ravel inpts bs)
end wall

theorem ravel_tangle_has_no_loose_threads : ∀ t : tangle, (t.val.ravel (0, [], [])).fst = t.domain + t.val.capnumber := begin
	-- for each two rows (a,b) in a tangle, the a.domain = b.codomain, thus the only way to introduce threads is the first row of the tangle, or with caps
	sorry
end

def equiv_groups : list (list ℕ) → list (list ℕ) := sorry
-- take a list of pairs of nats, and create a list of lists of nats such that forall a,b in pairs, there is exactly one group in the output that contains a,b

def braid := { w : wall // is_tangle w ∧ w.capnumber = 0 ∧ w.cupnumber = 0 }
namespace braid
end braid
