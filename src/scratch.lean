import tangle

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

namespace id
private def range : ℕ → list ℕ
| nat.zero := []
| (nat.succ n) := 0::(list.map nat.succ (range n))
lemma append_l1_e_l2_is_append_l1_el2 {α} : ∀ (e : α) l1 l2, list.append (list.append l1 [e]) l2 = list.append l1 (e::l2) := begin
	intro e, intro l1, induction l1,
	case list.nil { intro l2, refl },
	case list.cons {
		intro l2, rw [list.append, list.append, list.append, l1_ih]
	}
end
lemma range_core_pre : Π n l, list.range_core n l = list.append (list.range_core n []) l := begin
	intro n,
	induction n,
	case nat.zero { intro l, refl },
	case nat.succ {
		intro l,
		rw [list.range_core, list.range_core],
		have h1 : list.range_core n_n (n_n::l) = list.append (list.range_core n_n []) (n_n::l), from n_ih (n_n::l),
		have h2 : list.range_core n_n [n_n] = list.append (list.range_core n_n []) [n_n], from n_ih [n_n],
		rw [h1, h2],
		have h3 : ∀ l1 l2, list.append (list.append l1 [n_n]) l2 = list.append l1 (n_n::l2), from append_l1_e_l2_is_append_l1_el2 n_n,
		rw [h3]
	}
end
lemma range_sn_eq_append_range_n_n : Π n, range (nat.succ n) = list.append (range n) [n] := begin
	intro n, induction n,
	case nat.zero { rw [range, range, list.map, list.append] },
	case nat.succ {
		rw [range, n_ih],
		have h1 : ∀ l, list.map nat.succ (list.append l [n_n]) = list.append (list.map nat.succ l) [(nat.succ n_n)], begin
			intro, induction l,
			case list.nil { simp },
			case list.cons {
				rw [list.map, list.append, list.append, list.map, l_ih]
			},
		end,
		rw [h1, ←n_ih, ←list.append, range]
	}
end
lemma prange_eq_range : Π n, range n = list.range n := begin
	intro n, induction n,
	case nat.zero { refl },
	case nat.succ {
		rw [list.range, list.range_core],
		rw [range_core_pre, ←list.range, ←n_ih],
		from range_sn_eq_append_range_n_n n_n,
	}
end
lemma len_range_n_eq_n : Π n, list.length (list.range n) = n := begin
	intro n,
	have h : Π n, list.length (list.range n) = list.length (range n), intro n, rw prange_eq_range,
	have hlen : list.length (range n) = n, begin
		induction n,
		case nat.zero { rw range, simp },
		case nat.succ {
			rw [range, list.length],
			have hlenmap : Π {α} {β} (l : list α) (f : α → β), list.length (list.map f l) = list.length l, begin
				intros,
				induction l,
				case list.nil { rw [list.map], refl },
				case list.cons {
					rw [list.map, list.length, l_ih, list.length]
				}
			end,
			rw [hlenmap, n_ih]
		}
	end,
	rw [h, hlen],
end

lemma all_nat_ge_zero : ∀ n : ℕ, n ≥ 0 := begin
	intro n, induction n,
	case nat.zero { rw [ge] },
	case nat.succ {
		rw [ge],
		sorry
		-- I don't know how to work out the cases of nat.less_than_or_equal
		-- something about all the indirection from has_le.le is causing split/cases/rw to all fail
	}
end
lemma ge_imp_not_lt : ∀ (a b : ℕ), a ≥ b → ¬ (a < b) := begin
	intro a, intro b,
	assume h,
	have hnn : ¬ ¬ (a ≥ b), from not_not_intro h,
	rw [lt_iff_not_ge], assumption
end
lemma all_le_nats_in_range : ∀ N n : ℕ, n < N → list.any (list.range N) (λ n', n = n') = tt := begin
	intros, induction N,
	case nat.zero {
		have nge0 : n ≥ 0, from all_nat_ge_zero n,
		have notlt0 : ¬ (n < 0), from ge_imp_not_lt n 0 nge0,
		contradiction
	},
	case nat.succ {
		have lt_or_eq : n < N_n ∨ n = N_n, begin
			have nle : n ≤ N_n, sorry, -- could really use some direction on nat.less_than_or_equal_to
			rw ←le_iff_lt_or_eq, assumption
		end,
		cases lt_or_eq,
		case or.inl {
			have h : list.any (list.range N_n) (λ (n' : ℕ), to_bool (n = n')) = tt, from N_ih lt_or_eq,
			have range_subset_succ : ∀ n p, (list.any (list.range n) p) = tt → (list.any (list.range (nat.succ n)) p) = tt, begin
				intro n, intro p,
				rw [list.any, list.any],
				sorry -- may need to do (range n) ⊂ (range n+1) ?
			end 
		}
	}
end
end id
def permutation.id {N} : permutation N := ⟨list.range N, ⟨id.len_range_n_eq_n N, id.all_le_nats_in_range N⟩⟩

def permutation.append {N M} : permutation N → permutation M → permutation (N + M) := sorry
def permutation.swap {N} (i j : fin N) : permutation N → permutation N := sorry
def permutation.compose {N} : permutation N → permutation N → permutation N := sorry


end link
