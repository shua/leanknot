import basic

def is_tangle : wall → Prop
| [] := false
| [bs] := true
| (bs::bs'::w) := bricks.codomain bs = bricks.domain bs' ∧ is_tangle (bs'::w)

def tangle := { w : wall // is_tangle w }

namespace tangle
@[simp] def first : tangle → list brick
| ⟨bs::w, h⟩ := bs

@[simp] private def last' : list brick → wall → list brick
| last [] := last
| _ (bs::w) := last' bs w
@[simp] def last : tangle → list brick
| ⟨bs::w, h⟩ := last' bs w

@[simp] def domain (t : tangle) : ℕ := bricks.domain (first t)
@[simp] def codomain (t : tangle) : ℕ := bricks.codomain (last t)

@[pattern] def single (bs : list brick) : tangle := ⟨[bs], trivial⟩
@[pattern] def stack (bs : list brick) : Π (t : tangle), bricks.codomain bs = domain t → tangle
| ⟨hd::tl, th⟩ hdom := ⟨bs::hd::tl, begin
	split,
	rw [hdom, domain, first],
	assumption
end⟩
end tangle

namespace planar_isotopy
lemma succ_is_add1 : ∀ n, nat.succ n = nat.add 1 n := begin
	intro n,
	induction n,
	case nat.zero { refl },
	case nat.succ { rw [nat.add,n_ih] }
end

lemma verts_dom_eq_codom : ∀ n, bricks.domain (vert_bricks n) = bricks.codomain (vert_bricks n) := begin
	intro n,
	induction n,
	case nat.zero { refl },
	case nat.succ {
		rw [vert_bricks, bricks.domain, bricks.codomain, list.map, list.map, brick.domain, brick.codomain,
			list.foldr, list.foldr,
			←bricks.domain, ←bricks.codomain, n_ih],
	}
end

theorem is_tangle_invar (a b : wall) : map a b → (is_tangle a ↔ is_tangle b) := begin
	intro heqab,
	induction heqab,
	case planar_isotopy.map.inv { symmetry, from heqab_ih },
	case planar_isotopy.map.id { trivial },
	case planar_isotopy.map.compose { rw [heqab_ih_a], assumption },
	case planar_isotopy.map.stretch {
		apply iff.intro; intro h, {
			cases h,
			split,
			{
				induction bricks.codomain heqab_a,
				case nat.zero { refl },
				case nat.succ {
					rw [vert_bricks, bricks.domain, list.map, brick.domain, list.foldr],
					have ih2 : bricks.domain (vert_bricks n) = list.foldr nat.add 0 (list.map brick.domain (vert_bricks n)), rw [←bricks.domain],
					have hsn1 : nat.succ n = nat.add 1 n, from succ_is_add1 n,
					have h1bd : nat.add 1 n = nat.add 1 _, rw [ih],
					rw [hsn1,h1bd,ih2]
				},
			}, {
				rw [h_left],
				split,
				{
					induction bricks.domain heqab_b,
					case nat.zero { refl },
					case nat.succ {
						rw [vert_bricks, bricks.codomain, list.map, brick.codomain, list.foldr],
						have hn : (list.foldr nat.add 0 (list.map brick.codomain (vert_bricks n))) = bricks.codomain (vert_bricks n),
							by rw [bricks.codomain],
						rw [hn,ih,succ_is_add1 n],
					}
				},
				{ assumption }
			}
		}, {
			split; cases h; cases h_right,
			{
				have hveq : bricks.domain (vert_bricks _) = bricks.codomain (vert_bricks _), from verts_dom_eq_codom (bricks.codomain heqab_a),
				rw [h_left,hveq,h_right_left]
			},
			{ assumption }
		}
	},
	all_goals { split; intros; repeat { split, try { refl } } },
end

end planar_isotopy


namespace reidemeister
theorem is_tangle_invar (a b : wall) : move a b → (is_tangle a ↔ is_tangle b) := begin
	intro hmovab,
	induction hmovab,
	case reidemeister.move.rev { symmetry, assumption },
	case reidemeister.move.compose { rw [hmovab_ih_a], assumption },
	all_goals { split; intros; repeat { split, try { refl } } }
end
end reidemeister

