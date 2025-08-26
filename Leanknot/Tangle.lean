import Leanknot.Basic
open Brick

-- a wall is a tangle if, for every two rows of bricks,
-- the number of outputs from the first row matches the number of inputs from the second row
def isTangle : Wall → Prop
  | [] => true
  | [_] => true
  | bs::bs'::w => bs.codomain = bs'.domain ∧ isTangle (bs'::w)

def Tangle := { w : Wall // isTangle w }

namespace Tangle

def domain (t : Tangle) : Nat := (t.val.head?.map Bricks.domain).getD 0
def codomain (t : Tangle) : Nat := (t.val.getLast?.map Bricks.codomain).getD 0

theorem cons_tangle_tl : isTangle (hd::tl) → isTangle tl := by
  intro t
  cases tl with
  | nil => rfl
  | cons => exact t.right

theorem append_tangle_fst : isTangle (a ++ b) → isTangle a := by
  intro t
  induction a with
  | nil => rfl
  | cons _ tl h => cases tl with
    | nil => rfl
    | cons => exact And.intro t.left (h t.right)
theorem append_tangle_snd : isTangle (a ++ b) → isTangle b := by
  intro t
  induction a with
  | nil => exact t
  | cons hd tl hind => cases tl with
    | nil => cases b with
      | nil => rfl
      | cons => exact t.right
    | cons => exact hind t.right

theorem codomain_cons {bs: Bricks} {w: Wall} {ht: isTangle (bs::w)} : w ≠ [] → Tangle.codomain ⟨bs::w, ht⟩ = Tangle.codomain ⟨w, cons_tangle_tl ht⟩ := by
  intro w_nonempty
  cases w with
  | nil => contradiction
  | cons whd wtl =>
    simp [codomain]

theorem codomain_append {a b : Wall} {ht : isTangle (a ++ b)} : b ≠ [] → Tangle.codomain ⟨a ++ b, ht⟩ = Tangle.codomain ⟨b, append_tangle_snd ht⟩ := by
  -- goal: codomain ⟨a ++ b, ht⟩ = codomain ⟨b, ...⟩
  -- since the codomain is calculated based on the last row of the tangle, if any suffix of two tangles is equivalent
  -- then their codomains are equal
  intro b_nonempty
  cases b with
  | nil => contradiction
  | cons bhd btl =>
    induction a with
    | nil => simp
    | cons ahd atl ih =>
      simp
      rw [codomain_cons]
      have : isTangle (atl ++ bhd :: btl) := by
        have is_tangle_cons : isTangle (ahd :: (atl ++ bhd :: btl)) := by
          rw [←List.cons_append]
          assumption
        exact cons_tangle_tl is_tangle_cons
      exact ih

      -- some followup proof?
      have : atl ++ bhd :: btl  ≠ [] := by
        exact List.append_ne_nil_of_right_ne_nil atl b_nonempty
      assumption


@[simp] theorem codomain_append_cons : {a : List Bricks} → {ht: isTangle (a ++ (hd::b))} →
  Tangle.codomain ⟨a ++ (hd::b), ht⟩ = Tangle.codomain ⟨hd::b, append_tangle_snd ht⟩ := Tangle.codomain_append List.noConfusion

def happend_tangle : (a b : Wall) → (hlen : a.length = b.length) → isTangle a → isTangle b → isTangle (Wall.happend a b hlen) := by
  intro a
  induction a <;> intro b <;> cases b <;> try { intro hlen; contradiction }
  case nil.nil => intros; simp [Wall.happend, isTangle]
  case cons.cons ahd atl ih bhd btl =>
    cases atl <;> cases btl <;> try { intro hlen; simp at hlen }
    case nil.nil => intros; simp [Wall.happend, isTangle]
    case cons.cons ahd' atl bhd' btl =>
      intro hlen ta tb
      simp [Wall.happend, isTangle]
      apply And.intro
      case right =>
        have cons_len : (ahd'::atl).length = (bhd'::btl).length := by
          simp; simp at hlen; exact hlen
        have ta' : isTangle (ahd'::atl) := by simp [isTangle] at ta; exact ta.right
        have tb' : isTangle (bhd'::btl) := by simp [isTangle] at tb; exact tb.right
        have ih' : isTangle (Wall.happend (ahd'::atl) (bhd'::btl) cons_len) :=
          ih (bhd'::btl) cons_len ta' tb'
        simp [Wall.happend] at ih'
        exact ih'
      case left =>
        have foldr_distr (a b : List Brick) (f : Brick → Nat) : ((a++b).map f).foldr Nat.add 0 = (a.map f).foldr Nat.add 0 + (b.map f).foldr Nat.add 0 := by
          induction a with
          | nil => simp [List.map]
          | cons hd tl h =>
            rw [List.cons_append]
            simp [List.map]
            rw [Nat.add_assoc, ←h]
            simp

        rw [Bricks.codomain, Bricks.domain]
        repeat rewrite [foldr_distr]
        repeat rewrite [←Bricks.codomain, ←Bricks.domain]
        rewrite [ta.left, tb.left]
        rfl


def happend (a b : Tangle) (hlen : a.val.length = b.val.length) : Tangle where
  val := Wall.happend a.val b.val hlen
  property := happend_tangle a.val b.val hlen a.property b.property

theorem happend_cons_tangle: isTangle (Wall.happend (a'::a) (b'::b) hlen') → isTangle (Wall.happend a b hlen) := by sorry
theorem happend_left_tangle {a b : Wall} {hlen : a.length = b.length} : isTangle (Wall.happend a b hlen) → isTangle a → isTangle b := by
  revert b
  induction a with
  | nil => intro b; intros; cases b <;> trivial
  | cons ahd a h =>
    intro b; cases b <;> intros <;> try { trivial }
    case cons.cons bhd b hlen _ _ =>
    -- need to prove (isTangle ((ahd::a).happend (bhd::b))) → isTangle (ahd::a) → isTangle b → isTangle (bhd::b)
    cases a <;> cases b <;> try { simp at hlen }
    case nil.nil => trivial
    case cons.cons ahd' a ta bhd' b tapp =>
    have h := by
      have hlen' : (ahd'::a).length = (bhd'::b).length := by
        rewrite [List.length] at hlen
        have hlen := Eq.symm hlen; rewrite [List.length] at hlen
        exact (Nat.add_right_cancel (Eq.symm hlen))
      exact @h _ hlen' (happend_cons_tangle tapp) ta.right

    -- have isTangle (bhd'::b), need to prove bhd.codomain = bhd'.domain
    have tbl : bhd.codomain = bhd'.domain := by
      have tappl := tapp.left
      simp at tappl
      rewrite [Bricks.codomain_append, Bricks.domain_append] at tappl
      rewrite [ta.left] at tappl
      exact (Nat.add_left_cancel tappl)

    exact And.intro tbl h

  -- sorry

theorem happend_right_tangle {a b : Wall} {hlen : a.length = b.length} : isTangle (Wall.happend a b hlen) → isTangle b → isTangle a := by
  sorry

@[simp] theorem wall_happend {w : Wall} {t : Tangle} {hlen : w.length = t.val.length} {tapp : isTangle (w.happend t.val hlen)}:
  ⟨(w.happend t.val hlen), tapp⟩ = Tangle.happend ⟨w, (happend_right_tangle tapp t.property)⟩ t hlen
:= sorry
@[simp] theorem happend_wall {w : Wall} {t : Tangle} {hlen : t.val.length = w.length} {tapp : isTangle (t.val.happend w hlen)}:
  ⟨(t.val.happend w hlen), tapp⟩ = Tangle.happend t ⟨w, (happend_left_tangle tapp t.property)⟩ hlen
:= sorry

@[simp] theorem domain_happend_add {a b : Tangle} {hlen: a.val.length = b.val.length}:
  Tangle.domain (a.happend b hlen) = Tangle.domain a + Tangle.domain b := by sorry
@[simp] theorem codomain_happend_add {a b : Tangle} {hlen: a.val.length = b.val.length}:
  Tangle.codomain (a.happend b hlen) = Tangle.codomain a + Tangle.codomain b := by sorry

end Tangle

namespace Equivalence

inductive Surgery : Wall → Wall → Prop
  | top : Surgery a b → (c : Wall) → Surgery (a ++ c) (b ++ c)
  | bottom : Surgery a b → (c : Wall) → Surgery (c ++ a) (c ++ b)
  | right: Surgery a b → (c : Tangle) → (h : a.length = c.val.length ∧ b.length = c.val.length) → Surgery (a.happend c.val h.left) (b.happend c.val h.right)
  | left: Surgery a b → (c : Tangle) → (h : c.val.length = a.length ∧ c.val.length = b.length) → Surgery (c.val.happend a h.left) (c.val.happend b h.right)

inductive LocalHomotopic : Wall → Wall → Prop
  | planar : PlanarIsotopic a b → LocalHomotopic a b
  | rmove : ReidemeisterMove a b → LocalHomotopic a b
  | surgery : Surgery a b → LocalHomotopic a b
  -- equiv
  | id : LocalHomotopic a a
  | symm : LocalHomotopic a b → LocalHomotopic b a
  | trans : LocalHomotopic a b → LocalHomotopic b c → LocalHomotopic a c

inductive Homotopic : Wall → Wall → Prop
  | surgery : LocalHomotopic a b → Homotopic a b
  | vflip : Homotopic a a.vflip
  | hflip : Homotopic a a.hflip
  -- equiv
  | id : Homotopic a a
  | symm : Homotopic a b → Homotopic b a
  | trans : Homotopic a b → Homotopic b c → Homotopic a c

theorem verts_boundary_eq_n { n : Nat } : Bricks.domain (vert_bricks n) = n ∧ Bricks.codomain (vert_bricks n) = n := by
  induction n with
  | zero => simp [vert_bricks, Bricks.domain, Bricks.codomain]
  | succ n' h =>
      simp [vert_bricks, List.replicate, Bricks.domain, Bricks.codomain]
      simp [vert_bricks, Bricks.domain, Bricks.codomain] at h
      rewrite [h]
      apply Nat.add_comm

-- height_eq is useful because Wall.happend requires it (and LocalHomotopic.left/right use happend)
theorem piso_height_eq : { w₁ w₂ : Wall } → PlanarIsotopic w₁ w₂ → w₁.length = w₂.length := by
  intro a b piso
  cases piso <;> rfl

theorem rmove_height_eq : { w₁ w₂ : Wall } → ReidemeisterMove w₁ w₂ → w₁.length = w₂.length := by
  intro a b rmove
  cases rmove <;> rfl

theorem surgery_height_eq : { w₁ w₂ : Wall } → Surgery w₁ w₂ → w₁.length = w₂.length := by
  intro a b srgy
  sorry

theorem homt_height_eq : { w₁ w₂ : Wall } → LocalHomotopic w₁ w₂ → w₁.length = w₂.length := by
  intro a b lhomt
  induction lhomt with
  | planar piso => exact piso_height_eq piso
  | rmove rmove => exact rmove_height_eq rmove
  | surgery srgy => exact surgery_height_eq srgy
  | id => exact Eq.refl _
  | symm _ h => exact Eq.symm h
  | trans _ _ hab hbc => exact Eq.trans hab hbc


-- boundary equivalence is useful for knot surgery proofs
theorem piso_boundary_eq : { w₁ w₂ : Wall } → PlanarIsotopic w₁ w₂ → (ht₁ : isTangle w₁) → (ht₂ : isTangle w₂)
  → Tangle.domain ⟨w₁, ht₁⟩ = Tangle.domain ⟨w₂, ht₂⟩ ∧ Tangle.codomain ⟨w₁, ht₁⟩ = Tangle.codomain ⟨w₂, ht₂⟩ := by
  sorry

theorem rmove_boundary_eq : { w₁ w₂ : Wall } → ReidemeisterMove w₁ w₂ → (ht₁ : isTangle w₁) → (ht₂ : isTangle w₂)
  → Tangle.domain ⟨w₁, ht₁⟩ = Tangle.domain ⟨w₂, ht₂⟩ ∧ Tangle.codomain ⟨w₁, ht₁⟩ = Tangle.codomain ⟨w₂, ht₂⟩ := by
  sorry

theorem surgery_boundary_eq : { w₁ w₂ : Wall } → Surgery w₁ w₂ → (ht₁ : isTangle w₁) → (ht₂ : isTangle w₂)
  → Tangle.domain ⟨w₁, ht₁⟩ = Tangle.domain ⟨w₂, ht₂⟩ ∧ Tangle.codomain ⟨w₁, ht₁⟩ = Tangle.codomain ⟨w₂, ht₂⟩
  := by
  intro a b srgy ta tb
  apply And.intro
  case left => -- domain
    induction srgy with
    | @top a b homt c h =>
      have h := (h (Tangle.append_tangle_fst ta) (Tangle.append_tangle_fst tb))
      have hlen := surgery_height_eq homt
      cases a <;> cases b <;> try { simp at hlen }
      case nil => simp
      case cons h _ _ _ _ => exact h
    | @bottom a b _ c h =>
      cases c with
      | nil => exact (h ta tb)
      | cons hd tl => simp [Tangle.domain]

    | @left a b _ c hlen h =>
      -- for some reason I can't call apply Tangle.mk
      cases c; case mk c hc =>

      have h := (h (Tangle.happend_left_tangle ta hc) (Tangle.happend_left_tangle tb hc))
      -- we want to tease out Bricks.domain statements from Tangle.domain
      -- so split out cases to [], _::_
      -- since all the lengths must be equal (hlen), we can remove a bunch of
      -- absurd cases using contradictions
      cases c <;> cases a <;> cases b <;> simp at hlen
      case nil => trivial
      case cons =>
        simp [Tangle.domain, Wall.happend]
        simp [Tangle.domain] at h
        -- have Bricks.domain ahd = Bricks.domain bhd
        -- want Bricks.domain (chd++ahd) = Bricks.domain (chd++bhd)
        repeat rewrite [Bricks.domain_append]
        rewrite [h]
        rfl

    | @right a b homt c hlen h =>
      cases c; case mk c hc =>

      have h := (h (Tangle.happend_right_tangle ta hc) (Tangle.happend_right_tangle tb hc))
      cases c <;> cases a <;> cases b <;> simp at hlen
      case nil => trivial
      case cons =>
        simp [Tangle.domain, Wall.happend]
        simp [Tangle.domain] at h
        repeat rewrite [Bricks.domain_append]
        rewrite [h]
        rfl

  case right => -- codomain
    induction srgy with
    | @top a b _ c h =>
      cases c with
      | nil => simp; exact (h (Tangle.append_tangle_fst ta) (Tangle.append_tangle_fst tb))
      | cons => repeat rewrite [Tangle.codomain_append_cons, Tangle.codomain_append_cons]; rfl

    | @bottom a b homt c h =>
      induction c with
      | nil => exact (h (Tangle.append_tangle_snd ta) (Tangle.append_tangle_snd tb))
      | cons hd tl h =>
        cases a <;> cases b
          <;> try { have hlen := surgery_height_eq homt; trivial }
        case cons h _ _ _ _ =>
          have h := (h (Tangle.cons_tangle_tl ta) (Tangle.cons_tangle_tl tb))
          repeat rewrite [Tangle.codomain_append_cons]
          repeat rewrite [Tangle.codomain_append_cons] at h
          exact h

    | @left a b _ c hlen h =>
      repeat rewrite [Tangle.happend_wall, Tangle.codomain_happend_add]
      have h := h (Tangle.happend_left_tangle ta c.property) (Tangle.happend_left_tangle tb c.property)
      rewrite [h]
      rfl
    | @right a b _ c hlen h =>
      have h := h (Tangle.happend_right_tangle ta c.property) (Tangle.happend_right_tangle tb c.property)
      repeat rewrite [Tangle.wall_happend, Tangle.codomain_happend_add]
      rewrite [h]
      rfl

theorem homt_boundary_eq : { w₁ w₂ : Wall } → LocalHomotopic w₁ w₂ → (ht₁ : isTangle w₁) → (ht₂ : isTangle w₂)
  → Tangle.domain ⟨w₁, ht₁⟩ = Tangle.domain ⟨w₂, ht₂⟩ ∧ Tangle.codomain ⟨w₁, ht₁⟩ = Tangle.codomain ⟨w₂, ht₂⟩
  := by
  intro w₁ w₂ homt ht₁ ht₂
  induction homt with
  | planar m => exact piso_boundary_eq m ht₁ ht₂
  | rmove m => exact rmove_boundary_eq m ht₁ ht₂
  | surgery m => exact surgery_boundary_eq m ht₁ ht₂
  | id => simp
  | symm homt hind =>
    have hind := hind ht₂ ht₁
    exact And.intro (Eq.symm hind.left) (Eq.symm hind.right)
  | trans homab hombc hindab hindbc =>
    have hindab := hindab ht₁
    have hindbc (ht₃ : isTangle _) := hindbc ht₃ ht₂
    -- need proof of LocalHomotopic a b → (isTangle a = isTangle b)
    -- but this proof is supposed to be a lemma for that proof ...
    sorry


theorem piso_tangle_inv : { a b : Wall } → PlanarIsotopic a b → (isTangle a = isTangle b) := by
  intro a b m
  induction m <;> simp [isTangle, codomain, Bricks.codomain, domain, Bricks.domain]
  -- case slide => rewrite [verts_boundary_eq_n.left, verts_boundary_eq_n.right]; simp
  case slide => sorry

theorem rmove_tangle_inv : { a b : Wall } → ReidemeisterMove a b → (isTangle a = isTangle b) := by
  intro a b m
  induction m <;> simp [isTangle, codomain, Bricks.codomain, domain, Bricks.domain]

theorem surgery_tangle_inv : { a b : Wall } → Surgery a b → (isTangle a = isTangle b) := by
  intro a b m
  sorry

theorem homt_tangle_inv : { a b : Wall } → LocalHomotopic a b → (isTangle a = isTangle b) := by
  intro a b homt
  induction homt with
  | planar m => exact piso_tangle_inv m
  | rmove m => exact rmove_tangle_inv m
  | surgery m => exact surgery_tangle_inv m
  | id => rfl
  | symm _ hind => exact Eq.symm hind
  | trans _ _ tab tbc => rewrite [tab, tbc]; rfl

end Equivalence
