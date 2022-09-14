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
@[inline] def last_codomain : Wall → Nat
  | [] => 0
  | [bs] => bs.codomain
  | _::bs'::w => last_codomain (bs'::w)
def codomain (t : Tangle) : Nat := last_codomain t.val

theorem cons_tangle_tl { hd : Bricks } { tl : Wall } (ht : isTangle (hd::tl)) : isTangle tl := by
  cases tl with
  | nil => simp [isTangle]
  | cons hd' tl => rewrite [isTangle] at ht; exact ht.right

theorem append_tangle_fst { a b : Wall } (ht : isTangle (List.append a b)) : isTangle a := by
  sorry

theorem append_tangle_snd { a b : Wall } (ht : isTangle (List.append a b)) : isTangle b := by
  induction a with
  | nil => rewrite [List.append] at ht; exact ht
  | cons hd tl hind =>
    rewrite [List.append] at ht
    cases tl with
    | nil =>
      rewrite [List.append] at ht
      cases b with
      | nil => rfl
      | cons =>
        rewrite [isTangle] at ht
        exact ht.right
    | cons =>
      rewrite [List.append, isTangle] at ht
      exact hind (ht.right)

theorem last_codomain_append_nempty_snd : (as bs : Wall) → (hne : bs ≠ []) → last_codomain (List.append as bs) = last_codomain bs := sorry

def happend_tangle : (a b : Wall) → (hlen : a.length = b.length) → isTangle a → isTangle b → isTangle (Wall.happend a b hlen) := by
  intro a
  induction a <;> intro b <;> cases b <;> try { intro hlen; contradiction }
  case nil.nil => intros; simp [Wall.happend, isTangle]
  case cons.cons ahd atl h bhd btl =>
    cases atl <;> cases btl <;> try { intro hlen; simp at hlen; contradiction; }
    case nil.nil => intros; simp [Wall.happend, isTangle]
    case cons.cons ahd' atl bhd' btl =>
      intro hlen ta tb
      simp [Wall.happend, isTangle]
      apply And.intro
      case right =>
        have h' := h (bhd'::btl) (by simp; simp at hlen; exact hlen) (by simp [isTangle] at ta; exact ta.right) (by simp [isTangle] at tb; exact tb.right)
        simp [Wall.happend] at h'
        exact h'
      case left =>
        have foldr_distr (a b : List Brick) (f : Brick → Nat) : ((a++b).map f).foldr Nat.add 0 = (a.map f).foldr Nat.add 0 + (b.map f).foldr Nat.add 0 := by
          induction a with
          | nil => simp [List.map, List.foldr]
          | cons hd tl h => rewrite [List.cons_append]; simp [List.map, List.foldr]; rewrite [h, Nat.add_assoc]; rfl
        rewrite [Bricks.codomain, Bricks.domain]
        repeat rewrite [foldr_distr]
        repeat rewrite [←Bricks.codomain, ←Bricks.domain]
        rewrite [ta.left, tb.left]
        rfl

def happend (a b : Tangle) (hlen : a.val.length = b.val.length) : Tangle where
  val := Wall.happend a.val b.val hlen
  property := happend_tangle a.val b.val hlen a.property b.property

def happend_left_tangle {a b : Wall} {hlen : a.length = b.length} : isTangle (Wall.happend a b hlen) → isTangle a → isTangle b := by
  sorry
def happend_right_tangle {a b : Wall} {hlen : a.length = b.length} : isTangle (Wall.happend a b hlen) → isTangle b → isTangle a := by
  sorry

end Tangle

-- weirdly this is named List.List.append_eq ??
theorem List.append_eq : {α : Type} → (as bs : List α) → List.append as bs = as ++ bs := List.List.append_eq

namespace Equivalence

inductive Surgery : Wall → Wall → Prop
  | top : Surgery a b → (c : Wall) → Surgery (a.append c) (b.append c)
  | bottom : Surgery a b → (c : Wall) → Surgery (c.append a) (c.append b)
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
  | zero => simp
  | succ n' h =>
      simp [vert_bricks]
      rewrite [←vert_bricks, h.left, Brick.domain, h.right, Brick.codomain]
      -- don't know how to simplify '(match true with |true => a |false => b)' to 'a'
      simp
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
  . -- domain
    induction srgy with
    | @top a b homt c h =>
      have h := (h (Tangle.append_tangle_fst ta) (Tangle.append_tangle_fst tb))
      have hlen := surgery_height_eq homt
      simp [Tangle.domain]
      cases ha : a <;> cases hb : b <;> try { rewrite [ha, hb] at hlen; simp at hlen }
      case nil.nil => simp
      case cons.cons h _ _ _ _ =>
        simp [Tangle.domain]
        simp [ha, hb, Tangle.domain] at h
        exact h
    | @bottom a b homt c h =>
      cases c with
      | nil =>
        simp [List.append] at ta
        simp [List.append] at tb
        have h := (h ta tb)
        simp [Tangle.domain]
        simp [Tangle.domain] at h
        exact h
      | cons hd tl =>
        simp [Tangle.domain]

    | @left a b homt c hlen h =>
      simp [Tangle.domain]
      have ta := Tangle.happend_left_tangle ta c.property
      have tb := Tangle.happend_left_tangle tb c.property
      have h := h ta tb
      sorry
    | @right a b homt c hlen h =>
      simp [Tangle.domain]
      have ta := Tangle.happend_right_tangle ta c.property
      have tb := Tangle.happend_right_tangle tb c.property
      have h := h ta tb
      sorry

  . -- codomain
    induction srgy with
    | @top a b homt c h =>
      cases c with
      | nil =>
        simp
        exact (h (Tangle.append_tangle_fst ta) (Tangle.append_tangle_fst tb))
      | cons =>
        simp [Tangle.codomain]
        rewrite [←List.append_eq, Tangle.last_codomain_append_nempty_snd _ _ List.noConfusion]
        rewrite [←List.append_eq, Tangle.last_codomain_append_nempty_snd _ _ List.noConfusion]
        exact Eq.refl _
    | @bottom a b homt c h =>
      induction c with
      | nil =>
        have h := (h (Tangle.append_tangle_snd ta) (Tangle.append_tangle_snd tb))
        simp [Tangle.codomain]
        simp [Tangle.codomain] at h
        exact h
      | cons hd tl h =>
        simp [Tangle.codomain]
        rewrite [List.append] at ta
        rewrite [List.append] at tb
        have h := (h (Tangle.cons_tangle_tl ta) (Tangle.cons_tangle_tl tb))

        have hlen : a.length = b.length := surgery_height_eq homt
        cases ha : a <;> cases hb : b
          -- dispatch cases where a.length ≠ b.length
          <;> try { rewrite [ha, hb] at hlen; simp at hlen }
        case nil.nil => simp
        case cons.cons h _ _ _ _ =>
          simp [Tangle.codomain] at h
          rewrite [←List.cons_append, ←List.append_eq, Tangle.last_codomain_append_nempty_snd (hd::tl) _ List.noConfusion]
          rewrite [←List.cons_append, ←List.append_eq, Tangle.last_codomain_append_nempty_snd (hd::tl) _ List.noConfusion]
          rewrite [ha, hb, ←List.append_eq, ←List.append_eq] at h
          rewrite [Tangle.last_codomain_append_nempty_snd tl _ List.noConfusion] at h
          rewrite [Tangle.last_codomain_append_nempty_snd tl _ List.noConfusion] at h
          exact h

    | @left a b homt c hlen h =>
      sorry
    | @right a b homt c hlen h =>
      sorry

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
  induction m <;> simp [isTangle]
  case slide => rewrite [verts_boundary_eq_n.left, verts_boundary_eq_n.right]; simp

theorem rmove_tangle_inv : { a b : Wall } → ReidemeisterMove a b → (isTangle a = isTangle b) := by
  intro a b m
  induction m <;> simp [isTangle]

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

