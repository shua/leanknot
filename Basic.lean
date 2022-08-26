inductive Brick : Type
  | Vert : Brick
  | Cap : Brick
  | Cup : Brick
  | Over : Brick
  | Under : Brick
  deriving BEq, DecidableEq
open Brick

-- stolen from Bool LawfulBEq impl
instance instLawfulEqBrick : LawfulBEq Brick where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
  rfl {a} := by cases a <;> decide

/-- input threads -/
def Brick.domain : Brick → Nat
  | Vert => 1
  | Cap => 0
  | Cup => 2
  | Over => 2
  | Under => 2

/-- output threads -/
def Brick.codomain : Brick → Nat
  | Vert => 1
  | Cap => 2
  | Cup => 0
  | Over => 2
  | Under => 2

/-- 180° rotation -/
def Brick.rotate : Brick → Brick
  | Vert => Vert
  | Cap => Cup
  | Cup => Cap
  | Over => Over
  | Under => Under

theorem Brick.rotate_flips_domain (b : Brick) : b.rotate.domain = b.codomain ∧ b.rotate.codomain = b.domain := by
  cases b <;> simp


def Bricks : Type := List Brick

/-- input threads -/
def Bricks.domain (bs : Bricks) : Nat := List.foldr Nat.add 0 (bs.map Brick.domain)
/-- output threads -/
def Bricks.codomain (bs : Bricks) : Nat := List.foldr Nat.add 0 (bs.map Brick.codomain)

@[simp] theorem Bricks.domain_head_plus_domain_tail_eq_domain : Bricks.domain (b::bs) = b.domain + Bricks.domain bs := by
  rewrite [domain, List.map, List.foldr, ←domain]
  apply Nat.add_eq
@[simp] theorem Bricks.codomain_head_plus_codomain_tail_eq_codomain : Bricks.codomain (b::bs) = b.codomain + Bricks.codomain bs := by
  rewrite [codomain, List.map, List.foldr, ←codomain]
  apply Nat.add_eq

def Bricks.rotate (bs : Bricks) : Bricks := (List.map Brick.rotate bs).reverse

theorem Bricks.domain_eq_reverse_domain (bs : Bricks) : Bricks.domain bs.reverse = bs.domain ∧ Bricks.codomain bs.reverse = bs.codomain := by
  induction bs with
  | nil => simp
  | cons b bs h =>
      sorry
theorem Bricks.rotate_flips_domain (bs : Bricks) : bs.rotate.domain = bs.codomain ∧ bs.rotate.codomain = bs.domain := by
  induction bs with
  | nil => simp
  | cons b bs h =>
    rewrite [rotate, List.map]
    have bsrot := Bricks.domain_eq_reverse_domain (b.rotate :: (bs.map Brick.rotate))
    rewrite [bsrot.left, bsrot.right]
    simp
    have bflip := Brick.rotate_flips_domain b
    rewrite [bflip.left, bflip.right]
    have bsrot := Bricks.domain_eq_reverse_domain (bs.map Brick.rotate)
    rewrite [←bsrot.left, ←bsrot.right, ←Bricks.rotate, h.left, h.right]
    simp


def Wall : Type := List Bricks

def Wall.sliceBegin : Wall → Nat → Wall
  | [], _ => []
  | bs::w, 0 => bs::w
  | _bs::w, i+1 => Wall.sliceBegin w i
def Wall.sliceEnd : Wall → Nat → Wall
  | [], _ => []
  | bs::w, i => if w.length > i then bs::(Wall.sliceEnd w i) else []
def Wall.slice (w : Wall) (i j : Nat) : Wall := Wall.sliceBegin (Wall.sliceEnd w j) i

def Wall.happend : (a b : Wall) → (a.length = b.length) →  Wall
  | [], [], _ => []
  | a::as, bs, h => match bs with
      | b::bs => (a.append b)::(Wall.happend as bs (by simp [List.length] at h; exact h))
      | [] => by simp at h

def Wall.rotate (w : Wall) : Wall := (List.map Bricks.rotate w).reverse


namespace Equivalence
def vert_bricks (n : Nat) : Bricks := List.replicate n Vert

theorem verts_dom_eq_codom (n : Nat) : (vert_bricks n).domain = (vert_bricks n).codomain := by
  induction n with
  | zero => simp
  | succ _ h =>
    simp [vert_bricks, List.replicate, Brick.domain, Brick.codomain]
    rewrite [←vert_bricks, h]
    rfl

/--
Planar isotopic mappings

     vertcl    vertcc    crosscl       crosscc
     |  .". |  |  | .".  | |  .". | |  | |  | | .".
     |  | '.'  |  '.' |  '/.  | .\' |  '/.  | .\' |
                         | |  | | '.'  | |  '.' | |

     slide
     . . .    . . .
     #######  | | |
     | | | |  #######
     ' ' ' '  ' ' ' '
-/
inductive PlanarIsotopic : Wall → Wall → Prop
  | vertcl : PlanarIsotopic [[Vert],[Vert]] [[Cap,Vert],[Vert,Cup]]
  | vertcc : PlanarIsotopic [[Vert],[Vert]] [[Vert,Cap],[Cup,Vert]]
  | crosscl : PlanarIsotopic [[Vert,Vert],[Under],[Vert,Vert]] [[Cap,Vert,Vert],[Vert,Over,Vert],[Vert,Vert,Cup]]
  | crosscc : PlanarIsotopic [[Vert,Vert],[Under],[Vert,Vert]] [[Vert,Vert,Cap],[Vert,Over,Vert],[Cup,Vert,Vert]]
  | slide : PlanarIsotopic [a, vert_bricks (Bricks.codomain a)] [vert_bricks (Bricks.domain a), a]
  -- equiv relation
  | id : PlanarIsotopic a a
  | symm : PlanarIsotopic b a → PlanarIsotopic a b
  | trans : PlanarIsotopic a b → PlanarIsotopic b c → PlanarIsotopic a c

-- TODO: should this just be free functions? Should this really be a Prop or equivalence relation?
/--
Reidemeister moves

    1a .".  .".  2a | |  .\'  3a .\' |  | '/.
       | |  .\'     | |  '/.     | .\'  .\' |
                                 '/. |  | .\'
    1b .".  .".  2b | |  '/.
       | |  '/.     | |  .\'  3b '/. |  | '/.
                                 | '/.  '/. |
    1c | |  .\'                  '/. |  | '/.
       '.'  '.'
                              3c .\' |  | '/.
    1d | |  '/.                  | .\'  .\' |
       '.'  '.'                  '/. |  | .\'

                              3d '/. |  | .\'
                                 | '/.  '/. |
                                 .\' |  | '/.
-/
inductive ReidemeisterMove : Wall → Wall → Prop
  | type1a : ReidemeisterMove [[Cap], [Vert, Vert]]  [[Cap], [Over]]
  | type1b : ReidemeisterMove [[Cap], [Vert, Vert]]  [[Cap], [Under]]
  | type1c : ReidemeisterMove [[Vert, Vert], [Cup]]  [[Over], [Cup]]
  | type1d : ReidemeisterMove [[Vert, Vert], [Cup]]  [[Under], [Cup]]
  | type2a : ReidemeisterMove [[Vert, Vert], [Vert, Vert]]  [[Over], [Under]]
  | type2b : ReidemeisterMove [[Vert, Vert], [Vert, Vert]]  [[Under], [Over]]
  | type3a : ReidemeisterMove [[Over, Vert], [Vert, Over], [Under, Vert]]
                  [[Vert, Under], [Over, Vert], [Vert, Over]]
  | type3b : ReidemeisterMove [[Under, Vert], [Vert, Under], [Under, Vert]]
                  [[Vert, Under], [Under, Vert], [Vert, Under]]
  | type3c : ReidemeisterMove [[Over, Vert], [Vert, Over], [Over, Vert]]
                  [[Vert, Over], [Over, Vert], [Vert, Over]]
  | type3d : ReidemeisterMove [[Under, Vert], [Vert, Under], [Over, Vert]]
                  [[Vert, Over], [Under, Vert], [Vert, Under]]
  -- equiv
  | id : ReidemeisterMove a a
  | symm : ReidemeisterMove a b → ReidemeisterMove b a
  | trans : ReidemeisterMove a b → ReidemeisterMove b c → ReidemeisterMove a c

inductive LocalHomotopic : Wall → Wall → Prop
  | planar : PlanarIsotopic a b → LocalHomotopic a b
  | rmove : ReidemeisterMove a b → LocalHomotopic a b
  -- surgery
  | top : LocalHomotopic a b → (c : Wall) → LocalHomotopic (a.append c) (b.append c)
  | bottom : LocalHomotopic a b → (c : Wall) → LocalHomotopic (c.append a) (c.append b)
  | right : LocalHomotopic a b → (c : Wall) → (h : a.length = c.length ∧ b.length = c.length) → LocalHomotopic (a.happend c h.left) (b.happend c h.right)
  | left : LocalHomotopic a b → (c : Wall) → (h : c.length = a.length ∧ c.length = b.length) → LocalHomotopic (c.happend a h.left) (c.happend b h.right)
  -- equiv
  | id : LocalHomotopic a a
  | symm : LocalHomotopic a b → LocalHomotopic b a
  | trans : LocalHomotopic a b → LocalHomotopic b c → LocalHomotopic a c

inductive Homotopic : Wall → Wall → Prop
  | surgery : LocalHomotopic a b → Homotopic a b
  | rotate : Homotopic a a.rotate
  -- equiv
  | id : LocalHomotopic a a
  | symm : LocalHomotopic a b → LocalHomotopic b a
  | trans : LocalHomotopic a b → LocalHomotopic b c → LocalHomotopic a c

end Equivalence

