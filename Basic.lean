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


def Bricks : Type := List Brick

/-- input threads -/
def Bricks.domain (bs : Bricks) : Nat := List.foldr Nat.add 0 (bs.map Brick.domain)
/-- output threads -/
def Bricks.codomain (bs : Bricks) : Nat := List.foldr Nat.add 0 (bs.map Brick.codomain)

def Bricks.count (bs : Bricks) (b : Brick) : Nat := List.length (List.filter (· == b) bs)

@[simp] theorem Bricks.domain_head_plus_domain_tail_eq_domain : Bricks.domain (b::bs) = b.domain + Bricks.domain bs := by
  rewrite [domain, List.map, List.foldr, ←domain]
  apply Nat.add_eq
@[simp] theorem Bricks.codomain_head_plus_codomain_tail_eq_codomain : Bricks.codomain (b::bs) = b.codomain + Bricks.codomain bs := by
  rewrite [codomain, List.map, List.foldr, ←codomain]
  apply Nat.add_eq


def Wall : Type := List Bricks

def Wall.count (w : Wall) (b : Brick) : Nat := List.foldr Nat.add 0 (List.map (fun bs => Bricks.count bs b) w)

def Wall.cupNumber (w : Wall) : Nat := w.count Cup
def Wall.capNumber (w : Wall) : Nat := w.count Cap

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

inductive Homotopic : Wall → Wall → Prop
  | planar : PlanarIsotopic a b → Homotopic a b
  | rmove : ReidemeisterMove a b → Homotopic a b
  -- surgery
  | top : Homotopic a b → (c : Wall) → Homotopic (a.append c) (b.append c)
  | bottom : Homotopic a b → (c : Wall) → Homotopic (c.append a) (c.append b)
  | right : Homotopic a b → (c : Wall) → (h : a.length = c.length ∧ b.length = c.length) → Homotopic (a.happend c h.left) (b.happend c h.right)
  | left : Homotopic a b → (c : Wall) → (h : c.length = a.length ∧ c.length = b.length) → Homotopic (c.happend a h.left) (c.happend b h.right)
  -- equiv
  | id : Homotopic a a
  | symm : Homotopic a b → Homotopic b a
  | trans : Homotopic a b → Homotopic b c → Homotopic a c

end Equivalence

