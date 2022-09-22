
-- weirdly this is named List.List.append_eq ??
theorem List.append_eq : {α : Type} → (as bs : List α) → List.append as bs = as ++ bs := List.List.append_eq

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
def Brick.vflip : Brick → Brick
  | Vert => Vert
  | Cap => Cup
  | Cup => Cap
  | Over => Over
  | Under => Under

def Brick.hflip : Brick → Brick := id

theorem Brick.vflip_boundary (b : Brick) : b.vflip.domain = b.codomain ∧ b.vflip.codomain = b.domain := by
  cases b <;> simp

def Bricks := List Brick

instance : Append Bricks := List.instAppendList
-- want this for simp in proofs, allows us to translate first to List.append
-- then List.append_eq simps to (Append List _).append a b
-- otherwise stuff like [] ++ b won't simp because the ++ is the wrong type ((Append Bricks).append)
@[simp] theorem Bricks.append_eq : {a b : Bricks} → a ++ b = List.append a b := rfl

/-- input threads -/
def Bricks.domain (bs : Bricks) : Nat := List.foldr Nat.add 0 (bs.map Brick.domain)
/-- output threads -/
def Bricks.codomain (bs : Bricks) : Nat := List.foldr Nat.add 0 (bs.map Brick.codomain)

@[simp] theorem Bricks.domain_cons : Bricks.domain (b::bs) = b.domain + Bricks.domain bs := by
  rewrite [domain, List.map, List.foldr, ←domain]
  apply Nat.add_eq
@[simp] theorem Bricks.codomain_cons : Bricks.codomain (b::bs) = b.codomain + Bricks.codomain bs := by
  rewrite [codomain, List.map, List.foldr, ←codomain]
  apply Nat.add_eq

@[simp] theorem Bricks.domain_append : {a b : Bricks} → Bricks.domain (a ++ b) = Bricks.domain a + Bricks.domain b := by
  intro a b
  induction a with
  | nil => simp [domain, List.foldr]
  | cons hd tl h => simp; rewrite [h]; exact Eq.symm (Nat.add_assoc _ _ _)
@[simp] theorem Bricks.codomain_append : {a b : Bricks} → Bricks.codomain (a ++ b) = Bricks.codomain a + Bricks.codomain b := by
  intro a b
  induction a with
  | nil => simp [codomain, List.foldr]
  | cons hd tl h => simp; rewrite [h]; exact Eq.symm (Nat.add_assoc _ _ _)

def Bricks.vflip (bs : Bricks) : Bricks := List.map Brick.vflip bs
def Bricks.hflip (bs : Bricks) : Bricks := (List.map Brick.hflip bs).reverse

def Wall : Type := List Bricks

instance : Append Wall := List.instAppendList
@[simp] theorem Wall.append_eq : {a b : Wall} → a ++ b = List.append a b := rfl

def Wall.happend : (a b : Wall) → (a.length = b.length) →  Wall
  | [], [], _ => []
  | a::as, bs, h => match bs with
      | b::bs => (a.append b)::(Wall.happend as bs (by simp [List.length] at h; exact h))
      | [] => by simp at h

def Wall.vflip (w : Wall) : Wall := (List.map Bricks.vflip w).reverse
def Wall.hflip (w : Wall) : Wall := (List.map Bricks.hflip w)


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

end Equivalence

