inductive Brick : Type
  | Vert : Brick
  | Cap : Brick
  | Cup : Brick
  | Over : Brick
  | Under : Brick
  deriving BEq, DecidableEq
open Brick

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


namespace PlanarIsotopy
def vert_bricks : Nat → Bricks
  | Nat.zero => []
  | Nat.succ n' => Brick.Vert :: (vert_bricks n')

theorem verts_dom_eq_codom (n : Nat) : (vert_bricks n).domain = (vert_bricks n).codomain := by
  induction n <;> rewrite [vert_bricks, Bricks.domain, Bricks.codomain, List.map, List.foldr, List.map, List.foldr]
  case zero => apply Eq.refl
  case succ n h =>
    rewrite [←Bricks.domain, ←Bricks.codomain, h]
    simp [Brick.domain, Brick.codomain]

/--
Planar isotopic mappings

     vertcl    vertcc    crosscl       crosscc
     |  .". |  |  | .".  | |  .". | |  | |  | | .".
     |  | '.'  |  '.' |  '/.  | .\' |  '/.  | .\' |
                         | |  | | '.'  | |  '.' | |
-/
inductive Map : Wall → Wall → Type
  | vertcl : Map [[Vert],[Vert]] [[Cap,Vert],[Vert,Cup]]
  | vertcc : Map [[Vert],[Vert]] [[Vert,Cap],[Cup,Vert]]
  | crosscl : Map [[Vert,Vert],[Under],[Vert,Vert]] [[Cap,Vert,Vert],[Vert,Over,Vert],[Vert,Vert,Cup]]
  | crosscc : Map [[Vert,Vert],[Under],[Vert,Vert]] [[Vert,Vert,Cap],[Vert,Over,Vert],[Cup,Vert,Vert]]
  | stretch : ∀ a b, Map [a,b] [a, vert_bricks (Bricks.codomain a), b]
  | inv : ∀ a b, Map b a → Map a b
  | compose : ∀ a b c, Map a b → Map b c → Map a c

end PlanarIsotopy


namespace Reidemeister

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
inductive Move : Wall → Wall → Type
  | type1a : Move [[Cap], [Vert, Vert]]  [[Cap], [Over]]
  | type1b : Move [[Cap], [Vert, Vert]]  [[Cap], [Under]]
  | type1c : Move [[Vert, Vert], [Cup]]  [[Over], [Cup]]
  | type1d : Move [[Vert, Vert], [Cup]]  [[Under], [Cup]]
  | type2a : Move [[Vert, Vert], [Vert, Vert]]  [[Over], [Under]]
  | type2b : Move [[Vert, Vert], [Vert, Vert]]  [[Under], [Over]]
  | type3a : Move [[Over, Vert], [Vert, Over], [Under, Vert]]
                  [[Vert, Under], [Over, Vert], [Vert, Over]]
  | type3b : Move [[Under, Vert], [Vert, Under], [Under, Vert]]
                  [[Vert, Under], [Under, Vert], [Vert, Under]]
  | type3c : Move [[Over, Vert], [Vert, Over], [Over, Vert]]
                  [[Vert, Over], [Over, Vert], [Vert, Over]]
  | type3d : Move [[Under, Vert], [Vert, Under], [Over, Vert]]
                  [[Vert, Over], [Under, Vert], [Vert, Under]]
  | rev : ∀ a b, Move b a → Move a b
  | compose : ∀ a b c, Move a b → Move b c → Move a c

end Reidemeister
