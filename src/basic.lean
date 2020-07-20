inductive brick : Type
| Vert : brick
| Cap : brick
| Cup : brick
| Over : brick
| Undr : brick
open brick

def brick.domain : brick → ℕ
| Vert := 1
| Cap := 0
| Cup := 2
| Over := 2
| Undr := 2

def brick.codomain : brick → ℕ
| Vert := 1
| Cap := 2
| Cup := 0
| Over := 2
| Undr := 2

@[simp] def bricks.domain (bs : list brick) : ℕ := list.foldr nat.add 0 (bs.map brick.domain)
@[simp] def bricks.codomain (bs : list brick) : ℕ := list.foldr nat.add 0 (bs.map brick.codomain)

def wall : Type := list (list brick)

namespace planar_isotopy

def vert_bricks : ℕ → list brick
| nat.zero := []
| (nat.succ n) := Vert::(vert_bricks n)

inductive map : wall → wall → Type
| vertcl : map [[Vert],[Vert]] [[Cap,Vert],[Vert,Cup]]
| vertcc : map [[Vert],[Vert]] [[Vert,Cap],[Cup,Vert]]
| crosscl : map [[Vert,Vert],[Undr],[Vert,Vert]] [[Cap,Vert,Vert],[Vert,Over,Vert],[Vert,Vert,Cup]]
| crosscc : map [[Vert,Vert],[Undr],[Vert,Vert]] [[Vert,Vert,Cap],[Vert,Over,Vert],[Cup,Vert,Vert]]
| stretch : Π a b, map [a,b] [a, vert_bricks (bricks.codomain a), b]
| id : Π a, map a a
| inv : Π a b, map b a → map a b
| compose : Π a b c, map a b → map b c → map a c

@[refl] def map_refl (a : wall) : map a a := map.id a
@[symm] def map_symm (a b : wall) : map a b → map b a := map.inv b a
@[trans] def map_trans (a b c : wall) : map a b → map b c → map a c := map.compose a b c

end planar_isotopy

namespace reidemeister
inductive move : wall → wall → Type
| type1a : move [[Cap], [Vert, Vert]]  [[Cap], [Over]]
| type1b : move [[Cap], [Vert, Vert]]  [[Cap], [Undr]]
| type1c : move [[Vert, Vert], [Cup]]  [[Over], [Cup]]
| type1d : move [[Vert, Vert], [Cup]]  [[Undr], [Cup]]
| type2a : move [[Vert, Vert], [Vert, Vert]]  [[Over], [Undr]]
| type2b : move [[Vert, Vert], [Vert, Vert]]  [[Undr], [Over]]
| type3a : move [[Over, Vert], [Vert, Over], [Undr, Vert]]
                [[Vert, Undr], [Over, Vert], [Vert, Over]]
| type3b : move [[Undr, Vert], [Vert, Undr], [Undr, Vert]]
                [[Vert, Undr], [Undr, Vert], [Vert, Undr]]
| type3c : move [[Over, Vert], [Vert, Over], [Over, Vert]]
                [[Vert, Over], [Over, Vert], [Vert, Over]]
| type3d : move [[Undr, Vert], [Vert, Undr], [Over, Vert]]
                [[Vert, Over], [Undr, Vert], [Vert, Undr]]
| rev : Π a b, move b a → move a b
| compose : Π a b c, move a b → move b c → move a c

@[symm] def move_symm (a b : wall) : move a b → move b a := move.rev b a
@[trans] def move_trans (a b c: wall) : move a b → move b c → move a c := move.compose a b c

end reidemeister
