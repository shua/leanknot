import Basic
import Tangle
import Graph

open Brick

def isLink' : Wall -> Prop
| [] => true
| bs::[] => Bricks.codomain bs = 0
| bs::bs'::w => Bricks.codomain bs = Bricks.domain bs' ∧ isLink' (bs'::w)
def isLink : Wall -> Prop
| [] => true
| bs::w => Bricks.domain bs = 0 ∧ isLink' (bs::w)

def Link := { w : Wall // isLink w }

namespace Link

theorem is_tangle_aux {w : Wall} : isLink' w → isTangle w := by
  induction w with
  | nil => intro; rfl
  | cons bs w h =>
    cases w with
    | nil => intro; rfl
    | cons bs' w =>
      rewrite [isLink', isTangle]
      intro hl
      exact And.intro hl.left (h hl.right)

theorem is_tangle {w : Wall} : isLink w → isTangle w := by
  cases w with
  | nil => intro; rfl
  | cons bs w =>
    rewrite [isLink]
    -- again don't know how to go from (match true | true => a) to just a
    simp
    intro hl
    exact is_tangle_aux hl.right


def tangle (l : Link) : Tangle := ⟨l.val, is_tangle l.property⟩

def link_number (l : Link) : Nat := l.tangle.thread_count

end Link

-- here it is folks
def Knot := { l : Link // l.link_number = 1 }

