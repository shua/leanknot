import Basic
import Tangle

open Brick

def isLink' : Wall -> Prop
| [] => true
| bs::[] => Bricks.codomain bs = 0
| bs::bs'::w => Bricks.codomain bs = Bricks.domain bs' ∧ isLink' (bs'::w)
def isLink : Wall -> Prop
| [] => true
| bs::w => Bricks.domain bs = 0 ∧ isLink' (bs::w)

def Link := { w : Wall // isLink w }

def link_is_tangle_aux : {w : Wall} → isLink' w → isTangle w := by
  intro w
  induction w
  case nil => intro; rfl
  case cons bs w h =>
    cases w
    case nil => intro; rfl
    case cons bs' w =>
      rw [isLink']
      intro hl
      have hlr : isLink' (bs' :: w) := And.right hl
      have htr : isTangle (bs' :: w) := h hlr
      have htl : Bricks.codomain bs = Bricks.domain bs' := And.left hl
      rw [isTangle]
      apply And.intro htl htr

def link_is_tangle : {w : Wall} → isLink w → isTangle w := by
  intro w
  cases w
  case nil => intro; rfl
  case cons bs w =>
    rw [isLink]
    simp
    intro hl
    have hl' : isLink' (bs::w) := And.right hl
    apply link_is_tangle_aux hl'

namespace Link

def tangle (l : Link) : Tangle := ⟨l.val, link_is_tangle l.property⟩

def linkNumber (l : Link) : Nat := l.tangle.threadCount

end Link

-- here it is folks
def Knot := { l : Link // l.linkNumber = 1 }

