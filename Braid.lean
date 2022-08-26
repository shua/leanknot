import Basic
import Tangle

def isBraid : Wall → Prop
| [] => true
| bs::w => !bs.elem Brick.Cap ∧ !bs.elem Brick.Cup ∧
  match w with
  | [] => true
  | bs'::w => bs.codomain = bs'.domain ∧ isBraid (bs'::w)
def Braid := { w : Wall // isBraid w }

namespace Braid

theorem is_tangle : isBraid w → isTangle w := by
  intro hb
  induction w with
  | nil => simp [isTangle]
  | cons bs w hi =>
      cases w with
      | nil => simp [isTangle]
      | cons bs' w =>
          rewrite [isBraid] at hb
          rewrite [isTangle]
          exact And.intro hb.right.right.left (hi hb.right.right.right)

def tangle (b : Braid) : Tangle := ⟨b.val, is_tangle b.property⟩

-- TODO
def permute (b : Braid ) (as : List α) (hdom : b.tangle.domain = as.length) : List α :=
  sorry

end Braid

