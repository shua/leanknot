import Basic
import Tangle

def isBraid (t : Tangle) : Prop := t.val.cupNumber = 0 ∧ t.val.capNumber = 0
def Braid := { t : Tangle // isBraid t }

namespace Braid

-- TODO
def permute (b : Braid ) { ID : Type } (ids : List ID) (hdom : b.val.domain = ids.length) : List ID :=
  sorry

end Braid

