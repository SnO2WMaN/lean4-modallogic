import Mathlib.Data.Finset.Image
import ModalLogic.SupplymentSimp
import ModalLogic.PropositionalLogic.DeductionSystem
import ModalLogic.Normal.Notations

open ModalLogic.PropositionalLogic

namespace ModalLogic.Normal

variable (α : Type u) [DecidableEq α]

abbrev Context (α) := Finset α

variable [HasBox α] in
def Context.box (Γ : Context α) : Context α := Γ.image (λ φ => □φ)
prefix:60 "□" => Context.box

end ModalLogic.Normal