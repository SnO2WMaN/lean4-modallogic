import ModalLogic.PropositionalLogic.DeductionSystem.Notations
import ModalLogic.PropositionalLogic.DeductionSystem.Minimal0
import ModalLogic.PropositionalLogic.DeductionSystem.Minimal

open ModalLogic.PropositionalLogic
open Axioms 
open DeductionSystem

namespace ModalLogic.PropositionalLogic.DeductionSystem

variable [DecidableEq α] [HasImply α] [HasDisj α] [HasConj α] [HasBot α]
variable {D : DeductionSystem α} [IsIntuitional D]

lemma EFQ (φ) : Γ ⊢ᵈ[D] (Axioms.EFQ φ) := by aesop;

end ModalLogic.PropositionalLogic.DeductionSystem