import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import ModalLogic.PropositionalLogic.Notation

open Finset
open ModalLogic.PropositionalLogic

namespace ModalLogic.Normal

variable (α : Type u)

class HasBox where box : α → α
scoped[ModalLogic.Normal] prefix:66 "□" => HasBox.box

class HasDia where dia : α → α
scoped[ModalLogic.Normal] prefix:66 "◇" => HasDia.dia

section DefinedByOtherSymbols

variable (α : Type u)

class HasDiaDef [HasNeg α] [HasBox α] [HasDia α] where 
  DiaDef (φ : α) : (◇φ) = (~□(~φ))

end DefinedByOtherSymbols

abbrev Context (α) [DecidableEq α] := Finset α

variable {α} [DecidableEq α] [HasBox α] [HasDia α]

def Context.box (Γ : Context α) : Context α := Γ.image (λ φ => □φ)
prefix:60 "□" => Context.box

def Context.dia (Γ : Context α) : Context α := Γ.image (λ φ => ◇φ)
prefix:60 "◇" => Context.dia



end ModalLogic.Normal