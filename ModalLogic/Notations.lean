namespace ModalLogic


section Symbols

variable (α : Type u)

class HasBot where bot : α
notation:70 "⊥" => HasBot.bot

class HasTop where top : α
notation:70 "⊤" => HasTop.top

class HasDisj where disj : α → α → α
infixl:63 " ⋎ " => HasDisj.disj

class HasConj where conj : α → α → α
infixl:63 " ⋏ " => HasConj.conj

class HasNeg where neg : α → α
prefix:64 "~" => HasNeg.neg

class HasImply where imply : α → α → α
infixr:62 " ⇒ " => HasImply.imply

class HasEquiv where equiv : α → α → α
infixl:61 " ⇔ " => HasEquiv.equiv

class HasBox where box : α → α
prefix:65 "□" => HasBox.box

class HasDia where dia : α → α
prefix:65 "◇" => HasDia.dia

end Symbols


section DefinedBy
 
variable (α : Type u)
variable [HasBot α] [HasTop α] [HasNeg α] [HasImply α] [HasDisj α] [HasConj α] [HasEquiv α]

class DefinedNeg where defNeg (φ : α) : (~φ) = (φ ⇒ ⊥)
attribute [simp] DefinedNeg.defNeg

class DefinedTop where defTop : (⊤ : α) = ~(⊥ : α) 
attribute [simp] DefinedTop.defTop

class DefinedDisj where defDisj (φ ψ : α) : (φ ⋎ ψ) = (~φ ⇒ ψ)
attribute [simp] DefinedDisj.defDisj

class DefinedConj where defConj (φ ψ : α) : (φ ⋏ ψ) = ~(φ ⇒ ~ψ)
attribute [simp] DefinedConj.defConj

class DefinedEquiv where defEquiv (φ ψ : α) : (φ ⇔ ψ) = ((φ ⇒ ψ) ⋏ (ψ ⇒ φ))
attribute [simp] DefinedEquiv.defEquiv

variable [HasBox α] [HasDia α]

class DefinedDia where defDia (φ : α) : (◇φ) = ~(□(~φ))
attribute [simp] DefinedDia.defDia

end DefinedBy


end ModalLogic