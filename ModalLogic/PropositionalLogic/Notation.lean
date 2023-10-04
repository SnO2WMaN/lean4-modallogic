import Mathlib.Data.Finset.Basic

open Finset

namespace ModalLogic.PropositionalLogic

section Symbols

variable (α : Type u)

class HasBot where bot : α
scoped[ModalLogic.PropositionalLogic] notation:70 "⊥" => HasBot.bot

class HasImply where imply : α → α → α
scoped[ModalLogic.PropositionalLogic] infixr:63 " ⇒ " => HasImply.imply

class HasNeg where neg : α → α
scoped[ModalLogic.PropositionalLogic] prefix:64 "~" => HasNeg.neg

class HasNegDef [HasNeg α] [HasBot α] [HasImply α] where 
  NegDef (φ : α) : (~φ) = (φ ⇒ ⊥)
attribute [simp] HasNegDef.NegDef

class HasTop where top : α
scoped[ModalLogic.PropositionalLogic] notation:70 "⊤" => HasTop.top

class HasDisj where disj : α → α → α
scoped[ModalLogic.PropositionalLogic] infixl:62 " ⋎ " => HasDisj.disj

class HasDisjDef [HasDisj α] [HasImply α] [HasNeg α] where 
  DisjDef (φ ψ : α) : (φ ⋎ ψ) = (~φ ⇒ ψ)

class HasConj where conj : α → α → α
scoped[ModalLogic.PropositionalLogic] infixl:62 " ⋏ " => HasConj.conj

class HasConjDef [HasConj α] [HasImply α] [HasNeg α] where 
  ConjDef (φ ψ : α) : (φ ⋏ ψ) = ~(φ ⇒ ~ψ)

class HasEquiv where equiv : α → α → α
scoped[ModalLogic.PropositionalLogic] infixl:61 " ⇔ " => HasEquiv.equiv

class HasEquivDef [HasEquiv α] [HasImply α] [HasConj α] where 
  EquivDef (φ ψ : α) : (φ ⇔ ψ) = ((φ ⇒ ψ) ⋏ (ψ ⇒ φ))
attribute [simp] HasEquivDef.EquivDef

end Symbols

structure ProveSystem (α : Type u) where
  Proves: α → Prop
notation "⊢[" S "] " φ => ProveSystem.Proves S φ
notation "⊬[" S "] " φ => ¬(⊢[S] φ)

end ModalLogic.PropositionalLogic