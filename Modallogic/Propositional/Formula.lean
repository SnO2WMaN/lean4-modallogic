import Lean
import Mathlib.Data.Set.Basic

namespace Modallogic

namespace Propositional

inductive Formula (α : Type) : Type
| var : α → Formula α
| bot : Formula α
| impl : Formula α → Formula α → Formula α

namespace Formula

prefix:max "#" => var
notation "⊥ₚ" => bot
infixr:30 " →ₚ " => impl

variable (φ ψ χ : Formula α)
def not := φ →ₚ ⊥ₚ
prefix:70 "¬ₚ" => not

def top : Formula α := ¬ₚ⊥ₚ
notation "⊤ₚ" => top

def or := (¬ₚφ) →ₚ ψ
infixl:40 " ∨ₚ " => or

def and := ¬ₚ(¬ₚφ ∨ₚ ¬ₚψ)
infixl:50 " ∧ₚ " => and

def iff := (φ →ₚ ψ) ∧ₚ (ψ →ₚ φ)
infixl:30 " ↔ₚ " => iff

def toString [ToString α] : Formula α → String
| φ →ₚ ψ => s!"({toString φ} → {toString ψ})"
| ⊥ₚ => "⊥"
| #p => s!"#{p}"

instance [ToString α] : Repr (Formula α) := ⟨λ t _ => Formula.toString t⟩

instance [ToString α] : ToString (Formula α) := ⟨Formula.toString⟩

#eval (#1 →ₚ #2 ∧ₚ #1)

def beq [BEq α] (φ ψ : Formula α) : Bool :=
  match φ, ψ with
  | .var p₁, .var p₂ => p₁ == p₂
  | ⊥ₚ, ⊥ₚ => true
  | φ₁ →ₚ ψ₁, φ₂ →ₚ ψ₂ => (beq φ₁ φ₂) ∧ (beq ψ₁ ψ₂)
  | _, _ => false
instance [BEq α] : BEq (Formula α) := ⟨Formula.beq⟩

#eval (#1 →ₚ #2 →ₚ #1) == (#1 →ₚ (#2 →ₚ #1))

end Formula

abbrev Formulae (α : Type) := Set (Formula α)

def inconsistent (Γ : Formulae α) :=  ∃ φ, (φ ∈ Γ ∧ ¬ₚφ ∈ Γ)
def consistent (Γ : Formulae α) := ¬(inconsistent Γ)

end Modallogic.Propositional

