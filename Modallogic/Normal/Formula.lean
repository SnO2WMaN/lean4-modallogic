namespace Modallogic.Normal

inductive Formula (α : Type) : Type
| var : α → Formula α
| bot : Formula α
| impl : Formula α → Formula α → Formula α
| box : Formula α → Formula α

namespace Formula

prefix:max "#" => var
notation "⊥ₘ" => bot
infixr:30 "→ₘ" => impl
prefix:60 "□" => box

variable (φ ψ χ : Formula α)
def not := φ →ₘ ⊥ₘ
prefix:70 "¬ₘ" => not

def top : Formula α := ¬ₘ⊥ₘ
notation "⊤ₘ" => top

def or := (¬ₘφ) →ₘ ψ
infixl:40 "∨ₘ" => or

def and := ¬ₘ(¬ₘφ ∨ₘ ¬ₘψ)
infixl:50 "∧ₘ" => and

def iff := (φ →ₘ ψ) ∧ₘ (ψ →ₘ φ)
infixl:30 "↔ₘ" => iff

def dia := ¬ₘ(□(¬ₘ(φ)))
prefix:60 "◇" => dia

def toString [ToString α] : Formula α → String
| #p => s!"{p}"
| ⊥ₘ => "⊥"
| φ →ₘ ψ => s!"({toString φ} → {toString ψ})"
| □φ => s!"□{toString φ}"

instance [ToString α] : Repr (Formula α) := ⟨λ t _ => Formula.toString t⟩

instance [ToString α] : ToString (Formula α) := ⟨Formula.toString⟩

#eval (#1 →ₘ #2 ∧ₘ #1)

def beq [BEq α] (φ ψ : Formula α) : Bool :=
  match φ, ψ with
  | .var p₁, .var p₂ => p₁ == p₂
  | ⊥ₘ, ⊥ₘ => true
  | φ₁ →ₘ ψ₁, φ₂ →ₘ ψ₂ => (beq φ₁ φ₂) ∧ (beq ψ₁ ψ₂)
  | □φ₁, □φ₂ => beq φ₁ φ₂
  | _, _ => false
instance [BEq α] : BEq (Formula α) := ⟨Formula.beq⟩

#eval (#1 →ₘ #2 →ₘ #1.2) == (#1 →ₘ (#2 →ₘ #1))

end Formula
