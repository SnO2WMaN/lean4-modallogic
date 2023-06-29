import Modallogic.Propositional.Formula

namespace Modallogic.Propositional

namespace Semantics

variable {α β : Type}

def Valuation (α : Type) := α → Prop

def Satisfy (V : Valuation α) : Formula α → Prop
| #p => V p
| ⊥ₚ => false
| φ →ₚ ψ => (Satisfy V φ) → (Satisfy V ψ)

notation "⊨ₚ[" V "]" φ => (Satisfy V φ)
notation "⊭ₚ[" V "]" φ => ¬(⊨ₚ[V] φ)

namespace Satisfy

variable (V : Valuation α) (φ ψ : Formula α)

theorem mp : (⊨ₚ[V] φ →ₚ ψ) → (⊨ₚ[V] φ) → (⊨ₚ[V] ψ) := by intro h; exact h

end Satisfy

def Valid (φ : Formula α) := ∀ V, (⊨ₚ[V] φ)

notation "⊨ₚ" φ => (Valid φ)
notation "⊭ₚ" φ => ¬(⊨ₚ φ)

namespace Valid

variable (φ ψ : Formula α)

theorem mp : (⊨ₚ φ →ₚ ψ) → (⊨ₚ φ) → (⊨ₚ ψ) := by
  intro h1 h2 V;
  exact Satisfy.mp V φ ψ (h1 V) (h2 V);

end Valid

def Consequence (Γ : Formulae α) (φ : Formula α) := ∀ V, (∀ ψ ∈ Γ, (⊨ₚ[V] ψ)) → (⊨ₚ[V] φ)

notation Γ "⊨ₚ" φ => (Consequence Γ φ)
notation Γ "⊭ₚ" φ => ¬(Γ ⊨ₚ φ)

namespace Consequence

variable (Γ : Formulae α) (φ ψ : Formula α)

theorem valid_consequence : (⊨ₚ φ) → (Γ ⊨ₚ φ) := by
  intro h1 V _;
  exact h1 V

@[simp]
theorem mp : (Γ ⊨ₚ φ →ₚ ψ) → (Γ ⊨ₚ φ) → (Γ ⊨ₚ ψ) := by
  intro h1 h2 V h3;
  sorry

end Consequence

end Semantics

variable (φ ψ χ : Formula α)

end Modallogic.Propositional
