import Lean
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Encodable.Basic

open Option Nat Encodable

namespace Modallogic

namespace Propositional

inductive Formula (α : Type) : Type
| bot : Formula α
| var : α → Formula α
| impl : Formula α → Formula α → Formula α

namespace Formula

prefix:max "#" => var
notation "⊥ₚ" => bot
infixr:30 " →ₚ " => impl

section

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

end

def toStr [ToString α] : Formula α → String
| φ →ₚ ψ => s!"({toStr φ} → {toStr ψ})"
| ⊥ₚ => "⊥"
| #p => s!"#{p}"

instance [ToString α] : Repr (Formula α) := ⟨λ t _ => toStr t⟩
instance [ToString α] : ToString (Formula α) := ⟨toStr⟩

def beq [BEq α] (φ ψ : Formula α) : Bool :=
  match φ, ψ with
  | .var p₁, .var p₂ => p₁ == p₂
  | ⊥ₚ, ⊥ₚ => true
  | φ₁ →ₚ ψ₁, φ₂ →ₚ ψ₂ => (beq φ₁ φ₂) ∧ (beq ψ₁ ψ₂)
  | _, _ => false
instance [BEq α] : BEq (Formula α) := ⟨Formula.beq⟩

section

variable [Encodable α]

def toNat : Formula α → ℕ
  | ⊥ₚ => 0
  | #p => 2 * (encode p) + 1
  | φ →ₚ ψ => 2 * (pair (φ.toNat) (ψ.toNat)) + 2

def ofNat : ℕ → Option (Formula α)
  | 0 => some ⊥ₚ
  | n + 1 =>
    match n.bodd with
    | false => (decode n.div2).map Formula.var
    | true =>
      let m := n.div2
      have h : m < n + 1 := by
        apply lt_succ_iff.mpr; simp [div2_val]; exact div_le_self n 2;
      have : (unpair m).1 < n + 1 := lt_of_le_of_lt (unpair_left_le _) h;
      have : (unpair m).2 < n + 1 := lt_of_le_of_lt (unpair_right_le _) h;
      let φ := ofNat m.unpair.1
      let ψ := ofNat m.unpair.2
      φ.bind (λ φ => ψ.map (λ ψ => φ →ₚ ψ))
  termination_by ofNat n => n

theorem ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | ⊥ₚ => by simp [toNat, ofNat];
  | #p => by simp [toNat, ofNat, div2_val];
  | φ →ₚ ψ => by simp [toNat, ofNat, div2_val, ofNat_toNat];

instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

end

end Formula

abbrev Formulae (α : Type) := Set (Formula α)

end Modallogic.Propositional

