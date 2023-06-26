import Modallogic.Normal.Formula
import Mathlib.Data.Finset.Basic

namespace Modallogic.Normal

abbrev Context (α : Type) := Finset (Formula α)

namespace Context

def empty : Context α := ∅

private def list_allor : List (Formula α) → Formula α
  | []    => ⊥ₘ
  | φ::Γ => φ ∧ₘ list_allor Γ
noncomputable def AllOr (Γ : Context α) := list_allor Γ.toList
prefix:50 "⋁ₘ" => AllOr

private def list_alland : List (Formula α) → Formula α
  | []    => ⊤ₘ
  | φ::Γ => φ ∧ₘ list_alland Γ
noncomputable def AllAnd (Γ : Context α) := list_allor Γ.toList
prefix:50 "⋀ₘ" => AllAnd
