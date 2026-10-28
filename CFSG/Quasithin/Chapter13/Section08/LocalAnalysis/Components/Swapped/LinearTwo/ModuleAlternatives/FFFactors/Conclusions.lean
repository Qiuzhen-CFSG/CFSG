module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.OrbitActor

/-!
# Concrete factor-module conclusions and their transport

The model predicate records actual group and intertwining linear equivalences.
The natural action retains the field degree. The orthogonal action is the
four-dimensional even-weight permutation core for A₅, and retains n = 2.
This defines the desired output; it does not assert its classification.

A factor-marked product supplies the sum of the canonical commutator spaces
even when the ambient group exchanges the factors. A complement then gives
the literal addition equivalence, whose intertwining formula is proved from
cross-factor fixation. These transports preserve directness and the original
component actions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and proof of 13.8.16(1), p.952 (PDF p.969).
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

section Models
variable {D E F U V W : Type*} [Group D] [Group E] [Group F]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D U} {σ : Representation (ZMod 2) E V}
  {τ : Representation (ZMod 2) F W}

def composeActionEquiv (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) : ActionEquiv ρ τ where
  groupEquiv := e.groupEquiv.trans f.groupEquiv
  linearEquiv := e.linearEquiv.trans f.linearEquiv
  intertwines g u := by
    change f.linearEquiv (e.linearEquiv (ρ g u)) = _
    rw [e.intertwines, f.intertwines]
    rfl

inductive FactorModule (ρ : Representation (ZMod 2) D U) (n : ℕ) : Prop
  | natural (F : BinaryField) (degree : F.degree = n)
      (equiv : ActionEquiv ρ (linearNatural F 2))
  | orthogonal (degree : n = 2)
      (equiv : ActionEquiv ρ ((BinaryPermutation.coreRepresentation (Fin 5)).comp
        (alternatingGroup (Fin 5)).subtype))

theorem FactorModule.transport {n : ℕ} (e : ActionEquiv ρ σ) (h : FactorModule σ n) :
    FactorModule ρ n := by
  cases h with
  | natural F hn f => exact .natural F hn (composeActionEquiv e f)
  | orthogonal hn f => exact .orthogonal hn (composeActionEquiv e f)

end Models

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

theorem factor_spaces_sum_of_product (A B N : Subgroup D)
    (e : A × B ≃* N) (he : ∀ a b, (e (a, b) : D) = (a : D) * b)
    (hfull : subspaceCommutator ρ ⊤ N = ⊤) :
    subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B = ⊤ := by
  apply top_unique
  conv_lhs => rw [← hfull]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, _, rfl⟩
  obtain ⟨⟨a, b⟩, hab⟩ := e.surjective ⟨g, hg⟩
  have hg' : g = (a : D) * b := (congrArg Subtype.val hab).symm.trans (he a b)
  rw [hg', map_mul]
  have ha : ρ a (ρ b v) - ρ b v ∈ subspaceCommutator ρ ⊤ A :=
    Submodule.subset_span ⟨a, a.property, ρ b v, Submodule.mem_top, rfl⟩
  have hb : ρ b v - v ∈ subspaceCommutator ρ ⊤ B :=
    Submodule.subset_span ⟨b, b.property, v, Submodule.mem_top, rfl⟩
  change ρ a (ρ b v) - v ∈ subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B
  exact Submodule.mem_sup.mpr ⟨_, ha, _, hb, sub_add_sub_cancel _ _ _⟩

def factorSumEquiv (A B : Subgroup D)
    (h : IsCompl (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B)) :
    ((subspaceCommutator ρ ⊤ A) × (subspaceCommutator ρ ⊤ B)) ≃ₗ[ZMod 2] V :=
  Submodule.prodEquivOfIsCompl _ _ h

@[simp] theorem factorSumEquiv_apply (A B : Subgroup D)
    (h : IsCompl (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B))
    (u : subspaceCommutator ρ ⊤ A) (v : subspaceCommutator ρ ⊤ B) :
    factorSumEquiv ρ A B h (u, v) = (u : V) + v := rfl

theorem factorSumEquiv_intertwines (A B N : Subgroup D)
    (e : A × B ≃* N) (he : ∀ a b, (e (a, b) : D) = (a : D) * b)
    (h : IsCompl (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B))
    (hcross₁ : subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A)
    (hcross₂ : subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B)
    (a : A) (b : B) (u : subspaceCommutator ρ ⊤ A) (v : subspaceCommutator ρ ⊤ B) :
    factorSumEquiv ρ A B h (factorRepresentation ρ A a u, factorRepresentation ρ B b v) =
      ρ (e (a, b)) (factorSumEquiv ρ A B h (u, v)) := by
  simp only [factorSumEquiv_apply, factorRepresentation_apply, he, map_mul,
    Module.End.mul_apply, map_add]
  have hbu : ρ b (u : V) = u := hcross₂ u.property b
  rw [hbu]
  exact congrArg (fun w => ρ a u + w)
    (hcross₁ (factorRepresentation ρ B b v).property a).symm

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
