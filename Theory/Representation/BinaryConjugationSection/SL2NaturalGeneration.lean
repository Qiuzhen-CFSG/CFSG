module
public import Theory.Representation.BinaryConjugationSection.Generation
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# Generation modulo the kernel of a natural binary section

When an actor covers SL₂ on a natural section, its commutators cover the
whole section. Upper and lower transvections give the two coordinate
components of each vector, and the original section coordinates lift
these displacements to ambient group commutators.

The application is DGS, *Groups and Graphs* (1985), 9.10(5), printed p.149:
the two outer neighborhood modules generate the local actor modulo its
core, so their commutator supplements the kernel of the core quotient.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G]
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- A full natural actor generates the numerator by commutators and the literal kernel. -/
theorem natural_eq_kernel_sup_commutator (H A N : Subgroup G) (q : H →* SL(2,F))
    (σ : Representation (ZMod 2) SL(2,F) V)
    (d : BinaryConjugationSection H A N (σ.comp q))
    (E : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g v, E (σ g v) = Matrix.mulVec g.val (E v))
    (W : Subgroup G) (hWH : W ≤ H)
    (hW : (W.subgroupOf H).map q = ⊤) : A = N ⊔ ⁅A,W⁆ := by
  have hfull : d.image ⁅A,W⁆ = ⊤ := by
    apply top_unique
    intro v _
    have hmove (g : SL(2,F)) (w : V) : σ g w - w ∈ d.image ⁅A,W⁆ := by
      obtain ⟨a,ha,hag⟩ := show g ∈ (W.subgroupOf H).map q by rw [hW]; trivial
      have hh := d.coinvariants_le_image_commutator W hWH
        (Coinvariants.sub_mem_ker (ρ := (σ.comp q).comp (inclusion hWH)) (⟨a,ha⟩ : W) w)
      change σ (q a) w - w ∈ d.image ⁅A,W⁆ at hh
      rwa [hag] at hh
    let u : SL(2,F) := ⟨!![1,1;0,1], by simp [Matrix.det_fin_two_of]⟩
    let l : SL(2,F) := ⟨!![1,0;1,1], by simp [Matrix.det_fin_two_of]⟩
    let v₁ := E.symm ![0,E v 0]
    let v₂ := E.symm ![E v 1,0]
    have he : (σ u v₁ - v₁) + (σ l v₂ - v₂) = v := by
      apply E.injective
      simp only [map_add,map_sub,hE]
      ext i
      fin_cases i <;> simp [u,l,v₁,v₂,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
    exact he ▸ (d.image ⁅A,W⁆).add_mem (hmove u v₁) (hmove l v₂)
  apply le_antisymm
  · simpa only [sup_comm] using d.le_sup_kernel_of_image_top ⁅A,W⁆ hfull
  · exact sup_le d.kernel_le (le_normalizer_iff_commutator_le_left.mp (hWH.trans d.normalized))
end Representation.BinaryConjugationSection
