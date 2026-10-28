module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.CubicExtension.LocalData
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.CubicExtension.Automorphisms

/-!
# Reduction of the Rudvalis cubic normalizer to component centralizers and fusion

For the actual involution centralizer C = E₄ × Sz(8), let I be the ambient
image of its layer. If the ambient centralizer of I is precisely the first
factor, C = I C(I), so the relative normalizer index divides three. Fusion
moving the involution inside the first factor makes this index exactly three.
The full normalizer action then lifts the precise matrix field automorphism
to an actor of order three. The last theorem applies the odd-index result to
the literal Sylow image constructed in ProductSylow.

Source: GLS3 Table 5.3r, Note 2, and printed pp.291–292;
Aschbacher–Smith I.2.2(7), printed pp.412–413 (PDF pp.423–424).

The ambient component-centralizer equality and moving fusion are explicit
remaining model obligations. These conditional reductions do not assert that
those obligations follow from the abstract direct-product centralizer alone.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.CubicExtension
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory

variable {E : Type} [Group E]

/-- The ambient centralizer equality suffices for the odd relative index. -/
public theorem odd_index_of_component_centralizer (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1)
    (hcentralizer : centralizer (componentFactor C eC : Set Model) = fourFactor C eC) :
    ¬ 2 ∣ C.relIndex (normalizer (componentFactor C eC : Set Model)) := by
  have hd := normalizer_index_dvd_three (componentFactor C eC) (componentEquiv C eC)
  rw [hcentralizer, factor_sup] at hd
  intro htwo
  exact (by decide : ¬ 2 ∣ 3) (htwo.trans hd)

/-- The Sylow produced by ProductSylow is already Sylow in the literal
component normalizer once its ambient centralizer is known. -/
public theorem exists_normalizerSylow_of_component_centralizer (C : Subgroup Model)
    (eC : C ≃* E × SuzukiMatrixGroup 1) (hE : Nat.card E = 4)
    (hcentralizer : centralizer (componentFactor C eC : Set Model) = fourFactor C eC) :
    ∃ R : Sylow 2 (normalizer (componentFactor C eC : Set Model)),
      (R : Subgroup (normalizer (componentFactor C eC : Set Model))).map
        (normalizer (componentFactor C eC : Set Model)).subtype =
          sylowImage (centralizerEmbedding C eC) :=
  exists_overgroupSylow C _ eC hE (centralizer_le_normalizer C eC)
    (odd_index_of_component_centralizer C eC hcentralizer)

/-- Conditional assembly on the actual layer image. The two remaining model
inputs concern the ambient centralizer and fusion, with no normalizer input. -/
public theorem normalizer_geometry_of_centralizer_and_fusion [IsElementaryAbelian 2 E]
    (i : Model) (I : Subgroup Model)
    (eC : centralizer ({i} : Set Model) ≃* E × SuzukiMatrixGroup 1)
    (hE : Nat.card E = 4)
    (hLayer : (componentLayer (centralizer ({i} : Set Model))).map
      (centralizer ({i} : Set Model)).subtype = I)
    (hFactor : componentFactor _ eC = I)
    (hcentralizer : centralizer (I : Set Model) = fourFactor _ eC)
    (hfusion : ∃ g : Model, g * i * g⁻¹ ∈ fourFactor _ eC ∧ g * i * g⁻¹ ≠ i) :
    let C := centralizer ({i} : Set Model)
    C ≤ normalizer (I : Set Model) ∧
    C.relIndex (normalizer (I : Set Model)) = 3 ∧
    ¬ 2 ∣ C.relIndex (normalizer (I : Set Model)) ∧
    (∃ (y : normalizer (I : Set Model)) (e : I ≃* SuzukiMatrixGroup 1),
      orderOf (y : Model) = 3 ∧
      I.normalizerMonoidHom y = MulAut.congr e.symm (suzukiFieldAutomorphism 1)) ∧
    ∃ R : Sylow 2 (normalizer (I : Set Model)),
      (R : Subgroup (normalizer (I : Set Model))).map (normalizer (I : Set Model)).subtype =
        sylowImage (centralizerEmbedding C eC) := by
  rcases hFactor with rfl
  let C := centralizer ({i} : Set Model)
  let I := componentFactor C eC
  have hsup : I ⊔ centralizer (I : Set Model) = C := by
    rw [hcentralizer, factor_sup]
  have hout := exists_component_normalizer_outside i eC hLayer hfusion
  have hindex := normalizer_index_three_of_outside I (componentEquiv C eC) (by
    rwa [hsup])
  have hodd := odd_index_of_component_centralizer C eC hcentralizer
  refine ⟨centralizer_le_normalizer C eC, ?_, hodd, ?_,
    exists_normalizerSylow_of_component_centralizer C eC hE hcentralizer⟩
  · rwa [hsup] at hindex
  · obtain ⟨y, hy, he⟩ := exists_exact_field_actor I (componentEquiv C eC) hindex (by
      intro x hx
      rw [hcentralizer] at hx
      exact fourFactor_square C eC hx)
    exact ⟨y, componentEquiv C eC, hy, he⟩

end Rudvalis.CoveringIncidence.NormalizerGeometry.CubicExtension
