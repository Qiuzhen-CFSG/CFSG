module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadFixedCore
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The elementary product in the original hexad two-core

Let P = O₂(G₁,₃) intersect C_H(X), and let E₁ be the full preimage in Q
of the two-core fixed space. The two factors meet precisely in Z(H).
Their join E is elementary of order 2048 once the native fixed-space facts
make E₁ elementary of order 128.

The extraspecial abelian bound then makes E₁ self-centralizing in Q.
Consequently E = C_(O₂(G₁,₃))(E₁), proving normalization by the whole
G₁,₃ without claiming that it normalizes P. The same calculation gives
E intersect Q = E₁ and C_E(X) = P. The full two-core has order 2^17
independently of those remaining fixed-space premises.

Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), proof of (4.6), p.598, DOI 10.1007/BF01232280.
The general native fixed-space facts, Thompson equality, and full
normalizer/module marking remain separate steps of this source family.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu LocalGeometry LocalGeometry.LocalSubgroups
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

/-- The literal product E in AS91 (4.6). -/
def originalHexadElementary (B : Finset (Fin 22)) : Subgroup (centralizer z) :=
  originalHexadFixedCore h e X B ⊔ originalHexadCore h e X B

theorem originalHexadFixedCore_le (B : Finset (Fin 22)) :
    originalHexadFixedCore h e X B ≤ core z := commutatorPreimage_le _ _ _

theorem center_le_originalHexadFixedCore (B : Finset (Fin 22)) :
    center (centralizer z) ≤ originalHexadFixedCore h e X B := by
  rw [originalHexadFixedCore_eq]
  refine le_inf ?_ (center_le_centralizer _)
  rw [←core_center_eq_centralizer_center h]
  exact map_subtype_le _

theorem originalHexadFixedCore_centralizes (B : Finset (Fin 22)) :
    originalHexadFixedCore h e X B ≤
      Subgroup.centralizer (originalHexadCore h e X B : Set (centralizer z)) := by
  rw [originalHexadFixedCore_eq]
  exact inf_le_right

theorem originalHexadCore_inf_core {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    originalHexadCore h e X B ⊓ core z = center (centralizer z) := by
  apply le_antisymm
  · intro x hx
    have hh : (⟨x,hx.2⟩ : core z) ∈
        (Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))).subgroupOf (core z) :=
      ((originalHexadCore_eq_source h e X B).le hx.1).2
    rw [core_cubic_centralizer h e X] at hh
    rw [←core_center_eq_centralizer_center h]
    exact mem_map_of_mem _ hh
  · refine le_inf (originalHexadCore_data h e X hB).2.2 ?_
    rw [←core_center_eq_centralizer_center h]
    exact map_subtype_le _

theorem originalHexadFixedCore_inf_coreFactor {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    originalHexadFixedCore h e X B ⊓ originalHexadCore h e X B = center (centralizer z) := by
  apply le_antisymm
  · exact (le_inf inf_le_right (inf_le_left.trans (originalHexadFixedCore_le h e X B))).trans
      (originalHexadCore_inf_core h e X hB).le
  · exact le_inf (center_le_originalHexadFixedCore h e X B) (originalHexadCore_data h e X hB).2.2

theorem originalHexadElementary_elementary {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [IsElementaryAbelian 2 (originalHexadFixedCore h e X B)] :
    IsElementaryAbelian 2 (originalHexadElementary h e X B) := by
  let := (originalHexadCore_data h e X hB).1
  exact IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp (originalHexadFixedCore_centralizes h e X B))

theorem originalHexadElementary_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hc : Nat.card (originalHexadFixedCore h e X B) = 128) :
    Nat.card (originalHexadElementary h e X B) = 2048 := by
  have hnorm := (le_centralizer_iff.mp (originalHexadFixedCore_centralizes h e X B)).trans
    (Subgroup.centralizer_le_normalizer _)
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (originalHexadFixedCore h e X B) (originalHexadCore h e X B) hnorm
  rw [hc, (originalHexadCore_data h e X hB).2.1,
    originalHexadFixedCore_inf_coreFactor h e X hB,centralizer_center_card h] at hh
  change Nat.card (originalHexadFixedCore h e X B ⊔ originalHexadCore h e X B : Subgroup (centralizer z))=2048
  omega

theorem originalHexadFixedCore_selfcentralizing {B : Finset (Fin 22)}
    [IsElementaryAbelian 2 (originalHexadFixedCore h e X B)]
    (hc : Nat.card (originalHexadFixedCore h e X B) = 128) :
    core z ⊓ Subgroup.centralizer (originalHexadFixedCore h e X B : Set (centralizer z)) =
      originalHexadFixedCore h e X B := by
  let U := originalHexadFixedCore h e X B
  have hUQ := originalHexadFixedCore_le h e X B
  let := h.extraspecial
  let := IsElementaryAbelian.subgroupOf (p := 2) hUQ
  have hcard : Nat.card (U.subgroupOf (core z))=128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv).trans hc
  have hself := extraspecial_prime_selfcentralizing_of_card_sq (p := 2)
    (U.subgroupOf (core z)) (by rw [hcard,h.core_card]; norm_num)
  apply le_antisymm
  · intro x hx
    have hxC : (⟨x,hx.1⟩ : core z) ∈
        Subgroup.centralizer (U.subgroupOf (core z) : Set (core z)) := by
      intro u hu
      exact Subtype.ext (hx.2 u.val hu)
    exact hself.le hxC
  · exact le_inf hUQ U.le_centralizer

/-- Maximal abelianness in Q makes the literal E a canonical relative centralizer. -/
theorem originalHexadElementary_eq_centralizer {B : Finset (Fin 22)}
    [IsElementaryAbelian 2 (originalHexadFixedCore h e X B)]
    (hc : Nat.card (originalHexadFixedCore h e X B) = 128) :
    originalHexadElementary h e X B = (originalPlaneHexad e B).pCoreIn 2 ⊓
      Subgroup.centralizer (originalHexadFixedCore h e X B : Set (centralizer z)) := by
  let U := originalHexadFixedCore h e X B
  let P := originalHexadCore h e X B
  have hPC := le_centralizer_iff.mp (originalHexadFixedCore_centralizes h e X B)
  rw [originalPlaneHexad_twoCore h e X B]
  apply le_antisymm
  · exact le_inf (sup_le_sup (originalHexadFixedCore_le h e X B) le_rfl)
      (sup_le U.le_centralizer hPC)
  · intro x hx
    obtain ⟨q,hq,p,hp,he⟩ := mem_sup_of_normal_left.mp hx.1
    have hqc : q ∈ Subgroup.centralizer (U : Set (centralizer z)) := by
      have hh := (Subgroup.centralizer (U : Set (centralizer z))).mul_mem hx.2
        ((Subgroup.centralizer (U : Set (centralizer z))).inv_mem (hPC hp))
      rwa [←he,mul_inv_cancel_right] at hh
    have hqU : q ∈ U := (originalHexadFixedCore_selfcentralizing h e X hc).le ⟨hq,hqc⟩
    rw [←he]
    exact mul_mem_sup hqU hp

/-- Normalization follows from the canonical centralizer description,
without assuming that the rank-five factor is preserved by all of G₁,₃. -/
theorem originalHexadElementary_normalized {B : Finset (Fin 22)}
    [IsElementaryAbelian 2 (originalHexadFixedCore h e X B)]
    (hc : Nat.card (originalHexadFixedCore h e X B) = 128) :
    originalPlaneHexad e B ≤ normalizer (originalHexadElementary h e X B : Set (centralizer z)) := by
  rw [originalHexadElementary_eq_centralizer h e X hc]
  exact (le_inf
    ((originalPlaneHexad e B).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (originalPlaneHexad e B))))
    ((originalHexadFixedCore_normalized h e X B).trans
      (normalizer_le_normalizer_centralizer (originalHexadFixedCore h e X B)))).trans
    inf_normalizer_le_normalizer_inf

theorem originalHexadElementary_inf_core {B : Finset (Fin 22)}
    [IsElementaryAbelian 2 (originalHexadFixedCore h e X B)]
    (hc : Nat.card (originalHexadFixedCore h e X B) = 128) :
    originalHexadElementary h e X B ⊓ core z = originalHexadFixedCore h e X B := by
  apply le_antisymm
  · intro x hx
    exact (originalHexadFixedCore_selfcentralizing h e X hc).le
      ⟨hx.2,((originalHexadElementary_eq_centralizer h e X hc).le hx.1).2⟩
  · exact le_inf le_sup_left (originalHexadFixedCore_le h e X B)

/-- The original rank-five factor is precisely C_E(X). -/
theorem originalHexadElementary_cubic_centralizer (B : Finset (Fin 22)) :
    originalHexadElementary h e X B ⊓ fullCubicCentralizer e X = originalHexadCore h e X B := by
  have hP := (originalHexadCore_eq_source h e X B).le
  have hE : originalHexadElementary h e X B ≤ (originalPlaneHexad e B).pCoreIn 2 := by
    rw [originalPlaneHexad_twoCore h e X B]
    exact sup_le_sup (originalHexadFixedCore_le h e X B) le_rfl
  apply le_antisymm
  · exact (inf_le_inf_right _ hE).trans (originalHexadCore_eq_source h e X B).ge
  · exact le_inf le_sup_right (hP.trans inf_le_right)

include h X in
/-- The full local two-core has order 2^17, with the central line counted once. -/
theorem originalPlaneHexad_twoCore_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card ((originalPlaneHexad e B).pCoreIn 2) = 131072 := by
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (core z) (originalHexadCore h e X B) le_normalizer_of_normal
  rw [h.core_card,(originalHexadCore_data h e X hB).2.1,
    inf_comm,originalHexadCore_inf_core h e X hB,centralizer_center_card h,
    ←originalPlaneHexad_twoCore h e X B] at hh
  norm_num at hh ⊢
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
