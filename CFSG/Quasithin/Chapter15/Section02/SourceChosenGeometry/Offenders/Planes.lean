module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Numerics

/-!
# The commutator plane for every member of the actual Sigma difference

Every member of Sigma(T) centralizes V, since its defining maximum
elementary subgroup belongs to J(T). For B in Sigma minus Sigma(T), choose
an actual Delta preimage A outside T. The uniform fixed-space identity on
U_H and N_H(V)=T force B to move V. Quadraticity on U_H passes to the
literal B-image, and the numerical theorem constructs its order-four plane
and proves T-normality.

This is a conditional part of Aschbacher--Smith 15.2.9--11, printed
pp.1110--1111. Uniform Delta quadraticity and centralizer equality, and the
normalizer identity, remain explicit. The existing single minimum-order
actor theorem does not discharge these uniform hypotheses.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

theorem ChosenSmallSource.sigmaAt_centralizes
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hB : B ∈ sigmaAt (T : Subgroup G) H) : B ≤ centralizer (V : Set G) := by
  obtain ⟨A,⟨hA,hAT⟩,rfl⟩ := hB
  have hmax : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) :=
    ⟨hAT,hA.1.2.1,fun C hCT hCE => hA.1.2.2 C (hCT.trans hH.1.1.2) hCE⟩
  exact (inf_le_left.trans (le_sSup hmax)).trans
    (h.centralizing.trans (centralizer_le h.prepared.le_local))

theorem ChosenSmallSource.sigmaOutside_of_moves
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hB : B ∈ sigma H) (hmove : ¬ B ≤ centralizer (V : Set G)) :
    B ∈ sigmaOutside (T : Subgroup G) H :=
  ⟨hB,fun hb => hmove (h.sigmaAt_centralizes hH hb)⟩

theorem ChosenSmallSource.sigmaOutside_plane
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hNV : H ⊓ normalizer (V : Set G) = (T : Subgroup G))
    (hquad : ∀ A ∈ delta H, ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥)
    (hfix : ∀ A ∈ delta H,
      conjugateSpan H V ⊓ centralizer (A : Set G) =
        conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    letI := h.prepared.elementary
    IsElementaryTwo (actor M V B h.prepared.normalized) ∧
      IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V B h.prepared.normalized) ∧
      ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
      (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) := by
  let := h.prepared.elementary
  obtain ⟨A,hA,hAT,rfl⟩ := exists_offender_of_mem_sigmaOutside hB
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let : IsElementaryAbelian 2 (A ⊓ twoCoreIn H : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hmove : ¬ A ⊓ twoCoreIn H ≤ centralizer (V : Set G) := by
    intro hc
    have hVCA : V ≤ centralizer (A : Set G) := by
      have hh := le_inf hVU (le_centralizer_iff.mp hc)
      rw [←hfix A hA] at hh
      exact hh.trans inf_le_right
    apply hAT
    rw [←hNV]
    exact le_inf hA.1.1 ((le_centralizer_iff.mp hVCA).trans
      (Subgroup.centralizer_le_normalizer _))
  have hQT : twoCoreIn H ≤ (T : Subgroup G) := by
    have hh := map_mono (f := H.subtype)
      (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
    change (pCore 2 H).map H.subtype ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hBT : A ⊓ twoCoreIn H ≤ (T : Subgroup G) := inf_le_right.trans hQT
  have hq := actor_quadratic (D := A ⊓ twoCoreIn H)
    h.prepared.normalized hVU inf_le_left (hquad A hA)
  exact ⟨⟨actor_nontrivial _ (hBT.trans h.maximal.1.2) hmove,
    actor_elementary _ (hBT.trans h.maximal.1.2)⟩,hq,
    h.quadratic_actor_plane ha hBT hmove hq⟩

end CFSG.Quasithin.Chapter15.Section02
