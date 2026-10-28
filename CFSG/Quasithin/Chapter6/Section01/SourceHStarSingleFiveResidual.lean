module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarSingleFiveOverlap
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarSeedResidual
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.ThompsonNormalizer

/-!
# The original single-five seed residual

The actual marked row supplies the original S4 overlap, Sylow index three,
and the same transposition-four image of J(T). Restricting the whole quotient
retains its full two-kernel. Its native Thompson normalizer has order eight,
so the seed-residual source now applies without local geometry callbacks.
The resulting residual is normalized by L, not asserted to be normal in H.
Source: Aschbacher--Smith 6.1.5 and E.2.3, pp.666 and 216--217.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

theorem hstar_single_five_seed_residual
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI : U.Normal := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).normal
    letI : IsElementaryAbelian 2 U := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup α
    ∀ _hqs : IsQuasisimple (generalizedFitting Y),
    ∀ s : MovedSection (α.comp Y.subtype) (generalizedFitting Y),
    ∀ _e : MarkedActionEquiv s.action (offenderSubgroup s.action) (generalizedFitting Y)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)),
      let N := H ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)
      let R := (pResidual 2 N).map N.subtype
      R = ⁅R,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
        R ≤ centralizer
          (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) ∧
        L ≤ normalizer (R : Set G) := by
  intro U C q α Y hqs s e
  obtain ⟨hN,p,hpk,hp,a,_,hJ,hi,_⟩ :=
    h.hstar_single_five_overlap hout hH hZH hqs s e
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let N := H ⊓ centralizer (Z : Set G)
  let S := T.subtype hH.1.1.2
  have hTN : (T : Subgroup G) ≤ N := le_inf hH.1.1.2 (by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm)
  let inc : N →* H := inclusion (show N ≤ H from inf_le_left)
  let pN : N →* Equiv.Perm (Fin 5) := p.comp inc
  have hkN : IsPGroup 2 pN.ker := by
    change IsPGroup 2 (p.ker.comap inc)
    rw [hpk]
    exact pCore_isPGroup.comap_of_injective inc (inclusion_injective _)
  have hmapS : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hmapB : (M.subgroupOf H).map H.subtype = H ⊓ M :=
    (subgroupOf_map_subtype M H).trans (inf_comm M H)
  have hiN : ((T : Subgroup G).subgroupOf N).index = 3 := by
    change (T : Subgroup G).relIndex N = 3
    rw [show N = H ⊓ M from hN,←hmapS,←hmapB,
      relIndex_map_map_of_injective _ _ H.subtype_injective]
    exact hi
  have hSi : ((T : Subgroup G).subgroupOf N).map inc = (S : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_map]
    change ((T : Subgroup G).subgroupOf N).map N.subtype = _
    rw [map_subgroupOf_eq_of_le hTN,hmapS]
  have hJi : (elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf N)).map pN =
      (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom := by
    change (elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf N)).map (p.comp inc) = _
    rw [←map_map,←elementaryAbelianMaxJ_map_injective inc (inclusion_injective _),hSi]
    exact hJ
  apply h.hstar_seed_residual_of_index_three hout hH hZH hiN pN hkN
  rw [hJi]
  exact IsPGroup.of_card (n := 3) (ChapterC.SymmetricFive.source_thompson_image_normalizer_card a)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
