module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineAmbientParallel.SupportAction
public import Theory.GroupTheory.Commutator.CentralSingletonIndex

/-!
# Exact critical point-centralizers in the ambient-nine branch

The reciprocal point commutator puts every critical point in [U,J] and
outside Z. The original lifting theorem and the four-dimensional moved
quotient then force its centralizer image to have order four. Commutators
with O₂(J) lie in Z, so the centralizer meets that literal core in index
two. Counting through J → J/O₂(J) gives centralizer index eighteen in J.

Consequently each actual critical point-centralizer has index two in a
Sylow subgroup of the same J and is normalized by that Sylow subgroup.
This identifies the subgroup for the remaining ambient normalizer argument;
it does not exclude E₉:C₄ or establish original 14.6.12.

Source: Aschbacher--Smith, 14.6.1(5), 14.6.2 and the original 14.6.12
configuration, printed pp.1020--1021,1031, with F.9.13--17, pp.322--324
of refs/quasithin.pdf. These are consequences of the original hypotheses,
not an invocation of the later 14.6.13 alternatives.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

open OddCriticalPair.OrthogonalSource


/-- The point at every critical endpoint lies in the actual moved span and
is distinct from the original point. -/
private theorem critical_point_generator
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint, ∃ u : D.UH,
      zpowers (u : G) = i.conjugate D.V₁ ∧
      (u : G) ∈ ⁅D.UH,J⁆ ∧ (u : G) ∉ D.V₁ := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  have hb := (source_rankTwo_critical_track_bounds
    hG T hempty hM hu hmany hcard e hab J hJ.1).1
  obtain ⟨hcomm,_,_,hdis,_,_⟩ := source_singleton_nine_paired_point_lines
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hpW : i.conjugate D.V₁ ≤ ⁅D.UH,J⁆ := by
    rw [←hcomm]
    exact commutator_mono inf_le_left (i.large_le hb)
  have hpc : Nat.card (i.conjugate D.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
  obtain ⟨z,hz,hzne⟩ := (i.conjugate D.V₁).bot_or_exists_ne_one.resolve_left (by
    intro hz
    rw [hz,card_bot] at hpc
    omega)
  let u : D.UH := ⟨z,moved_le a (hpW hz)⟩
  refine ⟨u,?_,hpW hz,fun hh => hzne (hdis.le ⟨hh,hz⟩)⟩
  apply eq_of_le_of_card_ge (zpowers_le.mpr hz)
  rw [hpc]
  exact Nat.succ_le_of_lt ((zpowers z).one_lt_card_iff_ne_bot.mpr
    (fun hh => hzne (Subgroup.zpowers_eq_bot.mp hh)))

/-- The centralizer of every critical point has full cyclic-four image;
its intersection with the original two-core has index two in that core. -/
theorem source_singleton_nine_point_centralizer_indices
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
      (C ⊓ J.pCoreIn 2).relIndex (J.pCoreIn 2) = 2 ∧
      Nat.card ((C.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 4 ∧
      C.relIndex J = 18 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  obtain ⟨u,hline,huW,huZ⟩ := critical_point_generator
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have he : centralizer ({(u : G)} : Set G) = centralizer (i.conjugate D.V₁ : Set G) := by
    rw [←centralizer_closure,←zpowers_eq_closure,hline]
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  let C₀ := C.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := C₀.map q
  have hBfour : Nat.card B = 4 := by
    have hbound := source_solvable_moved_point_image_index
      hG T hempty hM hu hmany hcard e hab J hJ hs a u huW huZ
    rw [he,source_singleton_nine_moved_finrank
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine] at hbound
    obtain ⟨_,_,htwo | hfour⟩ := source_singleton_nine_point_centralizers
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
    · have hh := B.card_mul_index
      rw [show Nat.card B = 2 from htwo,
        (source_singleton_nine_quotient_structure
          hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine).1] at hh
      change B.index ≤ 2 ^ 4 at hbound
      omega
    · exact hfour
  have hcore : C.relIndex D.QH = 2 := by
    have hc : (centralizer ({(u : G)} : Set G)).relIndex D.QH ≤ 2 := by
      simpa only [h.point_card] using central_singleton_centralizer_index_le
        D.QH D.V₁ (h.point_lt.le.trans ((le_conjugateSpanBy _ _).trans h.UH_le_QH))
        (le_centralizer_iff.mp ((pCoreIn_le 2 J).trans h.H_centralizes))
        (h.UH_le_QH u.property)
        ((commutator_mono (zpowers_le.mpr u.property) le_rfl).trans h.commutator_UH_QH_le_point)
    have hi : C.relIndex D.QH =
        (centralizer ({(u : G)} : Set G)).relIndex D.QH := by
      rw [he]
      change (J ⊓ centralizer (i.conjugate D.V₁ : Set G)).relIndex D.QH = _
      rw [inf_comm,←inf_relIndex_right,inf_assoc,
        inf_eq_right.mpr (show D.QH ≤ J from pCoreIn_le 2 J),inf_relIndex_right]
    rw [←hi] at hc
    have hpos : C.relIndex D.QH ≠ 0 := index_ne_zero_of_finite
    have hne : C.relIndex D.QH ≠ 1 := by
      intro h1
      apply huZ
      rw [←source_solvable_moved_core_centralizer hG T hempty hM hu hmany hcard e hab J hJ hs a]
      refine ⟨huW,?_⟩
      intro x hx
      have hh := (relIndex_eq_one.mp h1 hx).2
      rw [←he] at hh
      exact mem_centralizer_singleton_iff.mp hh
    omega
  have hQindex : (pCore 2 J).index = 36 := by
    rw [(pCore 2 J).index_eq_card]
    exact (source_singleton_nine_quotient_structure
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine).1
  have hcore₀ : C₀.relIndex (pCore 2 J) = 2 := by
    have hh := relIndex_map_map_of_injective C₀ (pCore 2 J) J.subtype_injective
    rw [map_subgroupOf_eq_of_le (show C ≤ J from inf_le_left)] at hh
    exact hh.symm.trans hcore
  have himage : (pCore 2 J).relIndex C₀ = 4 := by
    have hh := relIndex_ker C₀ q
    rw [QuotientGroup.ker_mk'] at hh
    exact hh.trans hBfour
  have h1 := relIndex_mul_index (H := C₀ ⊓ pCore 2 J) (K := pCore 2 J) inf_le_right
  have h2 := relIndex_mul_index (H := C₀ ⊓ pCore 2 J) (K := C₀) inf_le_left
  rw [inf_relIndex_right,hcore₀,hQindex] at h1
  rw [inf_relIndex_left,himage] at h2
  refine ⟨?_,hBfour,?_⟩
  · exact (inf_relIndex_right C D.QH).trans hcore
  · change C₀.index = 18
    omega

/-- The actual point-centralizer is an index-two subgroup of a Sylow
subgroup of the same J, and is normalized by that Sylow subgroup. -/
theorem source_singleton_nine_point_centralizer_sylow
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
      ∃ S : Sylow 2 J,
        C ≤ (S : Subgroup J).map J.subtype ∧
        C.relIndex ((S : Subgroup J).map J.subtype) = 2 ∧
        (S : Subgroup J).map J.subtype ≤ normalizer (C : Set G) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  let C₀ := C.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hC := (source_singleton_nine_point_centralizers
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).1
  change IsPGroup 2 C at hC
  obtain ⟨S,hCSraw⟩ := (hC.comap_subtype : IsPGroup 2 C₀).exists_le_sylow
  have hCS : C₀ ≤ (S : Subgroup J) := hCSraw
  have hindex := (source_singleton_nine_point_centralizer_indices
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2
  have hSI : (S : Subgroup J).index = 9 := by
    let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
    obtain ⟨hc,hsy⟩ := source_singleton_nine_quotient_structure
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
    have hh := (S' : Subgroup (J ⧸ pCore 2 J)).card_mul_index
    rw [(hsy S').2,hc] at hh
    have he : (S' : Subgroup (J ⧸ pCore 2 J)).index = (S : Subgroup J).index :=
      index_map_eq (S : Subgroup J) (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']
        exact pCore_isPGroup.le_sylow_of_normal S)
    omega
  have hi : C₀.relIndex (S : Subgroup J) = 2 := by
    have hh := relIndex_mul_index hCS
    change C₀.index = 18 at hindex
    rw [hSI,hindex] at hh
    omega
  have hn : (C₀.subgroupOf (S : Subgroup J)).Normal := normal_of_index_eq_two hi
  let := hn
  have hNS : (S : Subgroup J) ≤ normalizer (C₀ : Set J) := by
    have hh := (C₀.subgroupOf (S : Subgroup J)).le_normalizer_map (S : Subgroup J).subtype
    rw [map_subgroupOf_eq_of_le hCS,normalizer_eq_top,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hN : (S : Subgroup J).map J.subtype ≤ normalizer (C : Set G) := by
    have hh := (map_mono (f := J.subtype) hNS).trans (C₀.le_normalizer_map J.subtype)
    rwa [map_subgroupOf_eq_of_le (show C ≤ J from inf_le_left)] at hh
  refine ⟨S,?_,?_,hN⟩
  · have hh := map_mono (f := J.subtype) hCS
    rwa [map_subgroupOf_eq_of_le (show C ≤ J from inf_le_left)] at hh
  · have hh := relIndex_map_map_of_injective C₀ (S : Subgroup J) J.subtype_injective
    rw [map_subgroupOf_eq_of_le (show C ≤ J from inf_le_left)] at hh
    exact hh.trans hi

end CFSG.Quasithin.Chapter14.Section06
