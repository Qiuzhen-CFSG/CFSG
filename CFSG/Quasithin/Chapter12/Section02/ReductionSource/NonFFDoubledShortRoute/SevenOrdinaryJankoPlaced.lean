module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryJanko
-- Continue the same native normal-image argument for the original odd residual.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryJanko
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryJankoCore
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedNative
public import CFSG.Quasithin.Chapter4.Section04.OddActorQuotient
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore

/-!
# Excluding the placed J₄ component for the original doubled A₇ orbit

Original residual uniqueness makes its native normalizer a maximal two-local.
The actual doubled orbit is normal there. Its trivial residual commutant puts
the whole rank-eight orbit in the center of the normalizer's full two-core.
The native radical classification and the original residual's solvable-kernel
A₇ quotient then contradict normality of that residual image.

The native equivalence is the supplied component-center quotient marking:
the J₄ odd multiplier bound and the original trivial two-core first prove that
the full center vanishes. The residual's own possible central cover is retained.
Source: Aschbacher–Smith 4.4.3 and 4.4.10–11, printed pp.621–623,
refs/quasithin.pdf; the native large-center radical classification is cited in
SevenOrdinaryJanko.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original component selected in the odd normalizer is not a cover of J₄.
No native local placement, residual module marking or core-centrality is assumed. -/
theorem sourceOrbit_seven_oddNormalizer_not_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    ¬ Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  rintro ⟨e⟩
  let : IsQuasisimple K := hK.2
  have hz : center K = ⊥ := DoubledBinaryPlacedNative.center_eq_bot hcore (Or.inl ⟨e⟩)
  let R := oddActorResidual L A
  let W := D.sourceOrbit
  let N := normalizer (A : Set G)
  let K₀ := K.map N.subtype
  let a : K₀ ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let m : K₀ ≃* Janko4.Model := a.trans (DoubledBinaryPlacedNative.nativeEquiv hz e)
  let q := m.toMonoidHom
  let r := q.comp (inclusion hr)
  have hAN := hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf hAN hAC
  obtain ⟨_,hm,hWR,_⟩ := D.doubledOrbit_oddActorResidual_cover h A hA ho
  rw [←D.sourceOrbit_eq] at hm hWR
  have hKN : K₀ ≤ N := map_subtype_le _
  have hcentermap : (center K₀).map a.toMonoidHom = center K := by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr a ⟨z,hz⟩).property
    · intro z hz
      exact ⟨a.symm z,(centerCongr a.symm ⟨z,hz⟩).property,a.apply_symm_apply z⟩
  let eK := (QuotientGroup.congr (center K₀) (center K) a hcentermap).trans e
  have hne : W ≠ ⊥ := D.sourceOrbit_weakClosure_setup.nontrivial
  have huQ : UniqueMaximalOvergroup r.range
      (normalizer (r.range : Set Janko4.Model)) :=
    DoubledBinaryPlacedNormality.residual_image_unique_local hKN hr hu hWR hne hm eK
  have hWR' : W ≤ R := hWR.trans (pCoreIn_le 2 R)
  have hWK : W ≤ K₀ := hWR'.trans hr
  let w := q.comp (inclusion hWK)
  let M := normalizer (r.range : Set Janko4.Model)
  have hqker : q.ker ≤ center K₀ := by
    rw [q.ker_eq_bot_iff.mpr m.injective]
    exact bot_le
  obtain ⟨hwM,hnw⟩ := DoubledBinaryPlacedNormality.whole_module_normal_in_local
    hKN hr hu hWR' (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
    q m.surjective hqker M huQ.1.1 r.range.le_normalizer
  have hnW : M ≤ normalizer (w.range : Set Janko4.Model) :=
    (normal_subgroupOf_iff_le_normalizer hwM).mp hnw
  have hbig := D.sourceOrbit_seven_mapped_core_center
    h hd σ hσ hmodel A hAC ho K₀ hr hWK m M r.range.le_normalizer hwM le_rfl hnW
  have hbig' : 64 ≤ Nat.card (center (pCore 2 M)) := by omega
  obtain ⟨hP,hN,hlarge⟩ :=
    Janko4.LocalStructure.LargeCenterRadicals.maximal_local_core_radical M huQ.1 hbig'
  let P := M.pCoreIn 2
  have hrN : r.range ≤ normalizer (P : Set Janko4.Model) := by
    rw [hN]
    exact r.range.le_normalizer
  let f : R →* normalizer (P : Set Janko4.Model) := r.codRestrict _
    (fun x => hrN ⟨x,rfl⟩)
  have hfi : Function.Injective f := by
    intro x y he
    exact (m.injective.comp (inclusion_injective hr)) (congrArg Subtype.val he)
  have hfk : f.ker = ⊥ := f.ker_eq_bot_iff.mpr hfi
  let : Group.IsSolvable f.ker := hfk.symm ▸ inferInstanceAs (Group.IsSolvable (⊥ : Subgroup R))
  have hfr : f.range = r.range.subgroupOf (normalizer (P : Set Janko4.Model)) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  let : f.range.Normal := hfr.symm ▸ normal_subgroupOf_of_le_normalizer (by
    rw [hN])
  have hcomm := ((le_sectionCentralizer_iff A L).mp
    (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2
  have hAV : A ≤ centralizer (V : Set G) :=
    hAC.trans (centralizer_le (by rw [D.sourceOrbit_eq]; exact le_componentOrbit V T))
  obtain ⟨c,_⟩ := chosen_oddActorResidual_quotient h.toHypothesis1221 D A hAN hcomm ho hAV
  obtain ⟨mark⟩ := hmodel
  let eL := (D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr mark.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
        (by norm_num : 4 ≤ Nat.card (Fin 7)))).trans QuotientGroup.quotientBot))
  let s : R →* (L ⧸ pCore 2 L) := c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hsk : s.ker = pCore 2 R := by
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 R) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable s.ker := hsk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 R))
  let π : R →* alternatingGroup (Fin 7) := eL.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp s)
  have hπ : Function.Surjective π := eL.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  let : Group.IsSolvable π.ker := by
    have he : π.ker = (center (L ⧸ pCore 2 L)).comap s := by
      rw [MonoidHom.ker_comp_of_injective _ _ eL.injective,
        ← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    rw [he]
    exact isSolvable_comap_of_solvable_ker s _
  let : Group.IsPerfect R := oddActorResidual_isPerfect L A
  exact seven_normal_image_not_janko_radical π hπ P hP hlarge f

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
