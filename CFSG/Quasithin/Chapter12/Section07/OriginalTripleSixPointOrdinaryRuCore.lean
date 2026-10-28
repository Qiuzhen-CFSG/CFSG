module

public import Theory.SpecificGroups.Rudvalis.Model.PointQuaternion.Core
import all Theory.SpecificGroups.Rudvalis.Model.PointQuaternion.Core
import all Theory.SpecificGroups.Rudvalis.Model.PointCoreBound
import all Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Separation

/-!
# The center of the actual Rudvalis involution-centralizer two-core

Four displayed words in the original Sylow coordinates preserve every block
of the actual five-letter quotient, so lie in its two-core. Commuting with
these four words leaves only normal-form indices zero and 6144. The existing
two-point decoder and complete Sylow normal forms turn this kernel-checked
finite certificate into the intrinsic center bound, then conjugacy carries
it to every involution in the central class.

The import-all edges reuse the private native coordinate certificate without
changing its public boundary. All new numerical checks concern the preserved
ATLAS degree-4060 action; discovery data are in Scratch/DirectTripleSixOrdinary/RuCore.
Source: Aschbacher--Smith C.3.1 and 12.7.5, printed pp.151 and840.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section07
open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open Max6Certificate CoreQuotients.Max6Blocks PointCoreBound

private def coreIndex (i : Fin 4) : Fin 16384 := ![61,1,12,64] i

set_option maxRecDepth 60000 in
private theorem core_blocks : ∀ i : Fin 4, ∀ j : Fin 5,
    (alignedBlock j).image (normalMap (coreIndex i)) = alignedBlock j := by
  decide +kernel

private theorem core_word_mem (i : Fin 4) :
    candidateNormalForm (coreIndex i) ∈
      (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2 := by
  apply PointQuaternion.mem_core_of_blocks _ (candidateNormalForm_mem _)
  intro j x hx
  rw [normal_smul,←core_blocks i j]
  exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

set_option maxRecDepth 60000 in
private theorem center_filter : ∀ n : Fin 16384,
    (∀ i : Fin 4,
      normalMap n (normalMap (coreIndex i) 0) = normalMap (coreIndex i) (normalMap n 0) ∧
      normalMap n (normalMap (coreIndex i) 1) = normalMap (coreIndex i) (normalMap n 1)) →
    n = 0 ∨ n = 6144 := by
  apply allIndices
  decide +kernel

private theorem core_le_candidate :
    (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2 ≤ candidate := by
  have hi : ¬ 2 ∣ candidate.index := by
    intro hi
    apply not_two_pow_fifteen_dvd_card_model
    rw [←candidate.card_mul_index,candidate_card]
    exact Nat.mul_dvd_mul_left 16384 hi
  let S : Sylow 2 Model := candidate_isTwoGroup.toSylow hi
  have hh := pCoreIn_le_sylow _ (S.subtype candidate_le_point_centralizer)
  change (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2 ≤
    (candidate.subgroupOf (centralizer ({elementaryGenerator 0} : Set Model))).map
      (centralizer ({elementaryGenerator 0} : Set Model)).subtype at hh
  rwa [map_subgroupOf_eq_of_le candidate_le_point_centralizer] at hh

/-- The center of the literal marked point core has at most two elements. -/
theorem ordinary_ru_marked_core_center_card_le_two :
    Nat.card (center ((centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2)) ≤ 2 := by
  classical
  let Q := (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2
  let n : center Q → Fin 16384 := fun x =>
    Classical.choose (exists_candidateNormalForm (core_le_candidate x.val.property))
  have hn (x : center Q) : candidateNormalForm (n x) = (x.val : Model) :=
    Classical.choose_spec (exists_candidateNormalForm (core_le_candidate x.val.property))
  have hc (x : center Q) : n x = 0 ∨ n x = 6144 := by
    apply center_filter
    intro i
    have he : candidateNormalForm (n x) * candidateNormalForm (coreIndex i) =
        candidateNormalForm (coreIndex i) * candidateNormalForm (n x) := by
      rw [hn]
      exact (congrArg Subtype.val (mem_center_iff.mp x.property
        ⟨candidateNormalForm (coreIndex i),core_word_mem i⟩)).symm
    constructor
    · simpa only [mul_smul,normal_smul] using congrArg (fun z : Model => z • (0 : Fin 4060)) he
    · simpa only [mul_smul,normal_smul] using congrArg (fun z : Model => z • (1 : Fin 4060)) he
  let f : center Q → Bool := fun x => decide (n x = 0)
  have hf : Function.Injective f := by
    intro x y he
    have heq : n x = n y := by
      rcases hc x with hx | hx <;> rcases hc y with hy | hy
      · exact hx.trans hy.symm
      · simp [f,hx,hy] at he
      · simp [f,hx,hy] at he
      · exact hx.trans hy.symm
    apply Subtype.ext
    apply Subtype.ext
    rw [←hn x,←hn y,heq]
  have hBool : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_bool]
  simpa only [hBool] using Nat.card_le_card_of_injective f hf

/-- The same center bound holds at every actual central-class involution. -/
theorem ordinary_ru_point_core_center_card_le_two (z : Model) (hz : IsConj z (b^2)) :
    Nat.card (center ((centralizer ({z} : Set Model)).pCoreIn 2)) ≤ 2 := by
  have hlocal : IsConj centralInvolution (elementaryGenerator 0) :=
    isConj_iff.mpr ⟨conjugator,conjugator_alignment⟩
  have hsquare : IsConj centralInvolution (b^2) :=
    isConj_iff.mpr ⟨LowCentralizers.squareConjugator,LowCentralizers.squareConjugator_alignment⟩
  obtain ⟨g,hg⟩ := isConj_iff.mp (hz.trans (hlocal.symm.trans hsquare).symm)
  let t := MulAut.conj g
  have hD : (centralizer ({z} : Set Model)).map t.toMonoidHom =
      centralizer ({elementaryGenerator 0} : Set Model) := by
    rw [map_point_centralizer]
    change t z = elementaryGenerator 0 at hg
    rw [hg]
  have hQ := map_pCoreIn_of_injective 2 (centralizer ({z} : Set Model)) t.toMonoidHom t.injective
  rw [hD] at hQ
  let e := (t.subgroupMap ((centralizer ({z} : Set Model)).pCoreIn 2)).trans
    (MulEquiv.subgroupCongr hQ)
  rw [Nat.card_congr (centerCongr e).toEquiv]
  exact ordinary_ru_marked_core_center_card_le_two

end CFSG.Quasithin.Chapter12.Section07
