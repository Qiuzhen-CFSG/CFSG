module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Paired.Canonical
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.CoordinateRecognition.OddCores

/-!
# Canonical geometry from the actual solvable source factors

The original reduced solvable action constructs its internal S₃ factors.
For each factor, take the full preimage L of its intrinsic odd core and
N=⟨Baum(T)^L⟩. Factor normality proves ambient subnormality of L and the
original Baumann image normalizes L. The source Baumann theorem and its
full kernel bound then construct the literal Sylow and characteristic-two
geometry of N and prove ambient subnormality of its embedded residual.

The action kernel remains the entire original centralizer. This theorem
does not infer a Frattini bound or minimality for the factor preimage.
Source: Aschbacher--Smith B.6.9--10 and C.1.26, pp.116--117,132.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Paired
open ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem source_canonical_factor_geometry
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hfit : generalizedFitting G = pCore 2 G) (hrank : primeRank 3 G ≤ 2)
    (hsolv : Group.IsSolvable (G ⧸ centralizer (U : Set G))) :
    let q := QuotientGroup.mk' (centralizer (U : Set G))
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ∃ d : ThreeConjugates.SolvableFFStructure α, ∀ i : Fin d.count,
      let L := (d.toSolvableFFFactors.factorOddCore i).comap q
      let N := conjugateSpanBy (baumann (T : Subgroup G)) L
      baumann (T : Subgroup G) ≤ normalizer (L : Set G) ∧ L.IsSubnormal ∧
      generalizedFitting N = pCore 2 N ∧
      ((pResidual 2 N).map N.subtype).IsSubnormal ∧
      ∃ S : Sylow 2 N, (S : Subgroup N).map N.subtype = baumann (T : Subgroup G) ∧
        (q.comp N.subtype).ker ≤ centralizer
          (normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N) : Set N) := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let Y := offenderSubgroup α
  let : Y.Normal := offenderSubgroup_normal α
  obtain ⟨d,hBY,hB,hker⟩ := solvable_baumann_kernel_and_layer T hP U hU q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot
    hJ hrank hsolv
  refine ⟨d,fun i => ?_⟩
  let F := d.factor i
  let A := d.toSolvableFFFactors.factorOddCore i
  let L := A.comap q
  let N := conjugateSpanBy (baumann (T : Subgroup G)) L
  have hFY : F ≤ Y := d.toSolvableFFFactors.factor_le_offenderSubgroup i
  have hFnormal : (F.subgroupOf Y).Normal := d.toSolvableFFFactors.factor_normal_in_offenderSubgroup i
  have hFsub : F.IsSubnormal := hFnormal.isSubnormal.trans hFY (inferInstance : Y.Normal).isSubnormal
  have hAsub : A.IsSubnormal := (inferInstance : (pPrimeCore 2 F).Normal).isSubnormal.trans' hFsub
  have hLsub : L.IsSubnormal := hAsub.comap q
  have hYA : Y ≤ normalizer (A : Set _) :=
    ((normal_subgroupOf_iff_le_normalizer hFY).mp hFnormal).trans
      (normalizer_le_normalizer_characteristic_image F (pPrimeCore 2 F))
  have hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G) :=
    (map_le_iff_le_comap.mp (hBY.trans hYA)).trans (A.le_normalizer_comap q)
  have hQL : pCore 2 G ≤ L := by
    intro x hx
    have hc := (le_centralizer_iff.mp hU.le_centralizer_pCore) hx
    have he : q x = 1 := (QuotientGroup.eq_one_iff _).mpr hc
    change q x ∈ A
    rw [he]
    exact A.one_mem
  obtain ⟨S,hS⟩ := canonical_baumann_sylow T L hB
  exact ⟨hBL,hLsub,canonical_baumann_fitting T L hfit hQL,
    canonical_residual_subnormal T L hBL hLsub,S,hS,
    canonical_kernel_centralizes_omegaClosure T q hker L S hS⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Paired
