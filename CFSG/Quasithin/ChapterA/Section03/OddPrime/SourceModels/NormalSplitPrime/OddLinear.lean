module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Action
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ProjectiveIndices
public import Theory.SpecificGroups.PSL3.OddPrimeOuterExponent
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear

/-!
# The odd-prime linear split branch

An odd prime actor on PSL₃(r), r an odd prime, has inner-diagonal action:
its square is linear and its order is odd. The sixth and determinant outer
exponents force p = 3 and r ≡ 1 mod 3. The actor lies outside the inner
image, so the index-three comparison gives the full PGL₃ image. The checked
kernel and generation comparisons identify the actual star component and
the ambient star residual, proving all of source alternative (2).

Source: Aschbacher–Smith A.3.18, printed pp.51–53; GLS3, Theorem 2.5.12.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open scoped MatrixGroups
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
variable {H : Type*} [Group H] [Finite H]

theorem ordinary_odd_linear_projective
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p r : ℕ} (hp : p.Prime) (ho : Odd p) (hrank : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : r.Prime) (hro : Odd r)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 r)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    p = 3 ∧ SignedCongruence false r ∧
      ClassicalGroup.IsPSL (starComponent p K) 3 r ∧
        IsPGLThree (primeToResidual 3 (Star p H)) r := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hns := Group.IsPerfect.not_isSolvable PSL(3,F)
  let f := normalAction K e
  have hb := hH.stronglyQuasithin p hp ho
  have hd6 : p ∣ 6 := prime_dvd_of_action_power_inner hz hrank hb e a ha haK
    (Matrix.PSL3.odd_prime_sixth_power_inner hns hr hro hF (f a))
  have hnot2 : ¬ p ∣ 2 := hp.coprime_iff_not_dvd.mp (Nat.coprime_two_right.mpr ho)
  have hd3 : p ∣ 3 := (hp.dvd_mul.mp (show p ∣ 2 * 3 from hd6)).resolve_left hnot2
  have hp3 : p = 3 := ((Nat.dvd_prime Nat.prime_three).mp hd3).resolve_left hp.ne_one
  cases hp3
  have hdiv : 3 ∣ r - 1 :=
    (Nat.prime_three.dvd_mul.mp (prime_dvd_of_action_power_inner hz hrank hb e a ha haK
      (Matrix.PSL3.odd_prime_split_power_inner hns hr hro hF (f a)))).resolve_left (by decide)
  have hmod : r % 3 = 1 := by
    have := hr.two_le
    have := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hapow : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hcube : f a ^ 3 = 1 := by rw [← map_pow, hapow, map_one]
  have hfa : f a ∈ innerDiagonal F := by
    have hs := (innerDiagonal F).pow_mem
      (OddPrimeSquares.square_mem_innerDiagonal hns hr hro hF (f a)) 2
    have hh : (f a ^ 2) ^ 2 = f a := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hcube, one_mul]
    exact hh ▸ hs
  have hi : MulAut.innerSubgroup PSL(3,F) ≤ f.range := by
    rw [← normalAction_component_image K e]
    exact Subgroup.map_le_range f K
  have hdiag : f.range ≤ innerDiagonal F := by
    rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup, normalAction_component_image,
      MonoidHom.map_zpowers]
    exact sup_le (inner_le_innerDiagonal F) (zpowers_le.mpr hfa)
  have hneq : f.range ≠ MulAut.innerSubgroup PSL(3,F) := by
    intro he
    have hh : f a ∈ MulAut.innerSubgroup PSL(3,F) := he ▸ (show f a ∈ f.range from ⟨a, rfl⟩)
    have hh' := prime_dvd_of_action_power_inner hz hrank hb e a ha haK
      (m := 1) (by simpa only [pow_one] using hh)
    norm_num at hh'
  have he : f.range = innerDiagonal F := by
    apply actionImage_eq_of_index_three _ _ _ hi hdiag hneq
    rw [← Nat.card_congr (pglEquivInnerDiagonal F).toEquiv,
      card_pgl_three_eq_three_mul_psl (by simpa only [hF] using hmod)]
    congr 1
    exact Nat.card_congr (MonoidHom.ofInjective (inner_injective F)).toEquiv
  let E : Star 3 H ≃* Matrix.ProjGenLinGroup (Fin 3) F :=
    (componentActionStarEquiv hz hrank hb e).trans
      ((MulEquiv.subgroupCongr he).trans (pglEquivInnerDiagonal F).symm)
  refine ⟨rfl, hmod, ?_, ?_⟩
  · exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(componentStarQuotientEquiv hz hrank hb).symm.trans e⟩⟩
  · exact ⟨F, inferInstance, inferInstance, hF,
      ⟨((MulEquiv.subgroupCongr (star_residual_eq_top_of_split hz hrank a ha hgen)).trans
        Subgroup.topEquiv).trans E⟩⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
