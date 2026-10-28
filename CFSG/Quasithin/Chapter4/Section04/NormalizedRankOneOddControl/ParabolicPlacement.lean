module
public import Theory.GroupTheory.CentralCoverTwoLocalPlacement
public import Theory.GroupTheory.ResidualCentralQuotientImage
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import CFSG.Quasithin.Chapter4.Defs
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki

/-!
# Full Ree parabolic placement through the original component cover

Lift the nontrivial root radical invariantly through the component's central
quotient. Residual uniqueness puts the full parabolic preimage in N(L).
It already belongs to N(A), so it normalizes the fixed odd-actor residual.
Thus the original residual image is normal inside the actual full Suzuki
parabolic, with the same quotient and inner conjugation maps.
Source: the parabolic maximality step in Aschbacher--Smith 4.4.12,
printed pp.621--622. Residual uniqueness is an explicit ambient premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

theorem ree_suzuki_parabolic_preimage_and_normality
    {G : Type*} [Group G] [Finite G] {L A K : Subgroup G}
    (hKN : K ≤ normalizer (A : Set G))
    (hFK : oddActorResidual L A ≤ K)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    {m : ℕ} (e : (K ⧸ center K) ≃* ReeF4.Model m) (g : ReeF4.Model m)
    (hpar : (residualQuotientMap hFK e).range.map (MulAut.conj g).toMonoidHom ≤
      ReeF4.ConverseParabolics.parabolic m .suzuki) :
    let q := (MulAut.conj g).toMonoidHom.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    let P := ReeF4.ConverseParabolics.parabolic m .suzuki
    (P.comap q).map K.subtype ≤ normalizer (L : Set G) ∧
      ((q.comp (inclusion hFK)).range.subgroupOf P).Normal := by
  intro q P
  have hq : Function.Surjective q := (MulAut.conj g).surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hc : q.ker ≤ center K := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    apply (MulAut.conj g).injective
    exact hx.trans (by simp only [map_one])
  have hFB : (q.comp (inclusion hFK)).range ≤ P := by
    simpa only [q,residualQuotientMap,MonoidHom.comp_assoc,MonoidHom.range_comp] using hpar
  have hPM := central_preimage_le_of_unique_maximalTwoLocal hFK hu.2.2 q hq hc
    P (ReeF4.ConverseParabolics.radical m .suzuki)
    (ReeF4.ConverseParabolics.radical_isPGroup m .suzuki)
    (ReeF4.ConverseParabolics.suzuki_radical_ne_bot m)
    (ReeF4.ConverseParabolics.suzuki_parabolic_le_radical_normalizer m) hFB
  refine ⟨hPM,image_normal_in_of_preimage_normalizes hFK q hq P hFB ?_⟩
  exact (le_inf hPM ((map_subtype_le _).trans hKN)).trans (normalizes_oddActorResidual L A)
end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
