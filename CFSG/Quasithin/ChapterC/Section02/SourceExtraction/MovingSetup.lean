module
public import CFSG.Quasithin.ChapterC.Defs
public import CFSG.Quasithin.Defs
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.CComponent.RadicalStabilizer
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.SylowCommutatorCore
/-!
# Component normalizers and Thompson stabilizer control

Odd prime rank at most two bounds the orbit of the ordinary component in
G/O₂(G) by two. Its normalizer therefore lifts to a normal subgroup of G.
Once J(R) fixes that component, Thompson heredity makes the full normalizer
of N_R(L) lie in the original characteristic-normalizer control group M.

These are the orbit and normalizer steps in Aschbacher–Smith C.2.4(2),
printed p.144, via Aschbacher, Math. Z. 177 (1981), 10.3.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

theorem component_normalizer_normal {κ : GroupClass} (hG : IsSQTK κ G)
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)] :
    (normalizer (L : Set G)).Normal := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hLq : IsComponent (G ⧸ pCore 2 G) (L.map q) :=
    ⟨hL.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hL)⟩
  have hrank : ∀ p, p.Prime → Odd p → primeRank p (G ⧸ pCore 2 G) ≤ 2 := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have ho := hLq.normal_or_index_two_of_odd_rank_le_two hrank
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  rcases cComponent_normal_or_index_two_of_quotient hL (pCore 2 G) ho with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    infer_instance
  · exact normal_of_index_eq_two hi

theorem stabilizer_normalizer_control {R M L : Subgroup G} (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hJ : elementaryAbelianMaxJ R ≤ normalizer (L : Set G)) :
    normalizer ((R ⊓ normalizer (L : Set G) : Subgroup G) : Set G) ≤ M := by
  have hj : elementaryAbelianMaxJ (R ⊓ normalizer (L : Set G)) = elementaryAbelianMaxJ R :=
    elementaryAbelianMaxJ_eq_of_intermediate R _
      (le_inf (sSup_le fun _ hA => hA.1) hJ) inf_le_left
  have hn := normalizer_le_normalizer_elementaryAbelianMaxJ (R ⊓ normalizer (L : Set G))
  rw [hj] at hn
  exact hn.trans ((normalizer_maxJ_le_characteristicNormalizerClosure R R (sSup_le fun _ hA => hA.1) le_rfl
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup R hr.isPGroup hr.1)).trans hcontrol)

end CFSG.Quasithin.ChapterC.Section02Source
