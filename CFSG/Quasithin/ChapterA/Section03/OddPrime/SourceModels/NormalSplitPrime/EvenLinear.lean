module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ProjectiveIndices
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.RankBound
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.BinaryCubicRankParity
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary

/-!
# The complete cubic binary linear branch

Cubic rank two forces even field degree. For the literal order-three actor,
projective semilinear descent produces a fixed elementary nine whenever its
field part is nontrivial, including mixed field–diagonal actors. Together with
the actor this would have rank three. Thus the actual action is inner-diagonal.
Its outer image is nontrivial, so the index-three comparison gives PGL₃.
The checked kernel and residual identities identify H/O₃′(H) and its full
three-residual with that same model, and the two-core transport returns the
complete source alternative on the original split extension.

No order-preserving replacement of an arbitrary prime-power actor is used;
the hypothesis is the original element of order exactly three. Source:
Aschbacher–Smith A.3.16–18, printed pp.51–53; GLS3 field fixed groups.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open scoped MatrixGroups
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
variable {H : Type*} [Group H] [Finite H]

theorem ordinary_even_linear_cubic_projective
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    (hrank : 1 < primeRank 3 K) (hz : Nat.Coprime 3 (Nat.card (center K)))
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n))
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    SignedCongruence false (2 ^ n) ∧
      ClassicalGroup.IsPSL (starComponent 3 K) 3 (2 ^ n) ∧
        IsPGLThree (primeToResidual 3 (Star 3 H)) (2 ^ n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have heven : Even n := Matrix.PSL3.BinaryCubicRankParity.even_of_rank_two hF
    (by rw [central_model_rank hz e]; omega)
  have hmod : 2 ^ n % 3 = 1 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three, if_pos (Nat.even_iff.mp heven)]
  let f := normalAction K e
  have hb := hH.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hapow : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hfa : f a ∈ innerDiagonal F := by
    apply Matrix.PSL3.StandardCubicFixedNine.innerDiagonal_of_primeRank_three_le_two
      (Group.IsPerfect.not_isSolvable PSL(3,F)) hF heven f.range
      (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
      (normalAction_rank_le_two hz hrank hb e) (f a) ⟨a, rfl⟩
    · rw [standard_eq_top_of_two_power_card F hn hF]
      trivial
    · apply orderOf_eq_prime
      · rw [← map_pow, hapow, map_one]
      · exact fun he => outside_action_not_inner hz hrank hb e a ha haK
          (he ▸ (MulAut.innerSubgroup PSL(3,F)).one_mem)
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
  refine ⟨hmod, ?_, ?_⟩
  · exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(componentStarQuotientEquiv hz hrank hb).symm.trans e⟩⟩
  · exact ⟨F, inferInstance, inferInstance, hF,
      ⟨((MulEquiv.subgroupCongr (star_residual_eq_top_of_split hz hrank a ha hgen)).trans
        Subgroup.topEquiv).trans E⟩⟩

/-- The full linear alternative in the original split extension. Neither
field parity, a two-group center nor inner-diagonal membership is assumed. -/
theorem alternatives_of_even_linear_cubic_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : 1 < primeRank 3 K)
    (hz : Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) 3 (2 ^ n))
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives 3 K := by
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  let f := QuotientGroup.mk' (pCore 2 H)
  have hc : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hz' : Nat.Coprime 3 (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank 3 (twoCoreComponent K) := by
    rwa [twoCore_rank hK (by decide : Odd 3)]
  have ha' := twoCore_actor Nat.prime_three (by decide) a ha haK
  obtain ⟨hcong, hmodel, hpgl⟩ := ordinary_even_linear_cubic_projective (twoCore_sqtk hH)
    hr' hz' hn (hm.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))
    (f a) ha'.1 ha'.2 (twoCore_join a hgen)
  apply Or.inr ∘ Or.inl
  refine ⟨rfl, false, 2 ^ n, hcong,
    hmodel.of_mulEquiv (starComponentEquiv 3 f (QuotientGroup.mk'_surjective _) hc K),
    Or.inl ?_⟩
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hpgl
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨(starResidualEquiv 3 f (QuotientGroup.mk'_surjective _) hc).trans eF⟩⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
