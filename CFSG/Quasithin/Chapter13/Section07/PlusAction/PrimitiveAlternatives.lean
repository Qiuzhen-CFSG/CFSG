module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.PrimitiveRank
public import Theory.GroupTheory.PResidual.SubnormalCorePreimage

/-!
# The complete primitive opening alternatives for source 13.7.4

Nonfaithfulness of the literal plus action supplies the source subgroup
K=O²(preimage(K*)). Its simple-component branch retains the actual intrinsic
quotient; its odd branch has order p or p², is normal in H, and lies outside
M by the earlier normal-kernel exclusion. Both branches satisfy the exact
commutator and centralizer formulas (!) and (*), belong to X_f, and exclude
L₁. The later component catalogue and module exclusions remain separate.

Source: Aschbacher--Smith13.7.4(1), printed pp.936--937.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion Section03.Noncentrality PlusAction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Source primitive selection with the actual residual preimage, full
rank restriction, and original-group kernel calculations. -/
theorem source_plus_primitive_alternatives
    (h1223 : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Chapter12.Section02.Structural1222.{u} KnownSimple.IsKnownSimple)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W}
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hσ : ¬ Function.Injective σ) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let C := (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype
    ∃ J : Subgroup H, let K := J.map H.subtype
      starResidual H (J.map (QuotientGroup.mk' (pCore 2 H))) = J ∧
      K ≤ C ∧ (K.subgroupOf H).IsSubnormal ∧ IsPPerfect 2 K ∧ K ≠ ⊥ ∧
      ChapterA.Section04.IsFaithfulSignalizerType K ∧ ¬ F.L₁ ≤ K ∧
      K ⊓ centralizer (fixedLayer F : Set G) = K.pCoreIn 2 ∧
      ⁅F.UH, K⁆ = ⁅fixedLayer F, K⁆ ∧ ⁅fixedLayer F, K⁆ ≠ ⊥ ∧
      ⁅fixedLayer F, K⁆ ≤ K.pCoreIn 2 ∧ K.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      K.pCoreIn 2 ≤ centralizer (fixedLayer F : Set G) ∧
      ((J.IsCComponent ∧ IsSimpleGroup (J ⧸ pCore 2 J)) ∨
        (∃ p : ℕ, p.Prime ∧ Odd p ∧ H ≤ normalizer (K : Set G) ∧ ¬ K ≤ M ∧
          ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥ ∧
          IsElementaryAbelian p (J ⧸ pCore 2 J) ∧
          (Nat.card (J ⧸ pCore 2 J) = p ∨ Nat.card (J ⧸ pCore 2 J) = p ^ 2))) := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  obtain ⟨J, hm, hJC, hn, hp, hJne, hf, hc, hcomm, hmove, h1, h2, h3⟩ :=
    source_plus_primitive_of_not_faithful d h hU s hσ
  let K := J.map H.subtype
  have hsub : K.subgroupOf H = J := comap_map_eq_self_of_injective H.subtype_injective J
  have hnJ : J.IsSubnormal := hsub ▸ hn
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  have hpJ : IsPPerfect 2 J := hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hneJ : J ≠ ⊥ := fun he => hJne (by simp only [he, Subgroup.map_bot])
  have hKC : K ≤ kernel F := hJC.trans_eq (section_action_kernel (D := F) s)
  have hres : starResidual H (J.map (QuotientGroup.mk' (pCore 2 H))) = J :=
    Theory.GroupTheory.residual_core_preimage_eq J hnJ hpJ
  refine ⟨J, hres, hJC, hn, hp, hJne, hf,
    fun hL => local_residual_not_le_kernel d h hne (hL.trans hKC),
    hc, hcomm, hmove, h1, h2, h3, ?_⟩
  rcases hm with hm | ⟨p, hprime, ho, hnormal, hchief, hE⟩
  · exact Or.inl hm
  · have hnormalK : H ≤ normalizer (K : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (map_subtype_le J)).mp (hsub.symm ▸ hnormal)
    exact Or.inr ⟨p, hprime, ho, hnormalK,
      normal_kernel_not_le_local d h1223 structural h hU hV hne hKC hnormalK hp hJne,
      hchief, hE, source_primitive_odd_order d h hpJ hneJ hprime ho hE⟩

end CFSG.Quasithin.Chapter13.Section07
