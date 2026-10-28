module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalOrderExclusion
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalPairExclusion

/-!
# Completion of the original odd-chief cubic branch

The actual reduced Thompson action has one or two symmetric-three factors.
The pair is excluded by the point residual, and irreducibility puts the
selected chief actor inside the remaining one-factor Thompson image.
Consequently its intrinsic quotient is cubic and L₁ centralizes it.
The selected-witness wrapper retains the separate simple-component branch.

Source: Aschbacher--Smith 13.7.4(1), printed p.937.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₃ M H : Subgroup G}

/-- The original elementary three-chief branch is cubic, and the point residual
centralizes its intrinsic quotient. -/
theorem source_primitive_three_quotient_cubic
    {V₂ G₁ : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hnot : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype)
    (hchief : ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥)
    (hE : IsElementaryAbelian 3 (J ⧸ pCore 2 J))
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3 ∨ Nat.card (J ⧸ pCore 2 J) = 9)
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) :
    Nat.card (J ⧸ pCore 2 J) = 3 ∧
      ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
        (J.map H.subtype).pCoreIn 2 := by
  have ho : Odd (Nat.card (J ⧸ pCore 2 J)) := by
    rcases hcard with hc | hc <;> rw [hc] <;> decide
  let : IsElementaryAbelian 3 (J ⧸ pCore 2 J) := hE
  have hm := source_primitive_three_thompson_models d h hU J hJC hJn ho hout hB
    (IsElementaryAbelian.isPGroup 3 _)
  have he := hm.resolve_right (source_primitive_thompson_not_pair d h eL J hJn hnot)
  have hc := source_primitive_order_three_of_thompson_s3 h hU J hJC hJn hchief hE
    hcard hout hB he
  exact ⟨hc,source_primitive_cubic_centralized h J hJn hc⟩

/-- The actual nonfaithful plus kernel selects a component or a cubic chief actor;
the latter branch has the original point-residual centralization. -/
theorem source_ordinary_kernel_cubic_branch
    {V₂ G₁ : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hk : kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) ≠ H.pCoreIn 2)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    ∃ J : Subgroup H, let K := J.map H.subtype
      K ≤ kernel F ∧ IsPPerfect 2 K ∧ K ≠ ⊥ ∧ ¬ F.L₁ ≤ K ∧
      K ⊓ centralizer (fixedLayer F : Set G) = K.pCoreIn 2 ∧
      ((J.IsCComponent ∧ IsSimpleGroup (J ⧸ pCore 2 J)) ∨
        (H ≤ normalizer (K : Set G) ∧ ¬ K ≤ M ∧
          ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥ ∧
          IsElementaryAbelian 3 (J ⧸ pCore 2 J) ∧
          Nat.card (J ⧸ pCore 2 J) = 3 ∧ ⁅K,F.L₁⁆ ≤ K.pCoreIn 2)) := by
  obtain ⟨J,hJC,hp,hJne,hnot,hcent,hm⟩ :=
    source_ordinary_kernel_three_branch d h1221 h hU eL hne hV hk hB
  dsimp only at *
  refine ⟨J,hJC,hp,hJne,hnot,hcent,?_⟩
  rcases hm with hm | ⟨hJn,hout,hchief,hE,hcard⟩
  · exact Or.inl hm
  · have hc := source_primitive_three_quotient_cubic d h hU eL J hJC hJn hnot
      hchief hE hcard hout hB
    exact Or.inr ⟨hJn,hout,hchief,hE,hc⟩
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
