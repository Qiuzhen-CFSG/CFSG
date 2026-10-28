module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalOddRadical
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.Prime
public import Stellmacher.ElementaryAbelianMaxJMap
/-!
# The original odd-chief prime and selected branch

The reduced Sylow action contains an actual SL₂(2) factor. Since both the
ambient quotient by the selected normal actor and its two-core are 2-groups,
that factor forces the odd chief prime to be 3. The final selected-witness
wrapper transports the equality through the original H and G quotient maps.

Source: Aschbacher--Smith 13.7.4(1), B.2.16, printed pp.937--938.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₃ M H : Subgroup G}

/-- The actual primitive odd chief actor has prime three. -/
theorem source_primitive_odd_prime_eq_three
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (ho : Odd (Nat.card (J ⧸ pCore 2 J)))
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (p : ℕ) [Fact p.Prime] (hp : IsPGroup p (J ⧸ pCore 2 J)) : p = 3 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  let KX := K.subgroupOf X
  have hXH : X ≤ H := sup_le (hJC.trans (kernel_le_H (D := F)))
    ((pCoreIn_le 2 _).trans h.local_le)
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hJn)
  let e : KX ≃* J := (subgroupOfEquivOfLe (show K ≤ X from le_sup_left)).trans
    (J.equivMapOfInjective H.subtype H.subtype_injective).symm
  have hpX : IsPGroup p (KX ⧸ pCore 2 KX) := hp.of_equiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  obtain ⟨S,hS⟩ := source_primitive_odd_sylow h J hJC hJn ho
  have hgen : KX ⊔ (S : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left), hS,
      ← MonoidHom.range_eq_map, range_subtype]
  have hc : centralizer (reducedTwoSubgroup X : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [map_centralizer_subtype]
    exact source_primitive_odd_reduced_centralizer h hU J hJC hJn ho
  apply ChapterB.prime_eq_three_of_reduced_sylow_movement p KX hpX S hgen hc
  intro hmove
  have hm := map_mono (f := X.subtype) hmove
  rw [← elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective, hS, map_centralizer_subtype] at hm
  exact source_primitive_odd_thompson_movement h hU J hJC hJn ho hout hB
    (hm.trans inf_le_right)


/-- The selected original kernel witness is a component or an elementary
three-chief actor of order three or nine. -/
theorem source_ordinary_kernel_three_branch
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
          (Nat.card (J ⧸ pCore 2 J) = 3 ∨ Nat.card (J ⧸ pCore 2 J) = 9))) := by
  obtain ⟨J,hKC,hp,hneJ,hL,hc,hm⟩ :=
    source_ordinary_kernel_odd_branch d h1221 h hU eL hne hV hk hB
  dsimp only at *
  refine ⟨J,hKC,hp,hneJ,hL,hc,?_⟩
  rcases hm with hm | ⟨p,hprime,ho,hn,hout,hchief,hE,hcard,_⟩
  · exact Or.inl hm
  · have hoJ : Odd (Nat.card (J ⧸ pCore 2 J)) := by
      rcases hcard with he|he
      · exact he ▸ ho
      · exact he ▸ ho.pow
    let : Fact p.Prime := ⟨hprime⟩
    let : IsElementaryAbelian p (J ⧸ pCore 2 J) := hE
    have he := source_primitive_odd_prime_eq_three h hU J hKC hn hoJ hout hB p
      (IsElementaryAbelian.isPGroup p _)
    subst p
    exact Or.inr ⟨hn,hout,hchief,hE,hcard⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
