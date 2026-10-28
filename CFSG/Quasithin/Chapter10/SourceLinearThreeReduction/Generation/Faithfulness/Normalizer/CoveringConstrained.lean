module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CoveringFinite
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedG2Normality
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ContainedComponentPromotion

/-!
# The constrained remainder for a simple original seed

The large symplectic and G₂ rows have a nontrivial radical intersection.
The actual perfect action stabilizes its image, so every odd rank is at
most one. Component normality and the simple-seed action eliminate these
rows. Combining the finite exclusions and the proved rank-one result
leaves only an ordinary component or a binary SL₃ star component.

Source: Aschbacher--Smith C.4.5--8, pp.152--154, used in 4.4.6, p.620.
The degree-three branch is completed in CoveringLinear.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- A normal component whose nontrivial span action has odd ranks at most
one forces the original simple seed to be normalized. -/
theorem normalizes_of_simple_component_action_odd_ranks
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) [K.Normal]
    (hne : coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H) ≠ ⊥)
    (hr : ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  obtain ⟨p,hp,ho,_,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card
    (L ⧸ pCore 2 L) Nat.prime_three
  let : Fact p.Prime := ⟨hp⟩
  exact h.normalizes_of_simple_component_action_rank_le_one hz K hne ho hd (hr p hp ho)

/-- The large binary symplectic row uses the literal radical intersection
and its proved perfect automorphism stabilizer bound. -/
theorem normalizes_of_simple_constrained_symplectic
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F)
    (hF : 4 ≤ Nat.card F) : M ≤ normalizer (L : Set G) := by
  let : K.Normal := h.constrained_symplectic_component_normal K hK hq hout hfK e hF
  apply h.normalizes_of_simple_component_action_odd_ranks hz K
    (h.constrained_span_action_nontrivial K hK hq hout)
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact h.constrained_symplectic_span_rank_le_one K hK hq hout hfK e hF ho

/-- The large binary G₂ row uses its original radical intersection;
no normality of the selected component is assumed. -/
theorem normalizes_of_simple_constrained_g2
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F)
    (hF : 4 ≤ Nat.card F) : M ≤ normalizer (L : Set G) := by
  let : K.Normal := h.constrained_g2_component_normal K hK hq hout hfK e hF
  apply h.normalizes_of_simple_component_action_odd_ranks hz K
    (h.constrained_span_action_nontrivial K hK hq hout)
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact h.constrained_g2_span_rank_le_one K hK hq hout hfK e hF ho

/-- The finite, rank-one, symplectic and G₂ constrained rows are discharged.
Only the ordinary branch and the binary SL₃ star row remain. -/
theorem nonnormal_simple_component_remainder
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (hstrict : M < H) (hn : ¬ M ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧
      (IsComponent H K ∨
        (generalizedFitting K = pCore 2 K ∧
          ∃ F : ChapterB.QuasisimpleSource.BinaryField,
            Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃*
              Matrix.SpecialLinearGroup (Fin 3) F.Carrier))) := by
  have hf : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H :=
    fun hf => hn (h.normalizes_of_fitting_contained hstrict hf)
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := h.ordinary_or_constrained_escape hf
  refine ⟨K,hK,hq,hout,?_⟩
  rcases hcases with hc | hc
  · exact Or.inl hc
  right
  refine ⟨hc,?_⟩
  have hm := C27Source.star_model_from_source (h.constrained_source_input K hK hq hout hc)
  cases hm with
  | linearTwo F e => exact (h.no_constrained_component_star_linear_two K hK hq hout hc F e).elim
  | linearThree F e => exact ⟨F,⟨e⟩⟩
  | symplectic F hF e =>
    apply (hn (h.normalizes_of_simple_constrained_symplectic hz K hK hq hout hc e ?_)).elim
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  | g2 F hF e =>
    apply (hn (h.normalizes_of_simple_constrained_g2 hz K hK hq hout hc e ?_)).elim
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  | g2DerivedTwo e =>
    exact (hn (h.normalizes_of_simple_constrained_star_g2_derived_two hz K hK hq hout hc e)).elim
  | alternating n hd e =>
    rcases hd with rfl | rfl | rfl | rfl
    · exact (h.no_constrained_component_star_alternating_five K hK hq hout hc e).elim
    · exact (hn (h.normalizes_of_simple_constrained_star_alternating hz K hK hq hout hc
        (by decide) (by decide) e)).elim
    · exact (hn (h.normalizes_of_simple_constrained_star_alternating hz K hK hq hout hc
        (by decide) (by decide) e)).elim
    · exact (hn (h.normalizes_of_simple_constrained_star_alternating hz K hK hq hout hc
        (by decide) (by decide) e)).elim
  | linearFiveTwo e =>
    exact (hn (h.normalizes_of_simple_constrained_star_linear_five_two hz K hK hq hout hc e)).elim
  | tripleSix _ e =>
    exact (hn (h.normalizes_of_simple_constrained_star_triple_six hz K hK hq hout hc e)).elim
end CFSG.Quasithin.ChapterC.HypothesisC28
