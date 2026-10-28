module
public import ABG.ChapterII.Section1.WreathedLemmaThree
public import ABG.ChapterII.Section1.CentricFusionRelation
public import ABG.ChapterII.Section1.ExtremalNormalizerControl
public import Theory.GroupTheory.FusionRelationTransport

/-!
# Wreathed fusion controlled by the chosen normalizers

For a chosen presentation of a wreathed Sylow two-subgroup S of a finite
group G, any reflexive transitive relation on S containing S-conjugacy
and preserved by normalizer steps at the actual mapped subgroups U and V
is preserved by every ambient conjugacy. This is the opening reduction
in Alperin--Brauer--Gorenstein, Chapter II Section 1 Proposition 2, article
p.12, `refs/latex/alperin-brauer-gorenstein-pages/page-013.tex`.

The centric conjugation-family theorem reduces to an extremal subgroup X.
If Aut(X) is a two-group, the normalizer action already occurs inside S.
Otherwise Lemma 3, after transporting the actual centralizer containment
to the subgroup of S, says that X is U or an S-conjugate of V. The first
case uses the U hypothesis directly. In the second, conjugating the entire
normalizer step reduces to the V hypothesis, and the endpoint conjugacies
are absorbed by transitivity. No assumption that the chosen representatives
are tame intersections or extremal subgroups is needed.
-/

namespace ABG.Wreathed
open BenderSuzuki.External
variable {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {n : ℕ}
    (P : Presentation S n)

/-- The two chosen normalizers control relations under ambient element fusion. -/
public theorem representative_fusion_relation
    (R : S → S → Prop) (hrefl : ∀ x, R x x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hconj : ∀ {x y : S}, IsConj x y → R x y)
    (hU : ∀ g : G, g ∈ Subgroup.normalizer
      (P.U.map (S : Subgroup G).subtype : Set G) →
      ∀ x y : S, (x : G) ∈ P.U.map (S : Subgroup G).subtype →
      g⁻¹ * (x : G) * g = (y : G) → R x y)
    (hV : ∀ g : G, g ∈ Subgroup.normalizer
      (P.V.map (S : Subgroup G).subtype : Set G) →
      ∀ x y : S, (x : G) ∈ P.V.map (S : Subgroup G).subtype →
      g⁻¹ * (x : G) * g = (y : G) → R x y)
    {x y : S} (hxy : IsConj (x : G) (y : G)) : R x y := by
  apply centric_fusion_relation S R hrefl htrans (fun X hX hc => ?_) hxy
  intro g hg x y hx hstep
  by_cases hAut : IsPGroup 2 (MulAut X)
  · exact hconj (extremal_normalizer_fusion_control S X hX hAut g hg x y hx hstep)
  · let X₀ : Subgroup S := X.subgroupOf (S : Subgroup G)
    let e : X₀ ≃* X := Subgroup.subgroupOfEquivOfLe hX.1
    have hA : ¬ IsPGroup 2 (MulAut X₀) := fun h => hAut (h.of_equiv (MulAut.congr e))
    have hc₀ : Subgroup.centralizer (X₀ : Set S) ≤ X₀ := by
      intro a ha
      apply hc
      refine ⟨a.property, ?_⟩
      intro b hb
      exact congrArg Subtype.val (ha ⟨b, hX.1 hb⟩ hb)
    rcases exceptional_centric_classification P X₀ hc₀ hA with heq | ⟨s, hs⟩
    · have hmap := congrArg (fun W : Subgroup S => W.map (S : Subgroup G).subtype) heq
      rw [Subgroup.map_subgroupOf_eq_of_le hX.1] at hmap
      rw [hmap] at hg hx
      exact hU g hg x y hx hstep
    · have hmap := congrArg (fun W : Subgroup S => W.map (S : Subgroup G).subtype) hs
      have he : (S : Subgroup G).subtype.comp (MulAut.conj s).toMonoidHom =
          (MulAut.conj (s : G)).toMonoidHom.comp (S : Subgroup G).subtype := by
        ext a
        rfl
      rw [Subgroup.map_map, he, ← Subgroup.map_map,
        Subgroup.map_subgroupOf_eq_of_le hX.1] at hmap
      exact Subgroup.normalizer_fusion_relation_of_conjugate (S : Subgroup G) X
        (P.V.map (S : Subgroup G).subtype) R htrans hconj s hmap hV g hg x y hx hstep

end ABG.Wreathed
