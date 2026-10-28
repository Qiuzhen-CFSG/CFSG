module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.LinearOffenders
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallThompson
/-!
# Removing larger-field rows by the same offender

The actual source alternatives are small natural wreath actions, marked
symmetric-five actions, or linear rank-one actions. In every larger linear
row a best offender lies in the two-residual. In a nonsolvable image the
rank-one field is larger than two, and a degree-one pair is impossible.
Thus an offender known to avoid the residual leaves exactly the small rows.
The residual premise is needed only when the original actor is nonsolvable;
this lets common-kernel comparison handle its actual source application.

Source: Aschbacher–Smith3.1.9(5), printed p.578.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource
universe u
variable {D W : Type u} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem minimalParabolic_chief_small_of_offender_not_residual
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    {A : Subgroup (actionImage ρ)}
    (hA : IsBestOffender (Representation.BinaryOffender.imageRepresentation ρ) A)
    (hn : ¬ Group.IsSolvable D → ¬ A ≤ pResidual 2 (actionImage ρ)) :
    SmallNaturalWreathAction (Representation.BinaryOffender.imageRepresentation ρ) ∨
      ChiefFiveMarkedSection (Representation.BinaryOffender.imageRepresentation ρ) ∨
      ∃ c : SourceTwoFactorCase ((Representation.BinaryOffender.imageRepresentation ρ).comp
        (offenderSubgroup (Representation.BinaryOffender.imageRepresentation ρ)).subtype),
        Nonempty (c.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5))) := by
  let q := actionHom ρ
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hf := imageRepresentation_injective ρ
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hff : IsFFModule σ := ⟨A,hA.isOffender σ⟩
  have hqne : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
    obtain ⟨g,hg⟩ := hq (a : actionImage ρ)
    apply ha
    apply Subtype.ext
    change (a : actionImage ρ) = 1
    rw [← hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  have hp := (minimalParabolic_reduced_image S hS q hq hc hqne).2
  by_cases hs : Group.IsSolvable (actionImage ρ)
  · obtain ⟨d,ht,hstable,hr,hgen⟩ :=
      source_solvable_minimalParabolic_factors (S.mapSurjective hq) hp hs hc hf hff
    have hcount := d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank
      q hq (hD.stronglyQuasithin 3 (by decide) (by decide))
    exact Or.inl ((d.toSolvableFFFactors.small_natural_moved_action hf hc hr hcount
      (fun i j => let ⟨t,ht⟩ := ht i j; ⟨t,ht⟩)).wreath)
  · have hns : ¬ Group.IsSolvable D := by
      intro hh
      let := hh
      exact hs (Group.isSolvable_of_surjective (f := q) hq)
    have hn := hn hns
    rcases (minimalParabolic_chief_natural_alternatives ρ hD S hS hff).1
      with hsmall | ⟨hqs,c,hlinear | hsym⟩ | ⟨c,hlinear | hsym⟩
    · exact Or.inl hsmall
    · obtain ⟨F,⟨e⟩⟩ := hlinear
      let := hqs
      let L := generalizedFitting (offenderSubgroup σ)
      let : IsSimpleGroup (L ⧸ center L) := hqs.simple
      let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
      have hF := perfect_linear_two_field_large F e.groupEquiv
      exact (hn (source_quasisimple_linear_offender_le_residual σ
        (S.mapSurjective hq) hp hff hc hqs c F hF ⟨e⟩ hA)).elim
    · exact Or.inr (Or.inl ⟨hqs,c,hsym⟩)
    · obtain ⟨F,⟨e⟩⟩ := hlinear
      have hdeg : F.degree ≠ 1 := fun hh => hs
        (source_pair_degree_one_solvable σ (S.mapSurjective hq) hp hff hc c F hh e)
      have hd : 2 ≤ F.degree := by have := F.degree_pos; omega
      have hF : 3 < Nat.card F.Carrier := by
        have h4 : 4 ≤ Nat.card F.Carrier := by
          rw [F.card_eq]
          exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
        omega
      exact (hn (source_pair_linear_offender_le_residual σ c F hF e hA)).elim
    · exact Or.inr (Or.inr ⟨c,hsym⟩)
end CFSG.Quasithin.ChapterB
