module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NonsolvableAlternatives
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree.ExceptionalFactor
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.RankOne
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ReducedSolvability
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
/-!
# Complete natural-factor dispatch on the original B.6.9 action

The proved full B.5 classifier applies to the faithful core-free offender
action with its actual SQTK cover. The genuine minimal-parabolic exclusions
remove the hyperplane and higher-rank rows. The result retains either the
original quasisimple moved section, naturally SL₂ or marked S₅, or the same
two natural rank-one factors and their source module decomposition.

The second theorem constructs every quotient hypothesis from the original
reduced normal subgroup. In particular, the solvable core kernel preserves
nonsolvability and the SQTK quotient keeps its literal original cover.
No classification or module-recognition premise remains.

Source: Aschbacher–Smith B.6.9, printed pp.115–116, using B.5.6.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
universe u v
variable {G : Type u} [Group G] [Finite G]

theorem nonsolvable_offender_natural_source
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hf : Function.Injective ρ)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hcover : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple G)) :
    let Y := offenderSubgroup ρ
    let σ := ρ.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        (∃ F : BinaryField, IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) F 2) ∨
        Nonempty (MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ c : SourceTwoFactorCase σ,
        SourceRankOneFactor σ c.first c.firstSpace ∧
          SourceRankOneFactor σ c.second c.secondSpace := by
  rcases nonsolvable_offender_classification ρ adequateClassification_knownSimple
      T hP hs hf hff hcore hcover with ⟨hqs,⟨c⟩⟩ | hrest
  · exact Or.inl ⟨hqs,c,source_offender_quasisimple_rank_one ρ T hP hff hcore hqs c⟩
  · rcases hrest with ht | hh
    · obtain ⟨c⟩ := ht
      exact Or.inr ⟨c,source_offender_two_factor_rank_one ρ T hP hff hcore c⟩
    · obtain ⟨c⟩ := hh
      exact (source_offender_hyperplane_excluded ρ T hP hff hcore c).elim

theorem reduced_nonsolvable_natural_source
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U) (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup ρ
    let σ := ρ.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        (∃ F : BinaryField, IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) F 2) ∨
        Nonempty (MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ c : SourceTwoFactorCase σ,
        SourceRankOneFactor σ c.first c.firstSpace ∧
          SourceRankOneFactor σ c.second c.secondSpace := by
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hker : q.ker = C := QuotientGroup.ker_mk' C
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    change elementaryAbelianMaxJ (T : Subgroup G) ≤ C
    rw [←hker,he]
    exact le_top
  have hp := (minimalParabolic_reduced_image T hP q hq hU.quotient_pCore_eq_bot hn).2
  have hsQ : ¬ Group.IsSolvable (G ⧸ C) := fun hh =>
    hs (solvable_of_reduced_minimalParabolic_action T hP U hU hJ q hq hker hh)
  have hff : IsFFModule ρ := by
    obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hf
  let c : SQTKQuotient KnownSimple.IsKnownSimple (G ⧸ C) := {
    Cover := G
    kernel := C
    sqtk := hG
    equiv := MulEquiv.refl _ }
  exact nonsolvable_offender_natural_source ρ (T.mapSurjective hq) hp hsQ
    (NormalElementaryQuotient.representation_injective U q hq hker) hff hU.quotient_pCore_eq_bot ⟨c⟩
end CFSG.Quasithin.ChapterB
