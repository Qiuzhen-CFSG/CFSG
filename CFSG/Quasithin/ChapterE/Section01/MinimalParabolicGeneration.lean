module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.ConjugacyFamilySpan

/-!
# E-generation from minimal parabolics

Minimal parabolics over a Sylow subgroup, together with its normalizer,
generate the group by B.6.6. Intrinsic E-generation of each parabolic places
it in the ambient generation target through the actual restricted elementary
family and E-member inheritance. The Sylow normalizer normalizes the weak
closure. A finite maximum turns separate positive witnesses into one bound.

This is the generation form of E.1.12 and the following McBride reduction,
Aschbacher--Smith, combined manuscript of 1 March 2004, printed p.214;
B.6.6, printed p.113. The local witnesses are genuine earlier inputs:
no attainment is inferred merely from the numeric infimum definition.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

theorem isEGenerated_of_minimalParabolics {n : ℕ} (T : Sylow 2 G)
    (hlocal : ∀ P : Subgroup G, ChapterB.IsMinimalParabolicOver T P →
      IsEGenerated n P) : IsEGenerated n G := by
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget n T Ω
  rw [← ChapterB.minimalParabolics_sup_normalizer T]
  apply sup_le
  · exact sSup_le fun P hP => ChiefOrbit.overgroup_le_generationTarget T P
      hP.1.1.le hΩ (hlocal P hP)
  · exact (SubgroupFamily.normalizer_le_span_normalizer
      (fun A hA g => hΩ.2 g A hA) (T : Subgroup G)).trans le_sup_right

theorem exists_generation_of_minimalParabolics (T : Sylow 2 G)
    (hlocal : ∀ P : Subgroup G, ChapterB.IsMinimalParabolicOver T P →
      ∃ n : ℕ, 0 < n ∧ IsEGenerated n P) :
    ∃ n : ℕ, 0 < n ∧ IsEGenerated n G := by
  classical
  let I := {P : Subgroup G // ChapterB.IsMinimalParabolicOver T P}
  let : Fintype I := Fintype.ofFinite I
  have hs : ∀ P : I, ∃ n : ℕ, 0 < n ∧ IsEGenerated n P.val :=
    fun P => hlocal P.val P.property
  choose f hpos hgen using hs
  refine ⟨max 1 (Finset.univ.sup f), Nat.zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  apply isEGenerated_of_minimalParabolics T
  intro P hP
  exact (hgen ⟨P, hP⟩).mono ((Finset.le_sup (f := f)
    (Finset.mem_univ ⟨P, hP⟩)).trans (le_max_right _ _))
end CFSG.Quasithin.ChapterE

