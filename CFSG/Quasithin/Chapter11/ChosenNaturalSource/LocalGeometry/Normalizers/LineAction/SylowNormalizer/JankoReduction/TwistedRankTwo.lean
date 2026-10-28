module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.RankTwo
public import Theory.SpecificGroups.Triality.OddSupplement
public import Theory.SpecificGroups.ReeF4.OddSupplement
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups

/-!
# Twisted rank-two and solvable-endpoint exclusions

The genuine graph-field triality carrier and the exceptional Ree fixed group
supply the same two-parabolic geometry as the untwisted models. Applying the
original quotient-action obstruction excludes both entire families. Proper
Sylow overgroups in the actual Tits and A₆ carriers are solvable, which excludes
the nonsolvable residual image in those endpoints as well.

The final application starts with the original Sylow-normalizer escape and
retains its literal component, residual and quotient. Remaining recognition
and terminal obligations stay with qt-d-1222-natural-line-action.
Source: Aschbacher--Smith, A.3.12 and 3.3.12, pp.47--48,589--590.
The concrete models retain the attribution and license in LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The genuine graph-field D₄ carrier is excluded by its two root parabolics. -/
theorem quotient_not_even_triality {n : ℕ} (hn : 1 ≤ n) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^n) (E.component ⧸ pCore 2 E.component) := by
  intro hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hm
  exact E.false_of_two_sylow_overgroups
    (Triality.Standard.OddSupplement.two_sylow_overgroups_of_equiv n (by omega) e)

/-- The actual exceptional fixed group, not a family label, supplies the Ree exclusion. -/
theorem quotient_not_ree {m : ℕ} (hm : 1 ≤ m) :
    ¬ Chapter1.Section02.LocalModels.IsReeF4At (E.component ⧸ pCore 2 E.component) m := by
  intro h
  obtain ⟨e⟩ := (ReeF4.exists_localBlockInput_mulEquiv_iff _ m).mp h
  exact E.false_of_two_sylow_overgroups (ReeF4.OddSupplement.two_sylow_overgroups_of_equiv m hm e)

/-- A proper local component cannot have a container whose proper full-Sylow
subgroups are all solvable. -/
theorem quotient_not_equiv_solvable_sylow_overgroups {M : Type*} [Group M]
    (hsol : SolvableSylowOvergroups M) :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* M) := by
  rintro ⟨e⟩
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  have hlocal : E.residualImage ∈ ChapterA.Section03.localCComponents P :=
    hP.symm ▸ E.residualImage_local
  exact E.residualImage_ne_top
    (ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups P
      hlocal E.componentQuotient_isCComponent le_top
      (SolvableSylowOvergroups.of_equiv (topEquiv.trans e) hsol))

/-- The actual Parrott carrier of the Tits group is excluded. -/
theorem quotient_not_tits :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Tits.ParrottGroup) :=
  E.quotient_not_equiv_solvable_sylow_overgroups Tits.ProperSylowOvergroups.solvableSylowOvergroups

/-- The six-letter alternating carrier is excluded by its proper Sylow overgroups. -/
theorem quotient_not_alternating_six :
    ¬ Chapter1.Section02.LocalModels.IsAlternating (E.component ⧸ pCore 2 E.component) 6 :=
  E.quotient_not_equiv_solvable_sylow_overgroups AlternatingSix.ProperSylowOvergroups.isSolvable

end MovedComponent

/-- The actual escaping configuration excludes both twisted rank-two families
and the Tits and A₆ endpoints in the same original quotient. -/
theorem exists_moved_component_not_twisted_rank_two (f : InvariantFlag c)
    (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      (∀ n, 1 ≤ n → ¬ Triality.Standard.IsTrialityGroupAt (2^n)
        (E.component ⧸ pCore 2 E.component)) ∧
      (∀ m, 1 ≤ m → ¬ Chapter1.Section02.LocalModels.IsReeF4At
        (E.component ⧸ pCore 2 E.component) m) ∧
      (¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Tits.ParrottGroup)) ∧
      (¬ Chapter1.Section02.LocalModels.IsAlternating (E.component ⧸ pCore 2 E.component) 6) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,fun _ hn => E.quotient_not_even_triality hn, fun _ hm => E.quotient_not_ree hm,
    E.quotient_not_tits,E.quotient_not_alternating_six⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
