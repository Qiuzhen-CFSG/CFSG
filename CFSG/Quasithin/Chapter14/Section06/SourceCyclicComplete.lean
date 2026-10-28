module

public import CFSG.Quasithin.Chapter14.Section06.SourceCyclicEnumerated
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsCompletion

/-!
# Ambient recognition in the original cyclic residual branch

The original cyclic reduction settles the cubic case and leaves the literal
index-five pair `[J, sourceResidual M Mc ⊔ T]`. Given the genuine first-endpoint
alternatives, the proved second-parabolic theorem supplies its cubic partner.
Quintic enumeration aligns the whole intersection and both inclusion maps,
and excludes the full Ree endpoint by the original centralizer argument.
The surviving Tits marking then gives ambient recognition by 14.2.22.

The cyclic consumer retains precisely the original source hypotheses and
the first-endpoint alternatives when the index is five. Its odd-core
application excludes cyclic residual for the actual minimal subgroup of a
counterexample outside the Theorem E models. The first-endpoint premise
remains with `qt-e-quintic-first-parabolic`; `qt-e-quintic-recognition` owns
its final discharge here and the application to `qt-e-14625-source`.
These conditional results do not assert unconditional 14.6.12.

Source: Aschbacher--Smith 14.6.11--12(2), printed pp.1030--1031, using
14.2.20--22, pp.988--989, and F.1.11--12, pp.262--264. The concrete Tits
first quotient is the corrected Sz(2).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab

/-- The original cyclic branch reaches an ambient Theorem E model. Only
the genuine index-five first-parabolic alternatives remain explicit; the
second endpoint, compatible marking and ambient recognition are proved. -/
theorem source_solvable_minimal_cyclic_theoremE_of_first_parabolic
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    (hcyc : IsCyclic (pResidual 2 (J ⧸ pCore 2 J)))
    (hfirst : (T : Subgroup G).relIndex J = 5 →
      Nonempty (Tits.ExceptionalParabolics.FullRee.first ≃* J) ∨
      Nonempty (Tits.ExceptionalParabolics.first ≃* J)) :
    ClassificationModels.IsTheoremEModel G := by
  rcases source_solvable_minimal_cyclic_model_or_tits_fusion_of_endpoints
      hG T hempty hM hu hmany hcard e hab J hJ hs hcyc hfirst
      (fun hi => Section02.SolvableAmalgam.QuinticSecondParabolic.source_second_parabolic
        hG T hempty hM hu hmany hcard e J hJ hi) with hmodel | ⟨htits, _⟩
  · exact hmodel
  · exact Section02.SolvableAmalgam.source_tits_theoremE
      hG T hempty hM hu hmany hcard e J hJ htits

/-- In the original odd-core counterexample, the selected minimal solvable
subgroup has noncyclic residual once the first-endpoint theorem is supplied.
The subgroup, its containment in H and its literal two-core quotient are
unchanged from the source selection. -/
theorem source_oddCore_counterexample_noncyclic_of_first_parabolics
    (hnomodel : ¬ ClassificationModels.IsTheoremEModel G)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥)
    (hfirst : ∀ J : Subgroup G, J ∈ Chapter3.HStar (T : Subgroup G) M →
      (T : Subgroup G).relIndex J = 5 →
      Nonempty (Tits.ExceptionalParabolics.FullRee.first ≃* J) ∨
      Nonempty (Tits.ExceptionalParabolics.first ≃* J)) :
    ∃ J : Subgroup G, J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      J ≤ H ∧ Group.IsSolvable J ∧ ¬ IsCyclic (pResidual 2 (J ⧸ pCore 2 J)) := by
  obtain ⟨J, hJH, hJ, hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  refine ⟨J, hJ, hJH, hs, ?_⟩
  intro hcyc
  exact hnomodel (source_solvable_minimal_cyclic_theoremE_of_first_parabolic
    hG T hempty hM hu hmany hcard e hab J hJ hs hcyc (hfirst J hJ))

end CFSG.Quasithin.Chapter14.Section06
