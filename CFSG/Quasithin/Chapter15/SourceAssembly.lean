module

public import CFSG.Quasithin.Chapter15.Section01.SourceReduction
public import CFSG.Quasithin.Chapter15.Section01.SourceTheorem1513
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.NoncentralSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData

/-!
# Source case assembly for Theorem E

The central involution centralizer has at least one maximal two-local
 overgroup. In the multiple-overgroup branch the original Section15.4
 theorem applies with corrected source F.6. In the singleton branch the
 original reduction15.1.3 supplies either one of the six model groups or
 the full orthogonal action. The latter constructs the literal local datum
 used by the independent15.3.1 exclusion, choosing the first residual in
 Hypothesis15.3.10.

The original15.1.3 and15.3.1 implications remain explicit until their source
 proofs are assembled. This module proves the final case split, not either
 of those independent branch theorems.

Source: Aschbacher--Smith, Theorem15.1.3, Theorem15.3.1, Theorem15.4.25
 and the final proof of Theorem E, printed pp.1086,1121,1165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source centralizer split for Theorem E. The singleton branch retains
the genuine conclusion of 15.1.3 and the original orthogonal exclusion 15.3.1;
the many-centralizer branch is fully supplied by corrected source F.6. -/
theorem source_theoremE_of_original_reductions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (h1513 : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (h1531 : ∀ M Mc : Subgroup G, IsOrderingMaximal T M →
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      NaturalOrthogonalAction M (localModule T M) → False) :
    ClassificationModels.IsTheoremEModel G := by
  rcases Section04.centralizer_overgroup_cases_section03 hG T with
    ⟨Mc, _, hu⟩ | hcentral
  · rcases h1513 Mc hu with h | ⟨M, hM, ⟨action⟩⟩
    · exact h
    · exact (h1531 M Mc hM hu action).elim
  · exact Section04.InitialSource.KnownSimpleSource.source_many_theoremE_from_f_source
      sourceF hG T hempty hcentral

omit [Finite G] in
/-- The orthogonal datum used by the final 15.3.1 consumer is constructed
from the original action. Its residual is the first choice of 15.3.10. -/
theorem orthogonal_exclusion_of_original_local_data
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hlocal : ∀ d : CharacteristicTwo.LocalData G,
      d.T = T → IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} → False)
    (action : NaturalOrthogonalAction M (localModule T M)) : False := by
  let d : CharacteristicTwo.LocalData G := {
    T := T
    M := M
    Mc := Mc
    sylow_le := hM.1.2
    action := action
    Yplus := residualY M Mc
    choice := Or.inl rfl }
  exact hlocal d rfl hM hu

end CFSG.Quasithin.Chapter15
