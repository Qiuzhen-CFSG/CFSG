module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Model
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Normalization

/-!
# Zeroth-closure reductions on the actual chosen doubled orbit

Nonsingular centralizer control gives r ≥ n on the original orbit. In
rank five H.9.2 and E.3.32 make every Sylow-contained conjugate mutually
normalizing. In rank four E.3.4 bounds the actor of a nonnormalizing
conjugate, while the pure-intersection premise makes its natural core
fixed by the inner actor.

The mutual-normalization contradictions and the last rank-four H.9.3
actor obstruction remain explicit in the assembly theorems. They are
independent mathematical obligations, not conclusions of this module.
Source: Aschbacher--Smith, 12.1.3 and 12.1.7, printed pp.789--790,792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

/-- Every Sylow-contained conjugate is normalized by the original degree-five orbit.
No pure-vector fusion or pure-intersection hypothesis is used. -/
theorem doubledFive_normalizes_conjugate_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
    ∀ g : G, (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ T →
      componentOrbit V (T : Subgroup G) ≤ normalizer
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S hc g hg
  let M := S.automizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)
  exact ZeroClosure.five_normalizes_conjugate M.setup M.representation_eq
    (B.globalR_ge (D.doubledOrbit_normalizer_eq h B.orbit_eq) hc) g
    (hg.trans (D.doubledOrbit_E322 h).normalizes)

/-- The literal degree-five W₀ statement once the mutual-normalization
argument has been supplied. This is an assembly implication, not yet 12.1.3. -/
theorem doubledFive_zeroClosure_of_pair_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hpair : ∀ g : G,
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ T →
      componentOrbit V (T : Subgroup G) ≤ normalizer
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G) →
      ⁅componentOrbit V (T : Subgroup G),
        (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      indexedWeakClosure (componentOrbit V (T : Subgroup G)) T 0 ≤
        (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      0 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro S hc
  have hw : 0 < globalW (componentOrbit V (T : Subgroup G)) T := by
    apply bot_lt_iff_ne_bot.mpr
    intro he
    obtain ⟨g, hg, hn⟩ := (globalW_eq_zero_iff _ _).mp he
    apply hn
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (hpair g hg (D.doubledFive_normalizes_conjugate_of_many h hmany B S hc g hg)))
  exact ⟨weakClosure_le_centralizer_of_lt_globalW hw, hw⟩

/-- The literal H.9.3 fixed-space obstruction extracted from a degree-four
noncentralizing, nonnormalizing conjugate in the original Sylow. -/
theorem doubledFour_zero_actor_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers → B.PureIntersectionCentralizes →
    ∀ g : G,
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅componentOrbit V (T : Subgroup G),
        (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ¬ componentOrbit V (T : Subgroup G) ≤ normalizer
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G) →
      let M := S.automizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)
      let I := inducedAutomizer (componentOrbit V (T : Subgroup G))
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom)
      IsElementaryAbelian 2 I ∧ 4 ≤ rank I ∧
        M.setup.natural ⊓ BinaryNaturalDual.generatedCore
          (M.setup.representation.comp I.subtype) 3 ≤
        M.setup.fixed (I ⊓ componentLayer (Automizer (componentOrbit V (T : Subgroup G)))) := by
  let := D.doubledOrbit_elementary h
  intro S hc hp g hg hnc hn
  let W := componentOrbit V (T : Subgroup G)
  let A := W.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let M := S.automizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)
  have hA := hg.trans (D.doubledOrbit_E322 h).normalizes
  have hr := B.globalR_ge (D.doubledOrbit_normalizer_eq h B.orbit_eq) hc
  refine ⟨inducedAutomizer_elementary W A hA,
    ZeroClosure.rank_ge_of_not_normalized g hA hn hr, ?_⟩
  apply ZeroClosure.natural_core_le_inner_fixed M.setup M.representation_eq g hA
    (r := 4) (k := 3) _ hr (by decide)
  rw [M.natural_eq]
  exact B.natural_intersection_eq_bot hp g hnc

/-- Assembly of the literal degree-four W₀ containment from the two remaining
local geometric arguments. No dimension-five closure premise is needed here. -/
theorem doubledFour_zeroClosure_of_pair_of_actors_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hpair : ∀ g : G,
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ T →
      componentOrbit V (T : Subgroup G) ≤ normalizer
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G) →
      ⁅componentOrbit V (T : Subgroup G),
        (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers → B.PureIntersectionCentralizes →
    (let M := S.automizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)
     ∀ I : Subgroup (Automizer (componentOrbit V (T : Subgroup G))),
       IsElementaryAbelian 2 I → 4 ≤ rank I →
       ¬ M.setup.natural ⊓ BinaryNaturalDual.generatedCore
         (M.setup.representation.comp I.subtype) 3 ≤
           M.setup.fixed (I ⊓ componentLayer (Automizer (componentOrbit V (T : Subgroup G))))) →
      indexedWeakClosure (componentOrbit V (T : Subgroup G)) T 0 ≤
        (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      0 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro S hc hp hactors
  have hw : 0 < globalW (componentOrbit V (T : Subgroup G)) T := by
    apply bot_lt_iff_ne_bot.mpr
    intro he
    obtain ⟨g, hg, hn⟩ := (globalW_eq_zero_iff _ _).mp he
    have hnc : ⁅componentOrbit V (T : Subgroup G),
        (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
      intro hh
      exact hn (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
    by_cases hnorm : componentOrbit V (T : Subgroup G) ≤ normalizer
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G)
    · exact hnc (hpair g hg hnorm)
    · obtain ⟨hi, hr, hf⟩ := D.doubledFour_zero_actor_of_many h hmany B S hc hp g hg hnc hnorm
      exact hactors _ hi hr hf
  exact ⟨weakClosure_le_centralizer_of_lt_globalW hw, hw⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
