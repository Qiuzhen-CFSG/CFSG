module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.Geometry
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Source

/-!
# The mutually normalizing branch of 12.1.7 on the chosen orbit

The literal pure-intersection premise gives zero natural intersection
for every noncentralizing conjugate, including the inverse conjugate.
The rank contradiction in `Mutual.centralizes_of_pure` therefore discharges
the pair premise in the original degree-four zeroth-closure reduction.
Only the independently produced large-actor obstruction remains in that
application; the compatible model and nonsingular control are permitted inputs.

Source: Aschbacher--Smith, 12.1.7, printed p.792 (PDF p.809).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

/-- The first branch of source 12.1.7, on each actual Sylow-contained conjugate. -/
theorem doubledFour_mutual_centralizes_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.PureIntersectionCentralizes →
    ∀ g : G,
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ T →
      componentOrbit V (T : Subgroup G) ≤ normalizer
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G) →
      ⁅componentOrbit V (T : Subgroup G),
        (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S hp g hg hn
  let M := S.automizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)
  apply ZeroClosure.Mutual.centralizes_of_pure M.setup M.representation_eq
    (fun k hk => ?_) g (hg.trans (D.doubledOrbit_E322 h).normalizes) hn
  rw [M.natural_eq]
  exact B.natural_intersection_eq_bot hp k hk

/-- Apply the proved mutual branch to the parent's actual zeroth-closure
assembly. The remaining actor premise belongs to the nonnormalizing branch. -/
theorem doubledFour_zeroClosure_of_actors_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
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
  exact D.doubledFour_zeroClosure_of_pair_of_actors_of_many h hmany B
    (D.doubledFour_mutual_centralizes_of_many h hmany B S hp) S hc hp hactors

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
