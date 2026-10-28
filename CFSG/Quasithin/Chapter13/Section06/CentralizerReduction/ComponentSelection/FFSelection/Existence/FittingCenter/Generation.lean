module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Commutator
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Generation.Quasisimple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Generation.SmallBranches
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Generation.Products
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Generation.DoubleThree

/-!
# Fitting-commutator generation from the complete FF alternatives

For the corrected, complete B.5.6 classification of the actual Thompson
representation, every branch gives [X,J(T_v)*] = X, where
X = [F(J(G_v)*),J(G_v)*]. All branches except a product of two symmetric-three
groups reduce to a Fitting subgroup of order dividing three.
The triple-cover centers and the nonsplit outer and hyperplane cases are
included. In particular no Fitting centrality or solvable exclusion is
assumed.

The double-S₃ branch retains an actual isomorphism and uses the Sylow and
normalization markings from `exists_starSylow_marking` to prove nontrivial
action on both cubic coordinates. This completes the structural generation
step. The source Fitting-center equality is assembled by the parent from
this identity and the independent solvable exclusion in 13.6.13.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.3/6, printed pp.104–110; paragraph after 13.6.13, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
variable {G : Type*} [Group G] [Finite G]

/-- Exhaust every corrected FF source alternative on the literal Thompson
image. Only the actual S₃ × S₃ group remains for the Sylow-marked argument. -/
theorem thompson_generation_or_doubleThree
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hclassification : FFAlternatives.ProjectiveLine.SourceAlternative
      (thompsonRepresentation z v hz)) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) ∨
      Nonempty (JGstar z v ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  cases hclassification with
  | trivial ht =>
    let := ht
    apply Or.inl
    apply thompson_generation_of_fitting_card_dvd_prime T z v hSyl (by decide : Nat.Prime 3)
    simp
  | quasisimple hq c =>
    exact Or.inl (thompson_generation_of_quasisimple T z v hz hSyl hq c)
  | symmetricThree c =>
    exact Or.inl (thompson_generation_of_symmetricThree T z v hz hSyl hcore c)
  | twoFactors c =>
    exact thompson_generation_or_doubleThree_of_product T z v hSyl hcore
      c.product.equiv.symm (c.firstCase.factorModel _) (c.secondCase.factorModel _)
  | outerSixThree c =>
    exact Or.inl (thompson_generation_of_outerSixThree T z v hz hSyl hcore c)
  | hyperplane c =>
    exact Or.inl (thompson_generation_of_hyperplane T z v hz hSyl hcore c)

/-- Every corrected FF classification alternative gives commutator generation
for the actual Thompson star image. The two-factor exception is discharged
using the genuine Sylow and normalization markings, with no extra structural
premise. -/
theorem thompson_generation
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hclassification : FFAlternatives.ProjectiveLine.SourceAlternative
      (thompsonRepresentation z v hz)) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) := by
  rcases thompson_generation_or_doubleThree T z v hz hSyl hcore hclassification with
    hgen | he
  · exact hgen
  · obtain ⟨e⟩ := he
    exact thompson_generation_of_doubleThree T z v hSyl hcore e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
