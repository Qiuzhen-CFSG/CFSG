module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.Normalization
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement
public import Theory.SpecificGroups.Triality.SolvableSylowControl
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry

/-!
# Solvable Sylow control for the five nonbinary rank-two families

The concrete linear, symplectic, G₂, triality and Ree root calculations
place each solvable Sylow overgroup in its actual Borel. This assembly
retains an arbitrary supplied Sylow and gives one common control interface.
It is consumed by the original inner p-subgroup case of A.3.15(5),
Aschbacher–Smith pp.50–51, and Proposition 1.3.4, pp.510–511.
-/
public noncomputable section


namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open ReeF4.Parabolics ReeF4.Parabolics.ThreeSylowContainment

/-- The original matrix PSL₃ carrier has solvable Sylow control for q > 2. -/
theorem linear_control {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) : SolvableSylowControl 2 PSL(3,F) :=
  Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le F hn hF

/-- The actual full symplectic carrier has solvable Sylow control for q > 2. -/
theorem symplectic_control {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) :
    SolvableSylowControl 2 (Matrix.symplecticGroup (Fin 2) F) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact Theory.SpecificGroups.SymplecticFour.solvable_overgroups_of_orthogonal_root_orbits hF hn
    (Theory.SpecificGroups.SymplecticFour.solvable_unipotent_point_orbit_orthogonal
      (by rw [hF]; exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)))

/-- The full split-octonion G₂ carrier has solvable Sylow control for q > 2. -/
theorem g2_control {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) : SolvableSylowControl 2 (Atlas.G2.Model F) := by
  apply SolvableSylowControl.of_standard Atlas.G2.LieParabolicSetup.sylow Atlas.G2.borel
  · exact Atlas.G2.SylowNormalizer.normalizer_unipotent
  · intro A hsol hU
    exact Atlas.G2.SolvableSylowPlacement.le_borel hF A hU hsol

/-- Genuine binary triality has solvable Sylow control for q > 2. -/
theorem triality_control (P : Triality.Standard.Parameters)
    (hp : P.prime = 2) (hq : 2 < P.q) :
    SolvableSylowControl 2 (Triality.Standard.Carrier P) :=
  Triality.Standard.SolvableSylowControl.control P hp hq

/-- The actual Ree carrier has solvable Sylow control over each nonbinary field. -/
theorem ree_control (m : ℕ) (hm : 1 ≤ m) :
    SolvableSylowControl 2 (ReeF4.Model m) := by
  apply SolvableSylowControl.of_standard (positiveSylow m)
    (normalizer (unipotent m : Set (ReeF4.Model m))) (congrArg (fun K : Subgroup (ReeF4.Model m) => normalizer (K : Set (ReeF4.Model m))) (positiveSylow_coe m))
  intro A hsol hU
  rw [positiveSylow_coe] at hU
  exact (le_borel_of_solvable hm A hsol hU).trans (borel_le_unipotent_normalizer m)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
