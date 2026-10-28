module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.Spectral

/-!
# Short-vector chains for a polynomial Leech cubic

A chain consists of orthogonal minimal Leech vectors and their prescribed
pairings with their cubic images. The polynomial determines the reverse
cross-pairings and the diagonal orbit angles. Thus one short-vector neighbor
constructs the initial two-orbit chain, and a further vector with specified
pairings appends one orbit.

These are algebraic constructions on the literal integral Leech lattice.
`CubicSeedExists` and `CubicChainExtension` state the still-unproved geometric
existence obligations; the latter requests only lengths two and three.
Their consumer is `stableE8RootsExist_of_chain_geometry` in
`InvariantRoots.lean`, in the same `TraceEightWitness` namespace.

Source context: Aschbacher, *Sporadic Groups* (1994), 25.1–25.9 and
Chapter 9 Exercise 6, p.141. That exercise starts with the cubic selected
in 25.9; it does not prove existence of these configurations for an
arbitrary polynomial cubic.
-/

open Atlas.Lattices Atlas.Codes
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness

@[expose] public noncomputable section

/-- Orthogonal minimal roots with the integral cross-pairings of a cubic orbit chain. -/
structure CubicRootChain (r : LeechIsometryGroup) (n : ℕ) where
  root : Fin n → leech
  orthogonal : ∀ i j, leechIntegralPairing (root i) (root j) =
    if i = j then 4 else 0
  mixed : ∀ i j, leechIntegralPairing (root i) (r.val (root j)) =
    if i = j then -2 else if i.val + 1 = j.val then -2
    else if j.val + 1 = i.val then 2 else 0

private theorem pairing_map (r : LeechIsometryGroup) (x y : leech) :
    leechIntegralPairing (r.val x) (r.val y) = leechIntegralPairing x y := by
  unfold leechIntegralPairing
  rw [r.prop]

private theorem orbit_diagonal {r : LeechIsometryGroup}
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0)
    {x : leech} (hx : integerDot x.val x.val = 32) :
    leechIntegralPairing x (r.val x) = -2 := by
  have h := cubic_orbit_pairing hp x
  have hmul := leechIntegralPairing_mul x (r.val x)
  omega

private theorem orbit_cross_sum {r : LeechIsometryGroup}
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) (x y : leech) :
    leechIntegralPairing (r.val x) y + leechIntegralPairing x y +
      leechIntegralPairing x (r.val y) = 0 := by
  have h := congrArg (fun z : leech => leechIntegralPairing z (r.val y)) (hp x)
  simpa only [leechIntegralPairing_add_left, pairing_map,
    show leechIntegralPairing 0 (r.val y) = 0 by simp [leechIntegralPairing, integerDot]]
    using h

namespace CubicRootChain
variable {r : LeechIsometryGroup}

/-- A single short neighbor of the initial orbit gives the two-orbit chain. -/
def ofNeighbor
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0)
    (x y : leech) (hx : integerDot x.val x.val = 32)
    (hy : integerDot y.val y.val = 32)
    (hxy : leechIntegralPairing x y = 0)
    (hrxy : leechIntegralPairing (r.val x) y = 2) : CubicRootChain r 2 where
  root := ![x, y]
  orthogonal := by
    have hxx : leechIntegralPairing x x = 4 := by
      have h := leechIntegralPairing_mul x x
      omega
    have hyy : leechIntegralPairing y y = 4 := by
      have h := leechIntegralPairing_mul y y
      omega
    have hyx : leechIntegralPairing y x = 0 := by
      rw [leechIntegralPairing_comm, hxy]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hxx, hyy, hxy, hyx]
  mixed := by
    have hxry : leechIntegralPairing x (r.val y) = -2 := by
      have h := orbit_cross_sum hp x y
      omega
    have hyrx : leechIntegralPairing y (r.val x) = 2 := by
      rw [leechIntegralPairing_comm, hrxy]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [orbit_diagonal hp hx, orbit_diagonal hp hy, hxry, hyrx]

theorem root_norm {n : ℕ} (c : CubicRootChain r n) (i : Fin n) :
    integerDot (c.root i).val (c.root i).val = 32 := by
  rw [← leechIntegralPairing_mul, c.orthogonal]
  simp

/-- Adjoin the next short vector; the polynomial supplies all reverse pairings. -/
def append {n : ℕ} (c : CubicRootChain r n)
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0)
    (y : leech) (hy : integerDot y.val y.val = 32)
    (horth : ∀ i, leechIntegralPairing (c.root i) y = 0)
    (hmixed : ∀ i, leechIntegralPairing (c.root i) (r.val y) =
      if i.val + 1 = n then -2 else 0) : CubicRootChain r (n + 1) where
  root := Fin.lastCases y c.root
  orthogonal := by
    have hyy : leechIntegralPairing y y = 4 := by
      have h := leechIntegralPairing_mul y y
      omega
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hyy]
      | cast j => simp [leechIntegralPairing_comm y, horth, ne_of_gt j.castSucc_lt_last]
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [horth]
      | cast j => simpa using c.orthogonal i j
  mixed := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [orbit_diagonal hp hy]
      | cast j =>
        have h := orbit_cross_sum hp (c.root j) y
        rw [horth, hmixed, leechIntegralPairing_comm (r.val (c.root j))] at h
        have hj : ¬ n + 1 = j.val := by omega
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc, ne_of_gt j.castSucc_lt_last,
          if_false, Fin.val_last, Fin.val_castSucc, hj]
        split_ifs at h ⊢ <;> omega
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        have hi : ¬ n + 1 = i.val := by omega
        simpa [hi] using hmixed i
      | cast j => simpa using c.mixed i j

end CubicRootChain

/-- The initial two-orbit configuration, to be constructed from short-vector geometry. -/
def CubicSeedExists : Prop :=
  ∀ r : LeechIsometryGroup, orderOf r = 3 →
    (∀ x : leech, r.val (r.val x) + r.val x + x = 0) →
    ∃ x y : leech, integerDot x.val x.val = 32 ∧
      integerDot y.val y.val = 32 ∧ leechIntegralPairing x y = 0 ∧
      leechIntegralPairing (r.val x) y = 2

/-- Only the two extension steps used to reach rank eight are requested. -/
def CubicChainExtension : Prop :=
  ∀ r : LeechIsometryGroup, orderOf r = 3 →
    (∀ x : leech, r.val (r.val x) + r.val x + x = 0) →
    ∀ n : ℕ, (n = 2 ∨ n = 3) → ∀ c : CubicRootChain r n,
    ∃ y : leech, integerDot y.val y.val = 32 ∧
      (∀ i, leechIntegralPairing (c.root i) y = 0) ∧
      ∀ i, leechIntegralPairing (c.root i) (r.val y) =
        if i.val + 1 = n then -2 else 0

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness
