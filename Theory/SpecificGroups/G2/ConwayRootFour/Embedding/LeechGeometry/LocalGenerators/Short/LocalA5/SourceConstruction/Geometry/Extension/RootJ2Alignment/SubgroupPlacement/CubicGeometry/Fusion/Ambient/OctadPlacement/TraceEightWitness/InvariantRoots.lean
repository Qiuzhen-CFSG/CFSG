module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.EightRoots
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.OrbitChain
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ShortSeed

/-!
# E₈ roots from four cubic orbits

Four orthogonal minimal vectors with the chain cross-pairings give eight
integral Leech vectors: the four roots and their cubic images. The explicit
integral change of basis below has Gram matrix twice the Bourbaki E₈
Cartan matrix. Its integral inverse recovers all eight orbit vectors.
The polynomial identity therefore makes the entire root lattice invariant.

The short-vector seed and the two chain-extension steps are proved in the
imported geometry modules. Applying them successively constructs the four
orbits, so the final theorem proves `StableE8RootsExist` without additional
premises. The conditional assembly remains available separately.

Source context: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5,
pp.132–134, for the rank-eight octad lattice. The change of basis here is
an explicit lattice calculation, not an appeal to the converse of
Chapter 9 Exercise 6 or to the conjugacy assertions of 49.1–49.4.
-/

open Atlas.Lattices Atlas.Codes
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness

@[expose] public noncomputable section

private theorem pairing_map (r : LeechIsometryGroup) (x y : leech) :
    leechIntegralPairing (r.val x) (r.val y) = leechIntegralPairing x y := by
  unfold leechIntegralPairing
  rw [r.prop]

private theorem pairing_sub_left (x y z : leech) :
    leechIntegralPairing (x - y) z = leechIntegralPairing x z -
      leechIntegralPairing y z := by
  have h := leechIntegralPairing_add_left (x-y) y z
  rw [sub_add_cancel] at h
  omega

private theorem pairing_sub_right (x y z : leech) :
    leechIntegralPairing x (y - z) = leechIntegralPairing x y -
      leechIntegralPairing x z := by
  rw [leechIntegralPairing_comm, pairing_sub_left,
    leechIntegralPairing_comm y x, leechIntegralPairing_comm z x]

namespace CubicRootChain
variable {r : LeechIsometryGroup} (c : CubicRootChain r 4)

private theorem mixed_left (i j : Fin 4) :
    leechIntegralPairing (r.val (c.root i)) (c.root j) =
    if j = i then -2 else if j.val + 1 = i.val then -2
    else if i.val + 1 = j.val then 2 else 0 := by
  rw [leechIntegralPairing_comm, c.mixed]

/-- The eight simple roots in the required Bourbaki numbering. -/
def e8Root : Fin 8 → leech :=
  ![r.val (c.root 1),
    r.val (c.root 3),
    c.root 2 - c.root 3 - r.val (c.root 1) + r.val (c.root 2),
    c.root 3 - r.val (c.root 2),
    r.val (c.root 2),
    c.root 1 - c.root 2 - c.root 3 - r.val (c.root 0) +
      r.val (c.root 1) - r.val (c.root 3),
    r.val (c.root 0),
    c.root 0 - c.root 1 - c.root 1 - c.root 2 + c.root 3 +
      r.val (c.root 0) - r.val (c.root 2) - r.val (c.root 2)]

theorem e8Root_gram (i j : Fin 8) :
    leechIntegralPairing (c.e8Root i) (c.e8Root j) = 2 * e8Gram i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [e8Root, e8Gram, leechIntegralPairing_add_left,
      leechIntegralPairing_add_right, pairing_sub_left, pairing_sub_right,
      pairing_map, c.orthogonal, c.mixed, c.mixed_left, Fin.ext_iff]

/-- A concrete scaled E₈ root configuration in the original Leech lattice. -/
def toE8Roots : E8Roots := ⟨c.e8Root, c.e8Root_gram⟩

/-- The four starting vectors followed by their cubic images. -/
def orbit : Fin 8 → leech :=
  ![c.root 0, c.root 1, c.root 2, c.root 3,
    r.val (c.root 0), r.val (c.root 1), r.val (c.root 2), r.val (c.root 3)]

private def inverseCoefficients : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1,2,3,4,3,2,1,1; 0,1,1,2,1,1,1,0; 1,0,1,1,0,0,0,0;
    0,0,0,1,1,0,0,0; 0,0,0,0,0,0,1,0; 1,0,0,0,0,0,0,0;
    0,0,0,0,1,0,0,0; 0,1,0,0,0,0,0,0]

private theorem orbit_recover (i : Fin 8) :
    ∑ j, inverseCoefficients i j • c.e8Root j = c.orbit i := by
  fin_cases i <;> simp [inverseCoefficients, e8Root, orbit, Fin.sum_univ_succ] <;> abel

/-- The integral inverse change of basis recovers every orbit vector. -/
theorem orbit_mem_root_span (i : Fin 8) :
    c.orbit i ∈ Submodule.span ℤ (Set.range c.e8Root) := by
  rw [← c.orbit_recover i]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The cubic preserves the integral lattice generated by the eight roots. -/
theorem root_action
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) (j : Fin 8) :
    r.val (c.e8Root j) ∈ Submodule.span ℤ (Set.range c.e8Root) := by
  let M := Submodule.span ℤ (Set.range c.e8Root)
  have h0 (i : Fin 4) : c.root i ∈ M := by
    fin_cases i
    all_goals first
      | exact c.orbit_mem_root_span 0
      | exact c.orbit_mem_root_span 1
      | exact c.orbit_mem_root_span 2
      | exact c.orbit_mem_root_span 3
  have h1 (i : Fin 4) : r.val (c.root i) ∈ M := by
    fin_cases i
    all_goals first
      | exact c.orbit_mem_root_span 4
      | exact c.orbit_mem_root_span 5
      | exact c.orbit_mem_root_span 6
      | exact c.orbit_mem_root_span 7
  have h2 (i : Fin 4) : r.val (r.val (c.root i)) ∈ M := by
    have he : r.val (r.val (c.root i)) = -c.root i - r.val (c.root i) :=
      eq_sub_iff_add_eq.mpr (eq_neg_of_add_eq_zero_left (hp (c.root i)))
    rw [he]
    exact M.sub_mem (M.neg_mem (h0 i)) (h1 i)
  change r.val (c.e8Root j) ∈ M
  fin_cases j <;> simp [e8Root]
  all_goals
    repeat first
      | exact h0 _
      | exact h1 _
      | exact h2 _
      | apply M.add_mem
      | apply M.sub_mem

/-- Apply the same integral action to the literal rational embedding. -/
theorem rational_root_action
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) (i : Fin 8) :
    rationalExtension r.val (c.toE8Roots.vector i) ∈ c.toE8Roots.span := by
  rw [E8Roots.vector, rationalExtension_agrees]
  exact c.toE8Roots.embedding_mem_span (c.root_action hp i)

end CubicRootChain

/-- The exact eight-root contract follows after discharging both short-vector obligations. -/
theorem stableE8RootsExist_of_chain_geometry
    (hseed : CubicSeedExists) (hextend : CubicChainExtension) : StableE8RootsExist := by
  intro r hr hp
  obtain ⟨x, y, hx, hy, hxy, hrxy⟩ := hseed r hr hp
  let c₂ := CubicRootChain.ofNeighbor hp x y hx hy hxy hrxy
  obtain ⟨y₃, hy₃, ho₃, hm₃⟩ := hextend r hr hp 2 (Or.inl rfl) c₂
  let c₃ := c₂.append hp y₃ hy₃ ho₃ hm₃
  obtain ⟨y₄, hy₄, ho₄, hm₄⟩ := hextend r hr hp 3 (Or.inr rfl) c₃
  let c₄ := c₃.append hp y₄ hy₄ ho₄ hm₄
  exact ⟨c₄.toE8Roots, c₄.rational_root_action hp⟩

/-- Every polynomial fixed-free Leech cubic preserves the rational span of
eight integral roots with Gram matrix twice the Bourbaki E₈ Cartan matrix. -/
theorem stableE8RootsExist : StableE8RootsExist :=
  stableE8RootsExist_of_chain_geometry cubicSeedExists cubicChainExtension

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness
