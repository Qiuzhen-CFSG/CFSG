module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Reduction

/-!
# The common 28-point geometry for four Rudvalis normalizers

The fixed point set of each of the first two relevant elementary subgroups,
and the union of the orbits of size at most two for the other two, is the same
explicit set of 28 points. The finite identifications are in `SmallOrbits`.
Normalizers preserve both constructions, so their upper bounds reduce to the
setwise stabilizer of this set. `smallOrbit` expresses that any three points
in an orbit include a repeated point, without assuming an enumeration of the
subgroup or its order.

Source: the fixed words of `LocalCover.Data`, the ATLAS representation and
max4 program preserved in this repository, and GLS3 Table 5.3r. This geometry
is an independently checked route to the local bounds used with [Asc86b] on
Aschbacher--Smith printed p.511, not a restatement of the book's conclusion.
-/

open scoped Pointwise
open Subgroup

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers

@[expose] public def smallOrbit {G X : Type*} [Group G] [MulAction G X]
    (E : Subgroup G) (x : X) : Prop :=
  ∀ a ∈ E, ∀ b ∈ E, a • x = x ∨ b • x = x ∨ a • x = b • x

public theorem smallOrbit_normalizer {G X : Type*} [Group G] [MulAction G X]
    (E : Subgroup G) (g : G) (hg : g ∈ normalizer (E : Set G)) (x : X)
    (hx : smallOrbit E x) : smallOrbit E (g • x) := by
  intro a ha b hb
  have ha' : g⁻¹ * a * g ∈ E := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hg) a).mp ha
  have hb' : g⁻¹ * b * g ∈ E := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hg) b).mp hb
  rcases hx _ ha' _ hb' with h | h | h
  · left
    have h' := congrArg (g • ·) h
    simpa only [mul_smul, smul_inv_smul] using h'
  · right; left
    have h' := congrArg (g • ·) h
    simpa only [mul_smul, smul_inv_smul] using h'
  · right; right
    have h' := congrArg (g • ·) h
    simpa only [mul_smul, smul_inv_smul] using h'

public theorem smallOrbit_of_pair {G X : Type*} [Group G] [MulAction G X]
    (E : Subgroup G) (x y : X)
    (h : E ≤ MulAction.stabilizer G ({x, y} : Set X)) : smallOrbit E x := by
  have hx : x ∈ ({x, y} : Set X) := by simp
  have images (a : G) (ha : a ∈ E) : a • x = x ∨ a • x = y := by
    have he := MulAction.mem_stabilizer_iff.mp (h ha)
    have hm : a • x ∈ a • ({x, y} : Set X) := Set.smul_mem_smul_set hx
    rw [he] at hm
    simpa using hm
  intro a ha b hb
  rcases images a ha with hax | hay
  · exact Or.inl hax
  rcases images b hb with hbx | hby
  · exact Or.inr (Or.inl hbx)
  · exact Or.inr (Or.inr (hay.trans hby.symm))

/-- The common point set, in zero-based numbering of the preserved model. -/
@[expose] public def points : List (Fin 4060) :=
  [74, 78, 125, 404, 417, 727, 739, 745, 774, 1022, 1152, 1182, 1385, 1439,
   1680, 1751, 2049, 2145, 2319, 2419, 2774, 2803, 3146, 3326, 3396, 3418, 3565, 3613]

@[expose] public def pointSet : Set (Fin 4060) := {x | x ∈ points}

public instance (x : Fin 4060) : Decidable (x ∈ pointSet) :=
  inferInstanceAs (Decidable (x ∈ points))

/-- Setwise stabilizer inside the original Rudvalis carrier. -/
@[expose] public def pointSetStabilizer : Subgroup Model :=
  MulAction.stabilizer Model pointSet

public theorem mem_pointSetStabilizer (g : Model) :
    g ∈ pointSetStabilizer ↔ ∀ x : Fin 4060, g • x ∈ pointSet ↔ x ∈ pointSet := by
  change g • pointSet = pointSet ↔ _
  constructor
  · intro h x
    simpa only [h] using
      (Set.smul_mem_smul_set_iff (a := g) (x := x) (s := pointSet))
  · intro h
    ext x
    obtain ⟨y, rfl⟩ := MulAction.surjective g x
    rw [Set.smul_mem_smul_set_iff, h]

/-- Normalizers preserve the union of the orbits of size at most two. -/
public theorem normalizer_le_pointSetStabilizer_of_smallOrbit (E : Subgroup Model)
    (h : ∀ x : Fin 4060, smallOrbit E x ↔ x ∈ pointSet) :
    normalizer (E : Set Model) ≤ pointSetStabilizer := by
  intro g hg
  apply (mem_pointSetStabilizer g).mpr
  intro x
  constructor
  · intro hx
    have hi := smallOrbit_normalizer E g⁻¹ (inv_mem hg) (g • x) ((h _).mpr hx)
    rw [inv_smul_smul] at hi
    exact (h _).mp hi
  · intro hx
    exact (h _).mp (smallOrbit_normalizer E g hg x ((h _).mpr hx))

/-- Normalizers preserve the common fixed point set. -/
public theorem normalizer_le_pointSetStabilizer_of_fixed (E : Subgroup Model)
    (h : ∀ x : Fin 4060, E ≤ MulAction.stabilizer Model x ↔ x ∈ pointSet) :
    normalizer (E : Set Model) ≤ pointSetStabilizer := by
  have forward (g : Model) (hg : g ∈ normalizer (E : Set Model))
      (x : Fin 4060) (hx : x ∈ pointSet) : g • x ∈ pointSet := by
    apply (h _).mp
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rw [mem_normalizer_iff_map_conj_eq] at hg
    rw [← hg]
    exact Subgroup.map_mono ((h x).mpr hx)
  intro g hg
  apply (mem_pointSetStabilizer g).mpr
  intro x
  constructor
  · intro hx
    simpa only [inv_smul_smul] using forward g⁻¹ (inv_mem hg) (g • x) hx
  · exact forward g hg x

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
