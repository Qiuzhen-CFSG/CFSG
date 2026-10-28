module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Coordinates.Quotient
/-!
# The coordinate table is exactly the natural homology orbit

Checked transition tables prove closure of the 693 columns under the two actual
local generators. Their invertible homology actions and finiteness also give
inverse closure, hence closure under the generated local subgroup. In the other
direction, checked decreasing-height predecessor witnesses give a path from
coordinate 14 to every listed column. The resulting two inclusions identify the
literal localHomologyAction orbit, using the quotient equivalence from Quotient.

Source and ATLAS attribution: Tables.lean and ImageBound/source/README.md.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Coordinates
set_option maxRecDepth 10000

def nextVertex (b : Bool) (i : Vertex) : Vertex :=
  ⟨(if b then yNextIndex i else xNextIndex i) % 693, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 2000000 in
theorem next_check (b : Bool) : ∀ i : Vertex,
    combine (actionCols b) (code i) = code (nextVertex b i) := by
  cases b <;> apply allFin <;> decide +kernel

theorem action_vector (b : Bool) (i : Vertex) :
    actionMatrix b *ᵥ vector i = vector (nextVertex b i) := by
  change columns (actionCols b) *ᵥ decode (code i) = decode (code (nextVertex b i))
  rw [← decode_combine, next_check]

def predecessor (i : Vertex) : Vertex :=
  ⟨parentIndex i % 693, Nat.mod_lt _ (by decide)⟩

def step (i : Vertex) : Bool := choice i == 1

set_option maxHeartbeats 2000000 in
/-- Every nonroot vertex has an earlier predecessor under one of the two generators. -/
theorem reachability_check : ∀ i : Vertex, code i = 14 ∨
    (height (predecessor i) < height i ∧
      combine (actionCols (step i)) (code (predecessor i)) = code i) := by
  apply allFin
  decide +kernel

theorem seed_is_vertex : vectorOfCode 14 = vector (0 : Vertex) := by
  rfl

private def candidate : Set NaturalHomology := equiv ⁻¹' Set.range vector

private theorem action_injective (g : involutionCentralizer) :
    Function.Injective (fun v => (homologyAction g : Module.End (ZMod 2) NaturalHomology) v) := by
  intro v w he
  have hi := congrArg
    (fun z => (↑(homologyAction g)⁻¹ : Module.End (ZMod 2) NaturalHomology) z) he
  simpa only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] using hi

private theorem generator_preserves (b : Bool) : ∀ v : NaturalHomology,
    v ∈ candidate ↔
      (homologyAction (generator b).val : Module.End (ZMod 2) NaturalHomology) v ∈ candidate := by
  let f : NaturalHomology → NaturalHomology := fun v =>
    (homologyAction (generator b).val : Module.End (ZMod 2) NaturalHomology) v
  have hm : Set.MapsTo f candidate candidate := by
    rintro v ⟨i, hi⟩
    change equiv (f v) ∈ Set.range vector
    refine ⟨nextVertex b i, ?_⟩
    change vector (nextVertex b i) = equiv
      ((localHomologyAction (generator b) : Module.End (ZMod 2) NaturalHomology) v)
    rw [equiv_generator, ← hi, action_vector]
  have hf : Function.Injective f := action_injective (generator b).val
  have hs : Set.SurjOn f candidate candidate :=
    ((Set.toFinite candidate).injOn_iff_bijOn_of_mapsTo hm).mp hf.injOn |>.surjOn
  intro v
  refine ⟨fun hv => hm hv, ?_⟩
  intro hv
  obtain ⟨w, hw, he⟩ := hs hv
  exact hf he ▸ hw

private theorem local_preserves (g : localSubgroup) : ∀ v : NaturalHomology,
    v ∈ candidate ↔
      (localHomologyAction g : Module.End (ZMod 2) NaturalHomology) v ∈ candidate := by
  have h : ∀ (x : involutionCentralizer), x ∈ localSubgroup → ∀ v : NaturalHomology,
      v ∈ candidate ↔
        (homologyAction x : Module.End (ZMod 2) NaturalHomology) v ∈ candidate := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact generator_preserves false
      · have he := Set.mem_singleton_iff.mp hx
        subst x
        exact generator_preserves true
    | one => intro v; simp
    | mul g h _ _ hg hh =>
      intro v
      simpa only [map_mul, Units.val_mul, Module.End.mul_apply] using
        (hh v).trans (hg ((homologyAction h : Module.End (ZMod 2) NaturalHomology) v))
    | inv g _ hg =>
      intro v
      have he := hg ((↑(homologyAction g)⁻¹ : Module.End (ZMod 2) NaturalHomology) v)
      rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply] at he
      simpa only [map_inv] using he.symm
  exact h g.val g.property

theorem orbit_to_coordinates (v : NaturalHomology) (hv : v ∈ distinguishedOrbit) :
    equiv v ∈ Set.range vector := by
  obtain ⟨g, rfl⟩ := hv
  apply (local_preserves g distinguishedClass).mp
  exact ⟨0, seed_is_vertex.symm.trans equiv_seed.symm⟩

theorem vertex_in_orbit (i : Vertex) : equiv.symm (vector i) ∈ distinguishedOrbit := by
  have h : ∀ n : ℕ, ∀ i : Vertex, height i = n →
      equiv.symm (vector i) ∈ distinguishedOrbit := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin
      rcases reachability_check i with hi | ⟨hlt, he⟩
      · have hv : vector i = equiv distinguishedClass := by
          rw [vector, hi, equiv_seed]
        rw [hv, equiv.symm_apply_apply]
        exact distinguishedClass_mem_orbit
      · have hp := ih (height (predecessor i)) (hin ▸ hlt) (predecessor i) rfl
        have ha := (localHomologyAction_preserves_orbit (generator (step i)) _).mp hp
        have heq :
            (localHomologyAction (generator (step i)) : Module.End (ZMod 2) NaturalHomology)
              (equiv.symm (vector (predecessor i))) = equiv.symm (vector i) := by
          apply equiv.injective
          rw [equiv_generator, equiv.apply_symm_apply, equiv.apply_symm_apply]
          change columns (actionCols (step i)) *ᵥ decode (code (predecessor i)) = decode (code i)
          rw [← decode_combine, he]
        exact heq ▸ ha
  exact h (height i) i rfl

theorem coordinates_to_orbit (v : NaturalHomology) (hv : equiv v ∈ Set.range vector) :
    v ∈ distinguishedOrbit := by
  obtain ⟨i, hi⟩ := hv
  have h := vertex_in_orbit i
  rw [hi, equiv.symm_apply_apply] at h
  exact h

theorem isOrbitCoordinates : IsOrbitCoordinates equiv := by
  intro v
  exact ⟨orbit_to_coordinates v, coordinates_to_orbit v⟩
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Coordinates
