module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions

/-!
# Point orbits in the actual six-letter natural module and its cover

Duads embed equivariantly in the natural module and in the even-weight
permutation core. Every nonzero natural vector is a duad. In the full
five-dimensional core, the nonfixed vectors form two duad orbits: the
weight-two vectors and their complements. The remaining vectors are zero
and the fixed constant vector. Thus neither the full cover nor its constant
line is discarded in the terminal point-parabolic comparison.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, §B.3,
printed pp.83–85, and the terminal argument of 13.8.1, printed pp.968–969.
-/

public section
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

private def letters (d : Duad) : Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),
    (2,3),(2,4),(2,5),(3,4),(3,5),(4,5)] d

private theorem letters_ne : ∀ d, (letters d).1 ≠ (letters d).2 := by decide
private theorem letters_set : ∀ d, pair (letters d).1 (letters d).2 = duadSet d := by decide

noncomputable def naturalDuad (d : Duad) : natural (Fin 6) :=
  Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector (letters d).1 (letters d).2

theorem naturalDuad_injective : Function.Injective naturalDuad := by
  intro d e h
  apply duadSet_injective
  rw [← letters_set d, ← letters_set e]
  exact (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector_eq_iff (letters_ne d) (letters_ne e)).mp h

theorem naturalDuad_map (g : S6) (d : Duad) :
    naturalRepresentation (Fin 6) g (naturalDuad d) = naturalDuad (g • d) := by
  rw [naturalDuad, Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector_map]
  apply (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector_eq_iff (g.injective.ne (letters_ne d)) (letters_ne (g • d))).mpr
  rw [letters_set, duadSet_smul, ← letters_set d]
  simp [pair]

noncomputable def coverDuad (d : Duad) : core (Fin 6) :=
  ⟨Pi.single (letters d).1 1 + Pi.single (letters d).2 1, by
    simp [mem_core, Finset.sum_add_distrib]; decide⟩

private theorem pair_sum_eq {i j k l : Fin 6}
    (h : pair i j = pair k l) :
    (Pi.single i 1 + Pi.single j 1 : Full (Fin 6)) = Pi.single k 1 + Pi.single l 1 := by
  have hs : ({i,j} : Set (Fin 6)) = {k,l} := by
    simpa only [pair, Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun s : Finset (Fin 6) => (s : Set (Fin 6))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact add_comm _ _

theorem coverDuad_injective : Function.Injective coverDuad := by
  intro d e h
  apply naturalDuad_injective
  apply Subtype.ext
  exact congrArg (fun v : core (Fin 6) => (constants (Fin 6)).mkQ v.val) h

private theorem representation_single (g : S6) (i : Fin 6) :
    representation (Fin 6) g (Pi.single i (1 : ZMod 2)) = Pi.single (g i) 1 := by
  ext k
  simp only [representation_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem coverDuad_map (g : S6) (d : Duad) :
    coreRepresentation (Fin 6) g (coverDuad d) = coverDuad (g • d) := by
  apply Subtype.ext
  change representation (Fin 6) g
    (Pi.single (letters d).1 1 + Pi.single (letters d).2 1) = _
  rw [map_add, representation_single, representation_single]
  apply pair_sum_eq
  rw [letters_set, duadSet_smul, ← letters_set d]
  simp [pair]
def coverOne : core (Fin 6) := ⟨allOne (Fin 6), by change augmentation (Fin 6) _ = 0; rw [augmentation_allOne]; rfl⟩

theorem coverOne_map (g : S6) : coreRepresentation (Fin 6) g coverOne = coverOne := by
  apply Subtype.ext
  exact permute_allOne (Fin 6) g

set_option maxRecDepth 4096 in
theorem cover_cases : ∀ v : core (Fin 6),
    v = 0 ∨ v = coverOne ∨ ∃ d, v = coverDuad d ∨ v = coverOne + coverDuad d := by
  have hc : ∀ v : Full (Fin 6), (∑ i, v i) = 0 →
      v = 0 ∨ v = allOne (Fin 6) ∨
        ∃ d, v = (coverDuad d).val ∨ v = allOne (Fin 6) + (coverDuad d).val := by
    decide +kernel
  intro v
  rcases hc v.val v.property with h | h | ⟨d, h | h⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr ⟨d, Or.inl (Subtype.ext h)⟩)
  · exact Or.inr (Or.inr ⟨d, Or.inr (Subtype.ext h)⟩)

/-- The nonzero natural vectors are exactly the fifteen duad vectors. -/
theorem natural_cases (v : natural (Fin 6)) (hv : v ≠ 0) :
    ∃ d, naturalDuad d = v := by
  rcases NaturalGeometry.vector_cases v with h | ⟨d, rfl⟩
  · exact (hv h).elim
  · obtain ⟨e, he⟩ := duadSet_complete (pair d.val.1 d.val.2) (by
      simp [pair, ne_of_lt d.property])
    refine ⟨e, ?_⟩
    apply (NaturalGeometry.pairVector_eq_iff (letters_ne e) (ne_of_lt d.property)).mpr
    exact (letters_set e).trans he

/-- Translation by the invariant vector gives the second duad orbit. -/
@[expose] noncomputable def complementaryDuad (d : Duad) : core (Fin 6) := coverOne + coverDuad d

theorem complementaryDuad_injective : Function.Injective complementaryDuad := by
  intro d e h
  exact coverDuad_injective (add_left_cancel h)

theorem complementaryDuad_map (g : S6) (d : Duad) :
    coreRepresentation (Fin 6) g (complementaryDuad d) = complementaryDuad (g • d) := by
  rw [complementaryDuad, map_add, coverOne_map, coverDuad_map]
  rfl

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
