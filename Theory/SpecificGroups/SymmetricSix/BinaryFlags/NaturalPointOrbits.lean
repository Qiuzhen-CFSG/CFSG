module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransverseInvolution

/-!
# The two orbits of a natural six-letter point stabilizer

The nonzero vectors of the actual binary augmentation quotient are duads.
The stabilizer of {4,5} has six other orthogonal points and eight
nonorthogonal points. Explicit even movers establish both orbits; the
invariant descended pairing transports the result to an arbitrary point.
The certificates check only the fifteen duads, not all ambient permutations.

`SourceCompletion.CaseOne.NaturalConjugates` lifts these movers through the
original marked A₆ quotient. Its source application transports endpoint
commutation to the whole orthogonal orbit and selects the nonorthogonal
conjugator used in the nonabelian-span argument.
Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966.
-/

public section
open BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPointOrbits
open NaturalGeometry NaturalPairing

private def disjointMover (d : NaturalGeometry.Duad) : Equiv.Perm (Fin 6) :=
  let g := Equiv.swap ((Equiv.swap 0 d.val.1) 1) d.val.2 * Equiv.swap 0 d.val.1
  if g ∈ alternatingGroup (Fin 6) then g else g * Equiv.swap 4 5

private def crossingMover (d : NaturalGeometry.Duad) : Equiv.Perm (Fin 6) :=
  let g := Equiv.swap 0 d.val.1 * Equiv.swap 5 d.val.2
  if g ∈ alternatingGroup (Fin 6) then g else g * Equiv.swap 1 2

private theorem disjointMover_spec : ∀ d : NaturalGeometry.Duad, d.val.2 < 4 →
    disjointMover d ∈ alternatingGroup (Fin 6) ∧
    pair (disjointMover d 4) (disjointMover d 5) = pair 4 5 ∧
    disjointMover d 0 = d.val.1 ∧ disjointMover d 1 = d.val.2 := by decide +kernel

private theorem crossingMover_spec : ∀ d : NaturalGeometry.Duad, d.val.1 < 4 → 4 ≤ d.val.2 →
    crossingMover d ∈ alternatingGroup (Fin 6) ∧
    pair (crossingMover d 4) (crossingMover d 5) = pair 4 5 ∧
    crossingMover d 0 = d.val.1 ∧ crossingMover d 5 = d.val.2 := by decide +kernel

private theorem pair_form (i j : Fin 6) :
    form (pairVector 4 5) (pairVector i j) =
      (if i = 4 then 1 else 0) + (if j = 4 then 1 else 0) +
      ((if i = 5 then 1 else 0) + (if j = 5 then 1 else 0)) := by
  let a : core (Fin 6) := ⟨Pi.single 4 1 + Pi.single 5 1, by
    simp [mem_core, Finset.sum_add_distrib]; decide⟩
  let b : core (Fin 6) := ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib]; decide⟩
  change naturalPairing (Fin 6) (coreToNatural (Fin 6) a) (coreToNatural (Fin 6) b) = _
  rw [naturalPairing_apply_core]
  dsimp [a, b]
  fin_cases i <;> fin_cases j <;> decide

private theorem duad_pairing (d : NaturalGeometry.Duad) :
    form (pairVector 4 5) (duadVector d) = if d.val.1 < 4 ∧ 4 ≤ d.val.2 then 1 else 0 := by
  rw [duadVector, pair_form]
  revert d
  decide

private theorem duad_cases : ∀ d : NaturalGeometry.Duad,
    d.val.2 < 4 ∨ (d.val.1 < 4 ∧ 4 ≤ d.val.2) ∨ d = ⟨(4, 5), by decide⟩ := by decide

private theorem based_orbit (v : natural (Fin 6)) (hv : v ≠ 0)
    (hne : v ≠ pairVector 4 5) :
    ∃ g : alternatingGroup (Fin 6),
      naturalRepresentation (Fin 6) g.val (pairVector 4 5) = pairVector 4 5 ∧
      naturalRepresentation (Fin 6) g.val
        (if form (pairVector 4 5) v = 0 then pairVector 0 1 else pairVector 0 5) = v := by
  obtain ⟨d, rfl⟩ := (vector_cases v).resolve_left hv
  rcases duad_cases d with hd | hd | rfl
  · obtain ⟨he, hf, h0, h1⟩ := disjointMover_spec d hd
    have hpair : form (pairVector 4 5) (duadVector d) = 0 := by
      rw [duad_pairing, if_neg (fun hh => (not_le_of_gt hd) hh.2)]
    refine ⟨⟨disjointMover d, he⟩, ?_, ?_⟩
    · rw [pairVector_map]
      exact (pairVector_eq_iff ((disjointMover d).injective.ne (by decide)) (by decide)).mpr hf
    · rw [hpair, if_pos rfl, pairVector_map, h0, h1]
      rfl
  · obtain ⟨he, hf, h0, h5⟩ := crossingMover_spec d hd.1 hd.2
    have hpair : form (pairVector 4 5) (duadVector d) = 1 := by rw [duad_pairing, if_pos hd]
    refine ⟨⟨crossingMover d, he⟩, ?_, ?_⟩
    · rw [pairVector_map]
      exact (pairVector_eq_iff ((crossingMover d).injective.ne (by decide)) (by decide)).mpr hf
    · rw [hpair, if_neg one_ne_zero, pairVector_map, h0, h5]
      rfl
  · exact (hne rfl).elim

/-- The stabilizer of a natural point is transitive on each of its two other
orbits: the distinct orthogonal points and the nonorthogonal points. -/
theorem stabilizer_transitive (z v w : natural (Fin 6)) (hz : z ≠ 0)
    (hv : v ≠ 0) (hw : w ≠ 0) (hvz : v ≠ z) (hwz : w ≠ z)
    (hp : form z v = form z w) :
    ∃ a : alternatingGroup (Fin 6),
      naturalRepresentation (Fin 6) a.val z = z ∧
      naturalRepresentation (Fin 6) a.val v = w := by
  obtain ⟨g, hg⟩ := NaturalTransport.exists_even_image z hz
  let ρ := naturalRepresentation (Fin 6)
  let v' := ρ g.val⁻¹ v
  let w' := ρ g.val⁻¹ w
  have hcancel (x : natural (Fin 6)) : ρ g.val (ρ g.val⁻¹ x) = x := by
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hv' : v' ≠ 0 := by intro he; have := hcancel v; rw [show ρ g.val⁻¹ v = 0 from he, map_zero] at this; exact hv this.symm
  have hw' : w' ≠ 0 := by intro he; have := hcancel w; rw [show ρ g.val⁻¹ w = 0 from he, map_zero] at this; exact hw this.symm
  have hvz' : v' ≠ pairVector 4 5 := by intro he; exact hvz ((hcancel v).symm.trans ((congrArg (ρ g.val) he).trans hg))
  have hwz' : w' ≠ pairVector 4 5 := by intro he; exact hwz ((hcancel w).symm.trans ((congrArg (ρ g.val) he).trans hg))
  have hp' : form (pairVector 4 5) v' = form (pairVector 4 5) w' := by
    rw [← form_invariant g.val (pairVector 4 5) v',
      ← form_invariant g.val (pairVector 4 5) w', hg]
    exact (congrArg (fun x => form z x) (hcancel v)).trans
      (hp.trans (congrArg (fun x => form z x) (hcancel w)).symm)
  obtain ⟨a, ha, hav⟩ := based_orbit v' hv' hvz'
  obtain ⟨b, hb, hbw⟩ := based_orbit w' hw' hwz'
  rw [← hp'] at hbw
  let c := b * a⁻¹
  have hc : ρ c.val (pairVector 4 5) = pairVector 4 5 := by
    have hi : ρ a.val⁻¹ (pairVector 4 5) = pairVector 4 5 := by
      have he := congrArg (ρ a.val⁻¹) ha
      change ρ a.val⁻¹ (ρ a.val (pairVector 4 5)) = ρ a.val⁻¹ (pairVector 4 5) at he
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at he
      exact he.symm
    change ρ (b.val * a.val⁻¹) (pairVector 4 5) = _
    rw [map_mul, Module.End.mul_apply, hi]
    exact hb
  have hvw : ρ c.val v' = w' := by
    rw [← hav]
    change ρ (b.val * a.val⁻¹) (ρ a.val _) = _
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    exact hbw
  refine ⟨g * c * g⁻¹, ?_, ?_⟩
  · rw [← hg]
    change ρ (g.val * c.val * g.val⁻¹) (ρ g.val (pairVector 4 5)) = _
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul,
      Module.End.mul_apply, hc]
  · change ρ (g.val * c.val * g.val⁻¹) v = w
    rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply]
    change ρ g.val (ρ c.val v') = w
    rw [hvw]
    exact hcancel w

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPointOrbits
