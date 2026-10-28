module

public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.GroupTheory.Nilpotent

/-!
# Solvable Sylow overgroups in the six-letter groups

The duad and syntheme parabolics generate A₆ and S₆. Each has a two-group
Borel subgroup of index three, so its coset action proves solvability.
Sylow conjugacy moves this generating pair over any specified Sylow two-subgroup.

A six-point action with solvable kernel and image containing A₆ therefore
lifts this pair to genuine solvable Sylow overgroups generating its whole
source group. Its image is A₆ or S₆, so both cases are retained. This is the
finite geometry used for the hexad subgroup in Aschbacher--Smith 13.8.21(2),
printed p.956 (PDF p.973).
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymmetricSix

private theorem borel_solvable : Group.IsSolvable borel := by
  let := borelSylow.isPGroup'.isNilpotent
  exact inferInstanceAs (Group.IsSolvable borelSylow)

private theorem a6_borel_solvable : Group.IsSolvable a6Borel := by
  let := a6BorelSylow.isPGroup'.isNilpotent
  exact inferInstanceAs (Group.IsSolvable a6BorelSylow)

private theorem duad_solvable : Group.IsSolvable duadStabilizer := by
  let := borel_solvable
  exact isSolvable_of_relIndex_le_four borel duadStabilizer
    (by rw [borel_relIndex_duad]; decide)
private theorem syntheme_solvable : Group.IsSolvable synthemeStabilizer := by
  let := borel_solvable
  exact isSolvable_of_relIndex_le_four borel synthemeStabilizer
    (by rw [borel_relIndex_syntheme]; decide)
private theorem a6_duad_solvable : Group.IsSolvable a6DuadStabilizer := by
  let := a6_borel_solvable
  exact isSolvable_of_relIndex_le_four a6Borel a6DuadStabilizer
    (by rw [a6Borel_relIndex_duad]; decide)
private theorem a6_syntheme_solvable : Group.IsSolvable a6SynthemeStabilizer := by
  let := a6_borel_solvable
  exact isSolvable_of_relIndex_le_four a6Borel a6SynthemeStabilizer
    (by rw [a6Borel_relIndex_syntheme]; decide)

private theorem solvable_map {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (H : Subgroup X) [Group.IsSolvable H] :
    Group.IsSolvable (H.map f) :=
  Group.isSolvable_of_surjective (f.subgroupMap_surjective H)

private theorem pair_of_conjugate {X : Type*} [Group X]
    (B Q R : Subgroup X) [Group.IsSolvable Q] [Group.IsSolvable R]
    (hBQ : B ≤ Q) (hBR : B ≤ R) (hgen : Q ⊔ R = ⊤)
    (P : Subgroup X) (g : X) (hg : (MulAut.conj g).mapSubgroup B = P) :
    ∃ U V : Subgroup X, P ≤ U ∧ P ≤ V ∧ Group.IsSolvable U ∧
      Group.IsSolvable V ∧ U ⊔ V = ⊤ := by
  refine ⟨Q.map (MulAut.conj g), R.map (MulAut.conj g), ?_, ?_,
    solvable_map _ Q, solvable_map _ R, ?_⟩
  · rw [← hg]; exact map_mono hBQ
  · rw [← hg]; exact map_mono hBR
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

/-- Two actual conjugate parabolics give a solvable generating pair over any S₆ Sylow. -/
theorem s6_solvable_pair (P : Sylow 2 S6) :
    ∃ U V : Subgroup S6, (P : Subgroup S6) ≤ U ∧ (P : Subgroup S6) ≤ V ∧
      Group.IsSolvable U ∧ Group.IsSolvable V ∧ U ⊔ V = ⊤ := by
  let := duad_solvable
  let := syntheme_solvable
  obtain ⟨g, hg, _⟩ := coatoms_over_sylow P
  exact pair_of_conjugate borel duadStabilizer synthemeStabilizer
    borel_le_duadStabilizer borel_le_synthemeStabilizer parabolics_sup P g hg

/-- The two A₆ parabolics give the corresponding solvable generating pair. -/
theorem a6_solvable_pair (P : Sylow 2 A6) :
    ∃ U V : Subgroup A6, (P : Subgroup A6) ≤ U ∧ (P : Subgroup A6) ≤ V ∧
      Group.IsSolvable U ∧ Group.IsSolvable V ∧ U ⊔ V = ⊤ := by
  let := a6_duad_solvable
  let := a6_syntheme_solvable
  obtain ⟨g, hg, _⟩ := a6_coatoms_over_sylow P
  exact pair_of_conjugate a6Borel a6DuadStabilizer a6SynthemeStabilizer
    a6Borel_le_duadStabilizer a6Borel_le_synthemeStabilizer a6_parabolics_sup P g hg


private theorem pull_pair {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (pairs : ∀ P : Sylow 2 Y, ∃ U V : Subgroup Y,
      (P : Subgroup Y) ≤ U ∧ (P : Subgroup Y) ≤ V ∧
      Group.IsSolvable U ∧ Group.IsSolvable V ∧ U ⊔ V = ⊤)
    (f : X →* Y) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (P : Sylow 2 X) :
    ∃ U V : Subgroup X, (P : Subgroup X) ≤ U ∧ (P : Subgroup X) ≤ V ∧
      Group.IsSolvable U ∧ Group.IsSolvable V ∧ U ⊔ V = ⊤ := by
  obtain ⟨U, V, hU, hV, hUs, hVs, hgen⟩ := pairs (P.mapSurjective hf)
  let := hUs
  let := hVs
  refine ⟨U.comap f, V.comap f, (map_le_iff_le_comap).mp hU,
    (map_le_iff_le_comap).mp hV, isSolvable_comap_of_solvable_ker f U,
    isSolvable_comap_of_solvable_ker f V, ?_⟩
  rw [comap_sup_eq f _ _ hf, hgen, comap_top]

/-- Lift both parabolics through a six-point action with solvable kernel. -/
theorem solvable_pair_of_six_action {X : Type*} [Group X] [Finite X]
    (f : X →* S6) [Group.IsSolvable f.ker]
    (hA : alternatingGroup (Fin 6) ≤ f.range) (P : Sylow 2 X) :
    ∃ U V : Subgroup X, (P : Subgroup X) ≤ U ∧ (P : Subgroup X) ≤ V ∧
      Group.IsSolvable U ∧ Group.IsSolvable V ∧ U ⊔ V = ⊤ := by
  have halt : f.range = alternatingGroup (Fin 6) ∨ f.range = ⊤ := by
    have hd : f.range.index ∣ 2 := (alternatingGroup.index_eq_two (α := Fin 6)) ▸ index_dvd_of_le hA
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact Or.inr (index_eq_one.mp h1)
    · left
      exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
  rcases halt with ha | hs
  · let g : X →* A6 := (MulEquiv.subgroupCongr ha).toMonoidHom.comp f.rangeRestrict
    have hg : Function.Surjective g := (MulEquiv.subgroupCongr ha).surjective.comp
      f.rangeRestrict_surjective
    have hk : g.ker = f.ker := by
      ext x
      change g x = 1 ↔ f x = 1
      exact Subtype.ext_iff
    let : Group.IsSolvable g.ker := hk ▸ inferInstance
    exact pull_pair a6_solvable_pair g hg P
  · exact pull_pair s6_solvable_pair f (MonoidHom.range_eq_top.mp hs) P


end Theory.SpecificGroups.SymmetricSix
