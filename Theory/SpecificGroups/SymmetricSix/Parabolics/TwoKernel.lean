module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.SolvableGeneration
public import Theory.GroupTheory.SolvableSylowOvergroupLifts

/-!
# The A₆ and S₆ parabolic intervals above a two-group kernel

The duad and syntheme stabilizers have relative index three over their
common Sylow two-subgroup. Their maximal-overgroup classification therefore
exhausts the entire Sylow interval. Conjugation transports this calculation
to any Sylow subgroup; subgroup correspondence lifts the pair through the
specified surjection with two-group kernel. The lifted parabolics are
solvable extensions, intersect in the original Sylow subgroup, and are the
only proper overgroups strictly containing it.

This supplies the two remaining quotient rows in the parabolic construction
of Aschbacher–Smith 13.4.10(7), printed p.909. All model subgroups and maps
are the literal six-letter permutation groups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricSix

private theorem prime_interval {Y : Type*} [Group Y]
    (B P U : Subgroup Y) (hi : Nat.Prime (B.relIndex P))
    (hBU : B ≤ U) (hUP : U ≤ P) : U = B ∨ U = P := by
  have hm := relIndex_mul_relIndex B U P hBU hUP
  have hd : B.relIndex U ∣ B.relIndex P := ⟨U.relIndex P, hm.symm⟩
  rcases (Nat.dvd_prime hi).mp hd with he | he
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp he) hBU)
  · rw [he] at hm
    have hUPi : U.relIndex P = 1 := by nlinarith [hi.pos]
    exact Or.inr (le_antisymm hUP (relIndex_eq_one.mp hUPi))

private theorem pair_interval {Y : Type*} [Group Y] [Finite Y]
    (B P Q : Subgroup Y)
    (hI : P ⊓ Q = B) (hiP : Nat.Prime (B.relIndex P))
    (hiQ : Nat.Prime (B.relIndex Q))
    (cover : ∀ U : Subgroup Y, IsCoatom U ∧ B ≤ U → U = P ∨ U = Q) :
    B < P ∧ B < Q ∧
      ∀ U : Subgroup Y, B ≤ U → U = B ∨ U = P ∨ U = Q ∨ U = ⊤ := by
  have hBP : B ≤ P := hI ▸ inf_le_left
  have hBQ : B ≤ Q := hI ▸ inf_le_right
  refine ⟨lt_of_le_of_ne hBP ?_, lt_of_le_of_ne hBQ ?_, ?_⟩
  · intro he
    exact hiP.ne_one (relIndex_eq_one.mpr he.ge)
  · intro he
    exact hiQ.ne_one (relIndex_eq_one.mpr he.ge)
  · intro U hBU
    by_cases hU : U = ⊤
    · exact Or.inr (Or.inr (Or.inr hU))
    obtain ⟨R, hR, hUR⟩ := (eq_top_or_exists_le_coatom U).resolve_left hU
    rcases cover R ⟨hR, hBU.trans hUR⟩ with he | he
    · rw [he] at hUR
      rcases prime_interval B P U hiP hBU hUR with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [he] at hUR
      rcases prime_interval B Q U hiQ hBU hUR with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))

private theorem lift_pair {X Y : Type*} [Group X] [Group Y] [Finite X]
    (S : Sylow 2 X) (f : X →* Y) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (P Q : Subgroup Y)
    (hP : IsCoatom P) (hQ : IsCoatom Q) (hne : P ≠ Q)
    (hI : P ⊓ Q = (S : Subgroup X).map f)
    (hSP : (S : Subgroup X).map f < P) (hSQ : (S : Subgroup X).map f < Q)
    (hsP : Group.IsSolvable P) (hsQ : Group.IsSolvable Q)
    (cover : ∀ U : Subgroup Y, (S : Subgroup X).map f ≤ U →
      U = (S : Subgroup X).map f ∨ U = P ∨ U = Q ∨ U = ⊤) :
    ∃ P Q : Subgroup X,
      IsCoatom P ∧ IsCoatom Q ∧ P ≠ Q ∧ P ⊓ Q = (S : Subgroup X) ∧
      (S : Subgroup X) < P ∧ (S : Subgroup X) < Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧
      ∀ U : Subgroup X, (S : Subgroup X) ≤ U →
        U = (S : Subgroup X) ∨ U = P ∨ U = Q ∨ U = ⊤ := by
  have hker : f.ker ≤ (S : Subgroup X) := hk.le_sylow_of_normal S
  have hS : ((S : Subgroup X).map f).comap f = (S : Subgroup X) :=
    comap_map_eq_self hker
  have strict {P : Subgroup Y} (h : (S : Subgroup X).map f < P) :
      (S : Subgroup X) < P.comap f := by
    refine lt_of_le_of_ne ((map_le_iff_le_comap).mp h.le) ?_
    intro he
    exact h.ne (by rw [he, map_comap_eq_self_of_surjective hf])
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  have solvable (P : Subgroup Y) (hs : Group.IsSolvable P) :
      Group.IsSolvable (P.comap f) := by
    apply (Group.isSolvable_map_iff_of_solvable_ker f (P.comap f)).mp
    rw [map_comap_eq_self_of_surjective hf]
    exact hs
  refine ⟨P.comap f, Q.comap f, isCoatom_comap_of_surjective hf hP,
    isCoatom_comap_of_surjective hf hQ, fun he => hne ((comap_injective hf) he),
    ?_, strict hSP, strict hSQ, solvable P hsP, solvable Q hsQ, ?_⟩
  · rw [← comap_inf, hI, hS]
  · intro U hSU
    have hUc : (U.map f).comap f = U := comap_map_eq_self (hker.trans hSU)
    rcases cover (U.map f) (map_mono hSU) with he | he | he | he
    · exact Or.inl (by rw [← hUc, he, hS])
    · exact Or.inr (Or.inl (by rw [← hUc, he]))
    · exact Or.inr (Or.inr (Or.inl (by rw [← hUc, he])))
    · exact Or.inr (Or.inr (Or.inr (by rw [← hUc, he, comap_top])))

/-- Lift the complete S₆ Sylow interval through the given two-group kernel. -/
theorem symmetric_two_kernel_parabolics {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (f : X →* S6) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    ∃ P Q : Subgroup X,
      IsCoatom P ∧ IsCoatom Q ∧ P ≠ Q ∧ P ⊓ Q = (S : Subgroup X) ∧
      (S : Subgroup X) < P ∧ (S : Subgroup X) < Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧
      ∀ U : Subgroup X, (S : Subgroup X) ≤ U →
        U = (S : Subgroup X) ∨ U = P ∨ U = Q ∨ U = ⊤ := by
  let S' := S.mapSurjective hf
  obtain ⟨g, hg, cover⟩ := coatoms_over_sylow S'
  let e := (MulAut.conj g).mapSubgroup
  have hI : e duadStabilizer ⊓ e synthemeStabilizer = (S' : Subgroup S6) := by
    rw [← e.map_inf, parabolics_inf]
    exact hg
  have hP := (e.isCoatom_iff _).mpr duadStabilizer_isCoatom
  have hQ := (e.isCoatom_iff _).mpr synthemeStabilizer_isCoatom
  have indices (P : Subgroup S6) (hi : borel.relIndex P = 3) :
      Nat.Prime ((S' : Subgroup S6).relIndex (e P)) := by
    rw [← hg]
    change Nat.Prime ((borel.map (MulAut.conj g).toMonoidHom).relIndex
      (P.map (MulAut.conj g).toMonoidHom))
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hi]
    decide
  have hi := pair_interval _ _ _ hI (indices _ borel_relIndex_duad)
    (indices _ borel_relIndex_syntheme) (fun U hU => (cover U).mp hU)
  exact lift_pair S f hf hk _ _ hP hQ
    (fun he => parabolics_ne (e.injective he)) hI hi.1 hi.2.1
    (Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _))
    (Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _))
    hi.2.2

/-- Lift the complete A₆ Sylow interval through the given two-group kernel. -/
theorem alternating_two_kernel_parabolics {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (f : X →* A6) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    ∃ P Q : Subgroup X,
      IsCoatom P ∧ IsCoatom Q ∧ P ≠ Q ∧ P ⊓ Q = (S : Subgroup X) ∧
      (S : Subgroup X) < P ∧ (S : Subgroup X) < Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧
      ∀ U : Subgroup X, (S : Subgroup X) ≤ U →
        U = (S : Subgroup X) ∨ U = P ∨ U = Q ∨ U = ⊤ := by
  let S' := S.mapSurjective hf
  obtain ⟨g, hg, cover⟩ := a6_coatoms_over_sylow S'
  let e := (MulAut.conj g).mapSubgroup
  have hI : e a6DuadStabilizer ⊓ e a6SynthemeStabilizer = (S' : Subgroup A6) := by
    rw [← e.map_inf, a6_parabolics_inf]
    exact hg
  have hP := (e.isCoatom_iff _).mpr a6DuadStabilizer_isCoatom
  have hQ := (e.isCoatom_iff _).mpr a6SynthemeStabilizer_isCoatom
  have indices (P : Subgroup A6) (hi : a6Borel.relIndex P = 3) :
      Nat.Prime ((S' : Subgroup A6).relIndex (e P)) := by
    rw [← hg]
    change Nat.Prime ((a6Borel.map (MulAut.conj g).toMonoidHom).relIndex
      (P.map (MulAut.conj g).toMonoidHom))
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hi]
    decide
  have hi := pair_interval _ _ _ hI (indices _ a6Borel_relIndex_duad)
    (indices _ a6Borel_relIndex_syntheme) (fun U hU => (cover U).mp hU)
  exact lift_pair S f hf hk _ _ hP hQ
    (fun he => a6_parabolics_ne (e.injective he)) hI hi.1 hi.2.1
    (Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _))
    (Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _))
    hi.2.2

/-- Every proper strict Sylow overgroup in S6 has relative index three. -/
theorem symmetric_sylow_parabolic_index (S : Sylow 2 S6) (U : Subgroup S6)
    (hSU : (S : Subgroup S6) < U) (hU : U ≠ ⊤) :
    (S : Subgroup S6).relIndex U = 3 := by
  obtain ⟨g, hg, cover⟩ := coatoms_over_sylow S
  let e := (MulAut.conj g).mapSubgroup
  have index (P : Subgroup S6) (hi : borel.relIndex P = 3) :
      (S : Subgroup S6).relIndex (e P) = 3 := by
    rw [← hg]
    change (borel.map (MulAut.conj g).toMonoidHom).relIndex
      (P.map (MulAut.conj g).toMonoidHom) = 3
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hi]
  have hI : e duadStabilizer ⊓ e synthemeStabilizer = (S : Subgroup S6) := by
    rw [← e.map_inf, parabolics_inf]
    exact hg
  have hi := pair_interval _ _ _ hI
    (by rw [index _ borel_relIndex_duad]; decide)
    (by rw [index _ borel_relIndex_syntheme]; decide)
    (fun R hR => (cover R).mp hR)
  rcases hi.2.2 U hSU.le with he | he | he | he
  · exact (hSU.ne he.symm).elim
  · rw [he]
    exact index _ borel_relIndex_duad
  · rw [he]
    exact index _ borel_relIndex_syntheme
  · exact (hU he).elim

/-- Every proper strict Sylow overgroup in A6 has relative index three. -/
theorem alternating_sylow_parabolic_index (S : Sylow 2 A6) (U : Subgroup A6)
    (hSU : (S : Subgroup A6) < U) (hU : U ≠ ⊤) :
    (S : Subgroup A6).relIndex U = 3 := by
  obtain ⟨g, hg, cover⟩ := a6_coatoms_over_sylow S
  let e := (MulAut.conj g).mapSubgroup
  have index (P : Subgroup A6) (hi : a6Borel.relIndex P = 3) :
      (S : Subgroup A6).relIndex (e P) = 3 := by
    rw [← hg]
    change (a6Borel.map (MulAut.conj g).toMonoidHom).relIndex
      (P.map (MulAut.conj g).toMonoidHom) = 3
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hi]
  have hI : e a6DuadStabilizer ⊓ e a6SynthemeStabilizer = (S : Subgroup A6) := by
    rw [← e.map_inf, a6_parabolics_inf]
    exact hg
  have hi := pair_interval _ _ _ hI
    (by rw [index _ a6Borel_relIndex_duad]; decide)
    (by rw [index _ a6Borel_relIndex_syntheme]; decide)
    (fun R hR => (cover R).mp hR)
  rcases hi.2.2 U hSU.le with he | he | he | he
  · exact (hSU.ne he.symm).elim
  · rw [he]
    exact index _ a6Borel_relIndex_duad
  · rw [he]
    exact index _ a6Borel_relIndex_syntheme
  · exact (hU he).elim

end Theory.SpecificGroups.SymmetricSix
