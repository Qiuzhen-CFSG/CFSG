module
public import Theory.Representation.OrbitSizeSeparation
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.FieldTheory.Finiteness

/-!
# Orbit sizes in the binary natural A₅, A₇ and A₈ modules

Equal-weight binary words are related by a coordinate permutation. A
transposition fixing a repeated coordinate value corrects its sign, so
the same weight classes are alternating-group orbits. In degree seven
their cardinalities are 21, 35 and 7, checked on the 64 core vectors.
In degree five there are two nonzero weight classes. In degree eight,
passing through the literal constant-line quotient identifies weights
two and six, leaving two nonzero orbits. The two-orbit parity lemma
separates the latter cases without enumerating permutations.

The odd-degree comparison uses the existing core-to-natural isomorphism;
the even-degree proof retains the actual quotient projection.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §B.3
and the irreducible cases of 12.2.16, printed pp.799–800.
-/

public noncomputable section
namespace BinaryPermutation
open Representation
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def wordWeight (v : Full Ω) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

omit [DecidableEq Ω] in
theorem wordWeight_permute (g : Equiv.Perm Ω) (v : Full Ω) :
    wordWeight (representation Ω g v) = wordWeight v := by
  change (Finset.univ.filter (fun i => v (g.symm i) ≠ 0)).card =
    (Finset.univ.filter (fun i => v i ≠ 0)).card
  apply Finset.card_bij (fun i _ => g.symm i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, representation_apply] using hi
  · intro i _ j _ h
    exact g.symm.injective h
  · intro j hj
    refine ⟨g j, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      representation_apply, Equiv.symm_apply_apply] using hj

omit [DecidableEq Ω] in
theorem exists_permutation_of_weight (v w : Full Ω)
    (hw : wordWeight v = wordWeight w) :
    ∃ g : Equiv.Perm Ω, representation Ω g v = w := by
  have hc : Fintype.card {i : Ω // v i ≠ 0} = Fintype.card {i : Ω // w i ≠ 0} := by
    simpa only [Fintype.card_subtype, wordWeight] using hw
  let e := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, ?_⟩
  ext i
  change v (e.extendSubtype.symm i) = w i
  have hb : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  apply hb
  constructor
  · intro h
    by_contra h'
    have hn := e.extendSubtype_not_mem (e.extendSubtype.symm i) (by simpa using h)
    exact hn (by simpa using h')
  · intro h
    by_contra h'
    have hn := e.extendSubtype_mem (e.extendSubtype.symm i) h'
    exact hn (by simpa using h)

theorem exists_even_permutation_of_weight (hn : 3 ≤ Fintype.card Ω)
    (v w : Full Ω) (hw : wordWeight v = wordWeight w) :
    ∃ g : alternatingGroup Ω, representation Ω g.val v = w := by
  classical
  obtain ⟨g,hg⟩ := exists_permutation_of_weight v w hw
  by_cases he : g.sign = 1
  · exact ⟨⟨g,Equiv.Perm.mem_alternatingGroup.mpr he⟩,hg⟩
  have hni : ¬ Function.Injective v := by
    intro hi
    have hc := Fintype.card_le_of_injective v hi
    rw [ZMod.card] at hc
    omega
  obtain ⟨i,j,hij,hv⟩ := Function.not_injective_iff.mp hni
  have hs : representation Ω (Equiv.swap i j) v = v := by
    ext k
    change v ((Equiv.swap i j).symm k) = v k
    rw [Equiv.symm_swap]
    by_cases hki : k = i
    · subst k; simp [hij]
    by_cases hkj : k = j
    · subst k; simp [hij]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  refine ⟨⟨g * Equiv.swap i j, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap hv, (Int.units_eq_one_or g.sign).resolve_left he]
    decide
  · change representation Ω (g * Equiv.swap i j) v = w
    rw [map_mul,Module.End.mul_apply,hs,hg]

theorem even_core_orbit_eq_weight (hn : 3 ≤ Fintype.card Ω) (v : core Ω) :
    (Set.range fun g : alternatingGroup Ω => alternatingCoreRepresentation Ω g v) =
      {w : core Ω | wordWeight w.val = wordWeight v.val} := by
  ext w
  constructor
  · rintro ⟨g,rfl⟩
    exact wordWeight_permute g.val v.val
  · intro hw
    obtain ⟨g,hg⟩ := exists_even_permutation_of_weight hn v.val w.val hw.symm
    exact ⟨g,Subtype.ext hg⟩

section Seven
local instance : DecidablePred (· ∈ core (Fin 7)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 7)) := Subtype.fintype _

private theorem seven_weights (v : core (Fin 7)) :
    wordWeight v.val = 0 ∨ wordWeight v.val = 2 ∨
    wordWeight v.val = 4 ∨ wordWeight v.val = 6 := by
  revert v
  decide +kernel

private theorem seven_counts :
    (Finset.univ.filter fun v : core (Fin 7) => wordWeight v.val = 0).card = 1 ∧
    (Finset.univ.filter fun v : core (Fin 7) => wordWeight v.val = 2).card = 21 ∧
    (Finset.univ.filter fun v : core (Fin 7) => wordWeight v.val = 4).card = 35 ∧
    (Finset.univ.filter fun v : core (Fin 7) => wordWeight v.val = 6).card = 7 := by
  decide +kernel

theorem seven_core_orbitCardSeparates :
    OrbitCardSeparates (alternatingCoreRepresentation (Fin 7)) := by
  intro v w _ _ hc
  rw [even_core_orbit_eq_weight (by decide),even_core_orbit_eq_weight (by decide)] at hc
  have hcount (x : core (Fin 7)) :
      {z : core (Fin 7) | wordWeight z.val = wordWeight x.val}.ncard =
        (Finset.univ.filter fun z : core (Fin 7) =>
          wordWeight z.val = wordWeight x.val).card := by
    rw [show {z : core (Fin 7) | wordWeight z.val = wordWeight x.val} =
      ↑(Finset.univ.filter fun z : core (Fin 7) =>
        wordWeight z.val = wordWeight x.val) by ext; simp, Set.ncard_coe_finset]
  rw [hcount,hcount] at hc
  have hw : wordWeight v.val = wordWeight w.val := by
    rcases seven_weights v with hv | hv | hv | hv <;>
      rcases seven_weights w with hw | hw | hw | hw <;>
      rw [hv,hw] at hc ⊢
    all_goals first | rfl | (simp only [seven_counts.1,seven_counts.2.1,
      seven_counts.2.2.1,seven_counts.2.2.2] at hc; contradiction)
  obtain ⟨g,hg⟩ := exists_even_permutation_of_weight (by decide : 3 ≤ Fintype.card (Fin 7))
    v.val w.val hw
  exact ⟨g,Subtype.ext hg⟩
end Seven

theorem natural_orbitCardSeparates_of_core (hodd : Odd (Fintype.card Ω))
    (hc : OrbitCardSeparates (alternatingCoreRepresentation Ω)) :
    OrbitCardSeparates (alternatingNaturalRepresentation Ω) := by
  let e := coreEquivNatural Ω hodd
  apply hc.of_intertwining (MonoidHom.id _) Function.surjective_id e.symm
  intro g v
  apply e.injective
  change e (e.symm (naturalRepresentation Ω g.val v)) =
    e (coreRepresentation Ω g.val (e.symm v))
  rw [e.apply_symm_apply,coreEquivNatural_equivariant,e.apply_symm_apply]

theorem seven_natural_orbitCardSeparates :
    OrbitCardSeparates (alternatingNaturalRepresentation (Fin 7)) :=
  natural_orbitCardSeparates_of_core (by decide) seven_core_orbitCardSeparates

private def fiveTwo : core (Fin 5) := ⟨![1,1,0,0,0],by rw [mem_core]; decide⟩
private def fiveFour : core (Fin 5) := ⟨![1,1,1,1,0],by rw [mem_core]; decide⟩

theorem five_core_orbitCardSeparates :
    OrbitCardSeparates (alternatingCoreRepresentation (Fin 5)) := by
  refine OrbitCardSeparates.of_two_nonzero_orbits _ ?_
    fiveTwo fiveFour (by decide) (by decide) ?_
  · rw [Module.natCard_eq_pow_finrank (K := ZMod 2),finrank_core,Nat.card_zmod]
    decide
  · intro v hv
    have hh : ∀ x : Full (Fin 5), (∑ i, x i) = 0 → x ≠ 0 →
        wordWeight x = 2 ∨ wordWeight x = 4 := by decide +kernel
    rcases hh v.val v.property (fun he => hv (Subtype.ext he)) with h | h
    · obtain ⟨g,hg⟩ := exists_even_permutation_of_weight (by decide : 3 ≤ Fintype.card (Fin 5))
        fiveTwo.val v.val (by rw [h]; decide)
      exact Or.inl ⟨g,Subtype.ext hg⟩
    · obtain ⟨g,hg⟩ := exists_even_permutation_of_weight (by decide : 3 ≤ Fintype.card (Fin 5))
        fiveFour.val v.val (by rw [h]; decide)
      exact Or.inr ⟨g,Subtype.ext hg⟩

theorem five_natural_orbitCardSeparates :
    OrbitCardSeparates (alternatingNaturalRepresentation (Fin 5)) :=
  natural_orbitCardSeparates_of_core (by decide) five_core_orbitCardSeparates

private def eightTwo : core (Fin 8) := ⟨![1,1,0,0,0,0,0,0],by rw [mem_core]; decide⟩
private def eightFour : core (Fin 8) := ⟨![1,1,1,1,0,0,0,0],by rw [mem_core]; decide⟩
private def eightOne : core (Fin 8) := ⟨allOne (Fin 8),by rw [mem_core]; decide⟩

private theorem eight_quotient_zero (v : core (Fin 8)) :
    coreToNatural (Fin 8) v = 0 ↔ v.val = 0 ∨ v.val = allOne (Fin 8) := by
  rw [Subtype.ext_iff]
  change (constants (Fin 8)).mkQ v.val = 0 ↔ _
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,
    constants,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,hc⟩
    have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hb c with rfl | rfl
    · exact Or.inl (by simpa using hc.symm)
    · exact Or.inr (by simpa using hc.symm)
  · rintro (h | h)
    · exact ⟨0,by simpa using h.symm⟩
    · exact ⟨1,by simpa using h.symm⟩

theorem eight_natural_orbitCardSeparates :
    OrbitCardSeparates (alternatingNaturalRepresentation (Fin 8)) := by
  refine OrbitCardSeparates.of_two_nonzero_orbits _ ?_
    (coreToNatural (Fin 8) eightTwo) (coreToNatural (Fin 8) eightFour) ?_ ?_ ?_
  · rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_natural_even (Fin 8) (by decide),Nat.card_zmod]
    decide
  · rw [ne_eq,eight_quotient_zero]
    decide
  · rw [ne_eq,eight_quotient_zero]
    decide
  · intro v hv
    obtain ⟨w,rfl⟩ := coreToNatural_surjective v
    have hw := mt (eight_quotient_zero w).mpr hv
    have h0 : w.val ≠ 0 := fun h => hw (Or.inl h)
    have h1 : w.val ≠ allOne (Fin 8) := fun h => hw (Or.inr h)
    have hh : ∀ x : Full (Fin 8), (∑ i, x i) = 0 → x ≠ 0 →
        x ≠ allOne (Fin 8) → wordWeight x = 2 ∨ wordWeight x = 4 ∨
          wordWeight (x + allOne (Fin 8)) = 2 := by decide +kernel
    have transport (u z : core (Fin 8)) (he : wordWeight u.val = wordWeight z.val) :
        ∃ g : alternatingGroup (Fin 8),
          alternatingNaturalRepresentation (Fin 8) g (coreToNatural (Fin 8) u) =
            coreToNatural (Fin 8) z := by
      obtain ⟨g,hg⟩ := exists_even_permutation_of_weight
        (by decide : 3 ≤ Fintype.card (Fin 8)) u.val z.val he
      refine ⟨g,?_⟩
      change naturalRepresentation (Fin 8) g.val (coreToNatural (Fin 8) u) = _
      rw [← coreToNatural_equivariant]
      exact congrArg (coreToNatural (Fin 8)) (Subtype.ext hg)
    rcases hh w.val w.property h0 h1 with h | h | h
    · exact Or.inl (transport eightTwo w (by rw [h]; decide))
    · exact Or.inr (transport eightFour w (by rw [h]; decide))
    · have ht := transport eightTwo (w + eightOne) (by
        change wordWeight eightTwo.val = wordWeight (w.val + allOne (Fin 8))
        rw [h]; decide)
      have he : coreToNatural (Fin 8) (w + eightOne) = coreToNatural (Fin 8) w := by
        rw [map_add,show coreToNatural (Fin 8) eightOne = 0 from
          (eight_quotient_zero _).mpr (Or.inr rfl),add_zero]
      rw [he] at ht
      exact Or.inl ht

end BinaryPermutation
