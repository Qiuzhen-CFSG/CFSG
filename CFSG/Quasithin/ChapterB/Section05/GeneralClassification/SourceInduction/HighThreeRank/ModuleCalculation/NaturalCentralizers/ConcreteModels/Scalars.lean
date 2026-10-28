module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer.Pairing
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Scalar commutants of the concrete binary permutation sections

A commuting map is determined on a weight-two vector. Its stabilizing double
transposition and three-cycles, together with the three-pair additive relation,
force its image to be a binary multiple of that vector. Double transitivity
and the pair-vector spanning formula propagate this scalar across the core.
The small coordinate checks range over only 64 or 128 binary vectors and are
checked by the kernel. In degree seven the core is the natural module; in
degree six the core retains its nonsplit fixed line.

Source: Aschbacher–Smith, B.5.7, printed p.106; natural modules as in B.3.1.
The degree-six natural scalar calculation is reused from the intrinsic
Chapter 13 pairing calculation.
-/

open BinaryPermutation
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
private def pair (i j : Ω) : core Ω :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
private theorem pair_map (g : Equiv.Perm Ω) (i j : Ω) :
    coreRepresentation Ω g (pair i j) = pair (g i) (g j) := by
  apply Subtype.ext
  change representation Ω g (Pi.single i 1 + Pi.single j 1) = _
  ext k
  simp [pair, representation_apply, Pi.single_apply, Equiv.symm_apply_eq]
private theorem scalar_of_pair (hn : 4 ≤ Fintype.card Ω)
    (f : Module.End (ZMod 2) (core Ω))
    (hf : ∀ g : alternatingGroup Ω, ∀ v,
      f (coreRepresentation Ω g v) = coreRepresentation Ω g (f v))
    {a b : Ω} (hab : a ≠ b) {c : ZMod 2} (hc : f (pair a b) = c • pair a b) :
    ∀ v, f v = c • v := by
  have hp (i j : Ω) : f (pair i j) = c • pair i j := by
    by_cases hij : i = j
    · subst j
      have hz : pair i i = 0 := Subtype.ext (by ext k; exact CharTwo.add_self_eq_zero _)
      simp only [hz, map_zero, smul_zero]
    have := alternatingGroup.isMultiplyPretransitive Ω
    have ht : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω 2 :=
      MulAction.isMultiplyPretransitive_of_le (n := Nat.card Ω - 2)
        (by simpa only [Nat.card_eq_fintype_card] using (show 2 ≤ Fintype.card Ω - 2 by omega))
        (Nat.sub_le _ _)
    obtain ⟨g, ha, hb⟩ := MulAction.is_two_pretransitive_iff.mp ht hab hij
    have he : coreRepresentation Ω g (pair a b) = pair i j := by
      rw [pair_map, show g.val a = i from ha, show g.val b = j from hb]
    rw [← he, hf, hc, map_smul]
  intro v
  have he : ∑ i, v.val i • pair i a = v := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ i, v.val i • (Pi.single i (1 : ZMod 2) + Pi.single a 1)) = v.val
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    rw [show ∑ i, v.val i = 0 from v.property, zero_smul, add_zero]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single v.val
  rw [← he, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hp, smul_comm]

private def s (k : ℕ) : Equiv.Perm (Fin (k+6)) := Equiv.swap 0 1 * Equiv.swap 2 3
private def t (k : ℕ) : Equiv.Perm (Fin (k+6)) := Equiv.swap 2 3 * Equiv.swap 2 4
private def r (k : ℕ) : Equiv.Perm (Fin (k+6)) := Equiv.swap 3 4 * Equiv.swap 3 5
private def g (k : ℕ) : Equiv.Perm (Fin (k+6)) := Equiv.swap 1 2 * Equiv.swap 3 4
private def h (k : ℕ) : Equiv.Perm (Fin (k+6)) := Equiv.swap 0 2 * Equiv.swap 0 1
private def t7 : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * Equiv.swap 4 6

private theorem six_certificate (x : Full (Fin 6))
    (hs : representation _ (s 0) x = x)
    (ht : representation _ (t 0) x = x)
    (hr : representation _ (r 0) x = x)
    (he : x + representation _ (g 0) x = representation _ (h 0) x) :
    x = 0 ∨ x = (pair (0 : Fin 6) 1).val := by
  have cert : ∀ x : Full (Fin 6),
      representation _ (s 0) x = x → representation _ (t 0) x = x →
      representation _ (r 0) x = x →
      x + representation _ (g 0) x = representation _ (h 0) x →
      x = 0 ∨ x = (pair (0 : Fin 6) 1).val := by decide +kernel
  exact cert x hs ht hr he

private theorem seven_certificate (x : Full (Fin 7))
    (hs : representation _ (s 1) x = x)
    (ht : representation _ (t 1) x = x)
    (hr : representation _ (r 1) x = x)
    (ht7 : representation _ t7 x = x)
    (he : x + representation _ (g 1) x = representation _ (h 1) x) :
    x = 0 ∨ x = (pair (0 : Fin 7) 1).val := by
  have cert : ∀ x : Full (Fin 7),
      representation _ (s 1) x = x → representation _ (t 1) x = x →
      representation _ (r 1) x = x → representation _ t7 x = x →
      x + representation _ (g 1) x = representation _ (h 1) x →
      x = 0 ∨ x = (pair (0 : Fin 7) 1).val := by decide +kernel
  exact cert x hs ht hr ht7 he

private theorem scalar_from_cert {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (f : Module.End (ZMod 2) (core (Fin n)))
    (hf : ∀ a : alternatingGroup (Fin n), ∀ v,
      f (coreRepresentation _ a v) = coreRepresentation _ a (f v))
    (hc : (f (pair 0 1)).val = 0 ∨ (f (pair 0 1)).val = (pair (0 : Fin n) 1).val) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  have hab : (0 : Fin n) ≠ 1 := by
    intro he
    have he' := congrArg Fin.val he
    change 0 = 1 % n at he'
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at he'
    omega
  rcases hc with hc | hc
  · exact ⟨0, scalar_of_pair (by simpa using hn) f hf hab (by simpa using Subtype.ext hc)⟩
  · exact ⟨1, scalar_of_pair (by simpa using hn) f hf hab (by simpa using Subtype.ext hc)⟩

private theorem six_even : s 0 ∈ alternatingGroup (Fin 6) ∧
    t 0 ∈ alternatingGroup (Fin 6) ∧ r 0 ∈ alternatingGroup (Fin 6) ∧
    g 0 ∈ alternatingGroup (Fin 6) ∧ h 0 ∈ alternatingGroup (Fin 6) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel
private theorem seven_even : s 1 ∈ alternatingGroup (Fin 7) ∧
    t 1 ∈ alternatingGroup (Fin 7) ∧ r 1 ∈ alternatingGroup (Fin 7) ∧
    g 1 ∈ alternatingGroup (Fin 7) ∧ h 1 ∈ alternatingGroup (Fin 7) ∧
    t7 ∈ alternatingGroup (Fin 7) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel
private theorem pair_relations (k : ℕ) (hk : k = 0 ∨ k = 1) :
    coreRepresentation _ (s k) (pair 0 1) = pair 0 1 ∧
    coreRepresentation _ (t k) (pair 0 1) = pair 0 1 ∧
    coreRepresentation _ (r k) (pair 0 1) = pair 0 1 ∧
    pair 0 1 + coreRepresentation _ (g k) (pair 0 1) =
      coreRepresentation _ (h k) (pair 0 1) := by
  rcases hk with rfl | rfl <;>
    repeat' constructor
  all_goals apply Subtype.ext; decide +kernel

/-- The nonsplit five-dimensional augmentation core has only scalar A₆ endomorphisms. -/
public theorem core_six_scalar (f : Module.End (ZMod 2) (core (Fin 6)))
    (hf : ∀ a : alternatingGroup (Fin 6), ∀ v,
      f (coreRepresentation _ a v) = coreRepresentation _ a (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  apply scalar_from_cert (by decide) f hf
  have rel := pair_relations 0 (Or.inl rfl)
  have fix (a : Equiv.Perm (Fin 6)) (ha : a ∈ alternatingGroup (Fin 6))
      (he : coreRepresentation _ a (pair 0 1) = pair 0 1) :
      representation _ a (f (pair 0 1)).val = (f (pair 0 1)).val := by
    exact congrArg Subtype.val ((hf ⟨a, ha⟩ (pair 0 1)).symm.trans (congrArg f he))
  apply six_certificate _ (fix _ six_even.1 rel.1)
    (fix _ six_even.2.1 rel.2.1) (fix _ six_even.2.2.1 rel.2.2.1)
  have he := congrArg f rel.2.2.2
  rw [map_add, hf ⟨g 0, six_even.2.2.2.1⟩, hf ⟨h 0, six_even.2.2.2.2⟩] at he
  exact congrArg Subtype.val he

/-- The seven-point augmentation core has only scalar A₇ endomorphisms. -/
public theorem core_seven_scalar (f : Module.End (ZMod 2) (core (Fin 7)))
    (hf : ∀ a : alternatingGroup (Fin 7), ∀ v,
      f (coreRepresentation _ a v) = coreRepresentation _ a (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  apply scalar_from_cert (by decide) f hf
  have rel := pair_relations 1 (Or.inr rfl)
  have fix (a : Equiv.Perm (Fin 7)) (ha : a ∈ alternatingGroup (Fin 7))
      (he : coreRepresentation _ a (pair 0 1) = pair 0 1) :
      representation _ a (f (pair 0 1)).val = (f (pair 0 1)).val := by
    exact congrArg Subtype.val ((hf ⟨a, ha⟩ (pair 0 1)).symm.trans (congrArg f he))
  apply seven_certificate _ (fix _ seven_even.1 rel.1)
    (fix _ seven_even.2.1 rel.2.1) (fix _ seven_even.2.2.1 rel.2.2.1)
    (fix _ seven_even.2.2.2.2.2 (Subtype.ext (by decide +kernel)))
  have he := congrArg f rel.2.2.2
  rw [map_add, hf ⟨g 1, seven_even.2.2.2.1⟩, hf ⟨h 1, seven_even.2.2.2.2.1⟩] at he
  exact congrArg Subtype.val he

/-- Scalar endomorphisms on the literal seven-point natural quotient action. -/
public theorem natural_seven_scalar (f : Module.End (ZMod 2) (natural (Fin 7)))
    (hf : ∀ a : alternatingGroup (Fin 7), ∀ v,
      f (naturalRepresentation _ a v) = naturalRepresentation _ a (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let e := coreEquivNatural (Fin 7) (by decide)
  let F := e.symm.toLinearMap.comp (f.comp e.toLinearMap)
  have he (a : Equiv.Perm (Fin 7)) (v : core (Fin 7)) :
      e (coreRepresentation _ a v) = naturalRepresentation _ a (e v) :=
    coreEquivNatural_equivariant _ _ a v
  obtain ⟨c, hc⟩ := core_seven_scalar F (by
    intro a v
    apply e.injective
    change e (e.symm (f (e (coreRepresentation _ a v)))) =
      e (coreRepresentation _ a (e.symm (f (e v))))
    rw [e.apply_symm_apply, he, hf, he, e.apply_symm_apply])
  refine ⟨c, fun v => ?_⟩
  obtain ⟨w, rfl⟩ := e.surjective v
  have hh := congrArg e (hc w)
  simpa only [F, LinearMap.comp_apply, LinearEquiv.coe_coe,
    e.apply_symm_apply, map_smul] using hh

/-- An invertible binary scalar operator is the identity, including on the zero space. -/
public theorem equiv_eq_refl_of_scalar {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W ≃ₗ[ZMod 2] W) (hc : ∃ c : ZMod 2, ∀ v, f v = c • v) :
    f = LinearEquiv.refl (ZMod 2) W := by
  obtain ⟨c, hc⟩ := hc
  apply LinearEquiv.ext
  intro v
  have hc01 : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases hc01 with rfl | rfl
  · have hv : v = 0 := f.injective (by simpa only [zero_smul, map_zero] using hc v)
    simp [hv]
  · simpa only [one_smul, LinearEquiv.refl_apply] using hc v
end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels
