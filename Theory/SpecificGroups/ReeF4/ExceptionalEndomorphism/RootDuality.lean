module

public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality

-- Internal extension: construct the classification certificate hidden by Core.
import all Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.Core
public import Theory.AlgebraicGroup.RootSystems.F4RootPairing

/-!
# The standard F4 root involution

The unique positive duality exchanges the two root lengths and reverses the
numbered base. Its inverse satisfies the same specification, so uniqueness
makes it an involution. Geometric lengths are identified using the explicit
Euclidean root-coroot pairing: `IsLongIndex` in the existing duality interface
names the geometrically short class, and `IsShortIndex` the long class.

This is the root datum for the exceptional endomorphism used in the Ree
construction; see Aschbacher–Smith, *The Classification of Quasithin Groups*,
Remark A.2.4 (`refs/quasithin.pdf`). No group endomorphism is asserted here.
-/

public section

namespace ReeF4

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

private theorem f4_cartan_integer_formula
    (i j : typeF4RootPairing_base.support) :
    typeF4RootPairing_base.cartanMatrixIn ℤ i j =
      dynkinCartanEntry ⟨.F4, 4⟩
        (typeF4RootPairing_baseEquiv.symm i) (typeF4RootPairing_baseEquiv.symm j) := by
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
  simpa [dynkinCartanEntry, typeF4CartanMatrix] using
    typeF4RootPairing_base_cartan_apply i j

private theorem f4_duality_unique :
    ExistsUnique (typeF4RootPairing.IsPositiveRootDuality typeF4RootPairing_base) :=
  existsUnique_exceptionalRootDuality typeF4RootPairing_base ⟨.F4, 4⟩
    typeF4RootPairing_baseEquiv.symm f4_cartan_integer_formula
    (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- The unique positive, length-interchanging duality of the standard F4 roots. -/
noncomputable def exceptionalRootPermutation : Equiv.Perm typeF4Roots :=
  Classical.choose f4_duality_unique.exists

theorem exceptionalRootPermutation_spec :
    typeF4RootPairing.IsPositiveRootDuality typeF4RootPairing_base
      exceptionalRootPermutation :=
  Classical.choose_spec f4_duality_unique.exists

theorem exceptionalRootPermutation_unique {ρ : Equiv.Perm typeF4Roots}
    (hρ : typeF4RootPairing.IsPositiveRootDuality typeF4RootPairing_base ρ) :
    ρ = exceptionalRootPermutation :=
  f4_duality_unique.unique hρ exceptionalRootPermutation_spec

theorem exceptionalRootPermutation_involutive :
    Function.Involutive exceptionalRootPermutation := by
  let ρ := exceptionalRootPermutation
  obtain ⟨hs, hp, hl, hh, hc⟩ := exceptionalRootPermutation_spec
  have hinv : typeF4RootPairing.IsPositiveRootDuality typeF4RootPairing_base ρ.symm := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r
      simpa only [ρ, Equiv.apply_symm_apply] using (hs (ρ.symm r)).symm
    · intro r
      simpa only [ρ, Equiv.apply_symm_apply] using (hp (ρ.symm r)).symm
    · intro r
      simpa only [ρ, Equiv.apply_symm_apply] using (hh (ρ.symm r)).symm
    · intro r
      simpa only [ρ, Equiv.apply_symm_apply] using (hl (ρ.symm r)).symm
    · intro r s
      simpa only [ρ, Equiv.apply_symm_apply] using (hc (ρ.symm r) (ρ.symm s)).symm
  have he : ρ.symm = ρ := exceptionalRootPermutation_unique hinv
  intro r
  exact (congrArg (fun e : Equiv.Perm typeF4Roots => e (ρ r)) he).symm.trans
    (ρ.symm_apply_apply r)

/-- Geometrically long F4 roots are the signed pair roots, of squared length two. -/
@[expose] def IsLongRoot (r : typeF4Roots) : Prop := r.val ∈ pairRoots 4

/-- All other F4 roots have squared length one. -/
@[expose] def IsShortRoot (r : typeF4Roots) : Prop := ¬IsLongRoot r

theorem isLongRoot_norm (r : typeF4Roots) (hr : IsLongRoot r) :
    dot r.val r.val = 2 := typeF4Root_dot_self_of_pair r hr

theorem isShortRoot_norm (r : typeF4Roots) (hr : IsShortRoot r) :
    dot r.val r.val = 1 := typeF4Root_dot_self_of_not_pair r hr

private theorem not_longIndex_of_long {r : typeF4Roots} (hr : IsLongRoot r) :
    ¬typeF4RootPairing.IsLongIndex r := by
  rintro ⟨s, hs⟩
  have hs' : |typeF4RootPairing.pairing r s| <
      |typeF4RootPairing.pairing s r| := by
    rw [← typeF4RootPairing.algebraMap_pairingIn ℤ,
      ← typeF4RootPairing.algebraMap_pairingIn ℤ]
    simp only [algebraMap_int_eq, Int.coe_castRingHom]
    exact_mod_cast hs
  rw [typeF4RootPairing_pairing, typeF4RootPairing_pairing,
    typeF4CorootScale_of_pair r hr, one_mul] at hs'
  have hdot : dot s.val r.val = dot r.val s.val := by
    simp only [dot, mul_comm]
  rw [hdot] at hs'
  by_cases h : s.val ∈ pairRoots 4
  · rw [typeF4CorootScale_of_pair s h, one_mul] at hs'
    exact (lt_irrefl _ hs')
  · rw [typeF4CorootScale_of_not_pair s h, abs_mul] at hs'
    norm_num at hs'
    linarith [abs_nonneg (dot r.val s.val)]

private theorem not_shortIndex_of_short {r : typeF4Roots} (hr : IsShortRoot r) :
    ¬typeF4RootPairing.IsShortIndex r := by
  rintro ⟨s, hs⟩
  have hs' : |typeF4RootPairing.pairing s r| <
      |typeF4RootPairing.pairing r s| := by
    rw [← typeF4RootPairing.algebraMap_pairingIn ℤ,
      ← typeF4RootPairing.algebraMap_pairingIn ℤ]
    simp only [algebraMap_int_eq, Int.coe_castRingHom]
    exact_mod_cast hs
  rw [typeF4RootPairing_pairing, typeF4RootPairing_pairing,
    typeF4CorootScale_of_not_pair r hr] at hs'
  have hdot : dot s.val r.val = dot r.val s.val := by
    simp only [dot, mul_comm]
  rw [hdot] at hs'
  by_cases h : s.val ∈ pairRoots 4
  · rw [typeF4CorootScale_of_pair s h, one_mul, abs_mul] at hs'
    norm_num at hs'
    linarith [abs_nonneg (dot r.val s.val)]
  · rw [typeF4CorootScale_of_not_pair s h] at hs'
    exact (lt_irrefl _ hs')

private theorem length_partition (r : typeF4Roots) :
    typeF4RootPairing.IsLongIndex r ∨ typeF4RootPairing.IsShortIndex r :=
  exceptionalRootPairing_isLong_or_isShort typeF4RootPairing_base ⟨.F4, 4⟩
    typeF4RootPairing_baseEquiv.symm f4_cartan_integer_formula
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) r

/-- The directed-pairing predicate `IsShortIndex` is the geometric long class. -/
theorem isLongRoot_iff_shortIndex (r : typeF4Roots) :
    IsLongRoot r ↔ typeF4RootPairing.IsShortIndex r := by
  classical
  constructor
  · intro hr
    exact (length_partition r).resolve_left (not_longIndex_of_long hr)
  · intro hr
    by_contra h
    exact not_shortIndex_of_short h hr

/-- The directed-pairing predicate `IsLongIndex` is the geometric short class. -/
theorem isShortRoot_iff_longIndex (r : typeF4Roots) :
    IsShortRoot r ↔ typeF4RootPairing.IsLongIndex r := by
  classical
  constructor
  · intro hr
    exact (length_partition r).resolve_right (not_shortIndex_of_short hr)
  · intro hr hl
    exact not_longIndex_of_long hl hr

theorem exceptionalRootPermutation_long_iff (r : typeF4Roots) :
    IsLongRoot r ↔ IsShortRoot (exceptionalRootPermutation r) := by
  rw [isLongRoot_iff_shortIndex, isShortRoot_iff_longIndex]
  exact exceptionalRootPermutation_spec.2.2.2.1 r

theorem exceptionalRootPermutation_short_iff (r : typeF4Roots) :
    IsShortRoot r ↔ IsLongRoot (exceptionalRootPermutation r) := by
  rw [isLongRoot_iff_shortIndex, isShortRoot_iff_longIndex]
  exact exceptionalRootPermutation_spec.2.2.1 r

private theorem simple_pairing (i j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex i)
      (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j := by
  exact typeF4RootPairing_base_cartan_apply i j

set_option maxHeartbeats 800000 in
private theorem numbered_reversal_check :
    ∀ p : Equiv.Perm (Fin 4),
      (∀ i, i.val < 2 ↔ ¬(p i).val < 2) →
      (∀ i j,
        typeF4CartanMatrix (p i) (p j) * typeF4CartanMatrix (p j) (p i) =
          typeF4CartanMatrix i j * typeF4CartanMatrix j i) →
      p = Fin.revPerm := by
  decide

/-- The positive duality reverses the standard numbered diagram. -/
theorem exceptionalRootPermutation_simple (i : Fin 4) :
    exceptionalRootPermutation (typeF4SimpleRootIndex i) =
      typeF4SimpleRootIndex (Fin.revPerm i) := by
  let p := supportPerm typeF4RootPairing_base typeF4RootPairing_baseEquiv.symm
    exceptionalRootPermutation exceptionalRootPermutation_spec.1
  have hp (j : Fin 4) : typeF4SimpleRootIndex (p j) =
      exceptionalRootPermutation (typeF4SimpleRootIndex j) :=
    congrArg Subtype.val (supportPerm_apply typeF4RootPairing_base
      typeF4RootPairing_baseEquiv.symm exceptionalRootPermutation
      exceptionalRootPermutation_spec.1 j)
  have plen (j : Fin 4) : j.val < 2 ↔ ¬(p j).val < 2 := by
    rw [← typeF4SimpleRootIndex_mem_pair_iff, ← typeF4SimpleRootIndex_mem_pair_iff]
    change IsLongRoot (typeF4SimpleRootIndex j) ↔ IsShortRoot (typeF4SimpleRootIndex (p j))
    rw [hp]
    exact exceptionalRootPermutation_long_iff _
  have pprod (j k : Fin 4) :
      typeF4CartanMatrix (p j) (p k) * typeF4CartanMatrix (p k) (p j) =
        typeF4CartanMatrix j k * typeF4CartanMatrix k j := by
    rw [← simple_pairing, ← simple_pairing, ← simple_pairing, ← simple_pairing, hp, hp]
    exact exceptionalRootPermutation_spec.2.2.2.2 _ _
  have he := numbered_reversal_check p plen pprod
  simpa only [he] using (hp i).symm

/-- The parameter part of the exceptional root formula: only short-root
parameters are squared. -/
noncomputable def exceptionalParameter {K : Type*} [Monoid K]
    (r : typeF4Roots) (t : K) : K := by
  classical
  exact if IsLongRoot r then t else t ^ 2

theorem exceptionalParameter_of_long {K : Type*} [Monoid K]
    {r : typeF4Roots} (hr : IsLongRoot r) (t : K) :
    exceptionalParameter r t = t := by
  simp [exceptionalParameter, hr]

theorem exceptionalParameter_of_short {K : Type*} [Monoid K]
    {r : typeF4Roots} (hr : IsShortRoot r) (t : K) :
    exceptionalParameter r t = t ^ 2 := by
  simp [exceptionalParameter, show ¬IsLongRoot r from hr]

/-- Applying the exceptional root formula twice squares the parameter. -/
theorem exceptionalParameter_twice {K : Type*} [Monoid K]
    (r : typeF4Roots) (t : K) :
    exceptionalParameter (exceptionalRootPermutation r) (exceptionalParameter r t) =
      t ^ 2 := by
  classical
  by_cases hr : IsLongRoot r
  · rw [exceptionalParameter_of_long hr,
      exceptionalParameter_of_short ((exceptionalRootPermutation_long_iff r).mp hr)]
  · rw [exceptionalParameter_of_short hr,
      exceptionalParameter_of_long ((exceptionalRootPermutation_short_iff r).mp hr)]

end ReeF4
