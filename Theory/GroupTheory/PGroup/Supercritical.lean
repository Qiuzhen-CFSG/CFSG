module

public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Nilpotent

/-!+# Supercritical subgroups

A supercritical subgroup is characteristic, has central Frattini subgroup
and central ambient commutators, has exponent dividing p, and contains all
order-p elements of its ambient centralizer. The exponent-divisibility
formulation includes the trivial subgroup of the trivial p-group.

The ambient commutator condition implies that its derived subgroup is central,
so its nilpotency class is at most two. These elementary consequences are
independent of the stronger critical-subgroup existence theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition A.1.20 and Lemma A.1.21(2), printed pp.24–25.
-/

open Subgroup
open scoped commutatorElement

/-- The supercritical conditions, including the order-p centralizer condition. -/
public structure IsSupercriticalPSubgroup (p : ℕ) {P : Type*} [Group P]
    (X : Subgroup P) : Prop where
  characteristic : X.Characteristic
  frattini_le_center : frattini X ≤ center X
  commutator_le : ⁅X, (⊤ : Subgroup P)⁆ ≤ (center X).map X.subtype
  exponent_dvd_p : Monoid.exponent X ∣ p
  order_p_mem : ∀ x : P, x ∈ centralizer (X : Set P) → orderOf x = p → x ∈ X

namespace IsSupercriticalPSubgroup

variable {p : ℕ} {P : Type*} [Group P] {X : Subgroup P}

/-- Every element of a supercritical subgroup has p-th power one. -/
public theorem pow_eq_one (hX : IsSupercriticalPSubgroup p X) (x : X) :
    x ^ p = 1 :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hX.exponent_dvd_p x

/-- A supercritical subgroup is its own first omega subgroup. -/
public theorem omega₁_eq_top (hX : IsSupercriticalPSubgroup p X) :
    omega₁ X (p := p) = ⊤ := by
  apply top_unique
  intro x _
  apply subset_closure
  change x ^ (p ^ 1) = 1
  simpa only [pow_one] using hX.pow_eq_one x

/-- The first omega subgroup of the ambient centralizer lies in the
supercritical subgroup. This is the subgroup form of the order-p condition. -/
public theorem omega₁_centralizer_le [Fact p.Prime]
    (hX : IsSupercriticalPSubgroup p X) :
    (omega₁ (centralizer (X : Set P)) (p := p)).map
      (centralizer (X : Set P)).subtype ≤ X := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  change (x : P) ∈ X
  by_cases hne : (x : P) = 1
  · rw [hne]
    exact X.one_mem
  · apply hX.order_p_mem x x.property
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, hne⟩
    have hxpow : x ^ p = 1 := by
      change x ^ (p ^ 1) = 1 at hx
      simpa only [pow_one] using hx
    exact congrArg Subtype.val hxpow

/-- The derived subgroup of a supercritical subgroup is central. -/
public theorem derived_le_center (hX : IsSupercriticalPSubgroup p X) :
    _root_.commutator X ≤ center X := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  have hm : ((⁅x, y⁆ : X) : P) ∈ (center X).map X.subtype :=
    hX.commutator_le (commutator_mem_commutator x.property (mem_top (y : P)))
  obtain ⟨z, hz, heq⟩ := hm
  exact (Subtype.ext heq : z = ⁅x, y⁆) ▸ hz

/-- The lower central series terminates after two commutator steps. -/
public theorem lowerCentralSeries_two (hX : IsSupercriticalPSubgroup p X) :
    (⊤ : Subgroup X).lowerCentralSeries 2 = ⊥ := by
  rw [show 2 = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
    Subgroup.top_lowerCentralSeries_one]
  exact bot_unique ((commutator_mono hX.derived_le_center le_rfl).trans
    (commutator_center_left ⊤).le)

/-- A supercritical subgroup is nilpotent. -/
public theorem isNilpotent (hX : IsSupercriticalPSubgroup p X) : Group.IsNilpotent X :=
  (Subgroup.nilpotent_iff_lowerCentralSeries).mpr ⟨2, hX.lowerCentralSeries_two⟩

/-- A supercritical subgroup has nilpotency class at most two. -/
public theorem nilpotencyClass_le_two (hX : IsSupercriticalPSubgroup p X) :
    Group.nilpotencyClass X ≤ 2 := by
  let := hX.isNilpotent
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hX.lowerCentralSeries_two

end IsSupercriticalPSubgroup
