module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.LocalSetup
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Suborbits

/-!
# The permutation kernel in the complement case

The actual action on the fixed-space orbit has kernel disjoint from the
cyclic actor in the complement case. Indeed, every nonfixed orbit member
has the second Step 1 suborbit type and hence trivial actor stabilizer.
An element of the kernel normalizes the actor and therefore centralizes it:
the commutator belongs both to the actor and to the normal kernel.

Orbit-stabilizer also gives the exact divisibility of the orbit cardinality
by the group order. These are the kernel and orbit transports for excluding
GLS C.14.2(iii) in the local approach to Aschbacher–Smith E.6.24, p.255.
-/

public section

open Module Subgroup Representation.BinaryOffender
open Representation.GoldschmidtONan
namespace Representation.RegularCyclicNormalClosure.FactorConstruction
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) X V) (Y : Subgroup X)

local instance fixedOrbitAction : MulAction X (fixedOrbit σ Y) where
  smul x U := ⟨U.val.map (σ x), map_mem_fixedOrbit U.property x⟩
  one_smul U := Subtype.ext (orbit_map_one U.val)
  mul_smul x y U := Subtype.ext (orbit_map_mul U.val x y)

/-- The actual permutation action on the fixed-space orbit. -/
@[expose] def fixedOrbitPermutation : X →* Equiv.Perm (fixedOrbit σ Y) :=
  MulAction.toPermHom X (fixedOrbit σ Y)

/-- Membership in the action kernel is literal fixation of every orbit member. -/
theorem mem_fixedOrbitPermutation_ker (x : X) :
    x ∈ (fixedOrbitPermutation σ Y).ker ↔
      ∀ U ∈ fixedOrbit σ Y, U.map (σ x) = U := by
  constructor
  · intro hx U hU
    exact congrArg Subtype.val (congrArg (fun p : Equiv.Perm (fixedOrbit σ Y) => p ⟨U, hU⟩) hx)
  · intro hx
    change fixedOrbitPermutation σ Y x = 1
    apply _root_.Equiv.ext
    intro U
    exact Subtype.ext (hx U U.property)

variable {σ Y} [Finite X] [Finite V]

omit [Finite X] in
/-- In the complement case, the cyclic actor has trivial intersection with
the kernel of the actual fixed-space permutation action. -/
theorem complement_kernel_disjoint_actor (h : GoldschmidtONan.Input σ Y)
    (hs : ComplementCase σ Y) (hsub : SuborbitGeometry σ Y) :
    Disjoint Y (fixedOrbitPermutation σ Y).ker := by
  have hex : ∃ U : fixedOrbit σ Y, U.val ≠ fixedSpace σ Y := by
    by_contra hn
    have hall : ∀ U : fixedOrbit σ Y, U.val = fixedSpace σ Y := by
      intro U
      by_contra he
      exact hn ⟨U, he⟩
    let : Subsingleton (fixedOrbit σ Y) := ⟨fun U T => Subtype.ext ((hall U).trans (hall T).symm)⟩
    let : Nontrivial (displacementSpan σ Y ⊤) := Submodule.nontrivial_iff_ne_bot.mpr h.moved_ne_bot
    have hle := (Finite.card_le_one_iff_subsingleton (α := fixedOrbit σ Y)).mpr inferInstance
    have hgt := Finite.one_lt_card (α := displacementSpan σ Y ⊤)
    rw [hs.1] at hle
    omega
  obtain ⟨U, hU⟩ := hex
  have hnle : ¬ U.val ≤ displacementSpan σ Y ⊤ := by
    intro hle
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h.orbit_ne_bot U.property)
    have hm : v ∈ {v : V | v ≠ 0 ∧ ∃ T ∈ fixedOrbit σ Y, v ∈ T} :=
      ⟨hv0, U.val, U.property, hv⟩
    rw [hs.2.1] at hm
    exact hm (hle hv)
  have hstab : ∀ y : Y, U.val.map (σ y) = U.val → y = 1 := by
    rcases hsub U U.property hU with hfirst | hsecond
    · exact (hnle hfirst.1).elim
    · exact hsecond.2.1
  apply Subgroup.disjoint_def.mpr
  intro y hy hk
  exact congrArg Subtype.val (hstab ⟨y, hy⟩
    ((mem_fixedOrbitPermutation_ker σ Y y).mp hk U U.property))

omit [Finite X] in
/-- In the complement case, an element of the orbit kernel centralizes the actor. -/
theorem complement_kernel_centralizes_actor (h : GoldschmidtONan.Input σ Y)
    (hs : ComplementCase σ Y) (hsub : SuborbitGeometry σ Y)
    (t : X) (ht : t ∈ (fixedOrbitPermutation σ Y).ker) :
    ∀ y ∈ Y, Commute y t := by
  let J := (fixedOrbitPermutation σ Y).ker
  have hdis := complement_kernel_disjoint_actor h hs hsub
  have hn : t ∈ normalizer (Y : Set X) := mem_normalizer_iff_map_conj_eq.mpr
    (h.normal_in_stabilizer t ((mem_fixedOrbitPermutation_ker σ Y t).mp ht _ fixed_mem_fixedOrbit))
  intro y hy
  have hmY : t * y * t⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem ((mem_normalizer_iff.mp hn y).mp hy) (Y.inv_mem hy)
  have hmJ : t * y * t⁻¹ * y⁻¹ ∈ J := by
    have hh := J.mul_mem ht ((inferInstance : J.Normal).conj_mem t⁻¹ (J.inv_mem ht) y)
    simpa only [mul_assoc] using hh
  have he := Subgroup.disjoint_def.mp hdis hmY hmJ
  have hh := congrArg (fun x : X => x * (y * t)) he
  change y * t = t * y
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using hh.symm

omit [Finite X] [Finite V] in
/-- The cardinality of the actual fixed-space orbit divides the acting group order. -/
theorem fixedOrbit_card_dvd : Nat.card (fixedOrbit σ Y) ∣ Nat.card X := by
  let : MulAction.IsPretransitive X (fixedOrbit σ Y) := ⟨by
    intro U T
    obtain ⟨x, hx⟩ := exists_map_eq_of_mem_fixedOrbit U.property T.property
    exact ⟨x, Subtype.ext hx⟩⟩
  let U : fixedOrbit σ Y := ⟨fixedSpace σ Y, fixed_mem_fixedOrbit⟩
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup X U)
  rw [Nat.card_prod, MulAction.orbit_eq_univ] at hh
  rw [Nat.card_congr (Equiv.Set.univ (fixedOrbit σ Y))] at hh
  exact ⟨Nat.card (MulAction.stabilizer X U), hh.symm⟩

end Representation.RegularCyclicNormalClosure.FactorConstruction
