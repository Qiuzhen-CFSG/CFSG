module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Cubic inversion and lifting moved subspaces

An involution inverting a fixed-point-free cubic operator has equal fixed and
moved spaces. An actor commuting with that involution therefore moves its fixed
vectors into the involution's moved space. Commutation is required only on the
representation, so the result applies to actors commuting modulo its kernel.

The second lemma lifts subspace containment through an actual equivariant
quotient of a normalized subgroup. It retains the kernel and requires that it
lie in the target subgroup; no splitting of the quotient is used.

These are the linear and lifting steps in Aschbacher--Smith, Lemma 14.4.12,
printed p.1012, combined manuscript of 1 March 2004.
-/

public section

namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A commuting actor moves fixed vectors into the moved space of an inverting
involution belonging to `W`. All operator relations are on the actual module. -/
theorem subspaceCommutator_le_of_cubic_inversion
    (ρ : Representation (ZMod 2) G V)
    (P : Submodule (ZMod 2) V) (A W : Subgroup G) (c x : G)
    (hc : (ρ c) ^ 3 = 1) (hfree : ∀ v, ρ c v = v → v = 0)
    (hx : ρ x * ρ x = 1) (hxc : ρ x * ρ c = (ρ c) ^ 2 * ρ x)
    (hP : ∀ v ∈ P, ρ x v = v)
    (hA : ∀ a ∈ A, Commute (ρ x) (ρ a)) (hxW : x ∈ W) :
    subspaceCommutator ρ P A ≤ subspaceCommutator ρ ⊤ W := by
  have hr := RankTwo.range_eq_ker_of_inverts_cubic (ρ c) (ρ x)
    (RankTwo.quadratic_of_cubic_fixed_free (ρ c) hc hfree) hx hxc
  apply Submodule.span_le.mpr
  rintro v ⟨a, ha, w, hw, rfl⟩
  have hk : ρ a w - w ∈ LinearMap.ker (ρ x - 1) := by
    change ρ x (ρ a w - w) - (ρ a w - w) = 0
    have hxa : ρ x (ρ a w) = ρ a (ρ x w) :=
      LinearMap.congr_fun (hA a ha).eq w
    rw [map_sub, hxa, hP w hw, sub_self]
  rw [← hr] at hk
  obtain ⟨u, hu⟩ := hk
  exact Submodule.subset_span ⟨x, hxW, u, Submodule.mem_top,
    (show ρ x u - u = ρ a w - w from hu).symm⟩

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {D Q : Type*} [Group D] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]

/-- Subspace commutator containment lifts along literal conjugation coordinates
when the target contains the quotient kernel. Normality is only relative to
the acting subgroup `X`. -/
theorem commutator_le_of_conjugation_image
    (ρ : Representation (ZMod 2) D (Additive Q)) (U P X E : Subgroup G)
    (hn : X ≤ normalizer (U : Set G)) (hPU : P ≤ U)
    (f : X →* D) (q : U →* Q)
    (hact : ∀ (x : X) (u : U), ρ (f x) (Additive.ofMul (q u)) =
      Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩))
    (Pbar Ebar : Submodule (ZMod 2) (Additive Q))
    (hP : ∀ u : U, (u : G) ∈ P → Additive.ofMul (q u) ∈ Pbar)
    (hE : Subgroup.toAddSubgroup.symm Ebar.toAddSubgroup = (E.subgroupOf U).map q)
    (hker : q.ker ≤ E.subgroupOf U)
    (hcomm : subspaceCommutator ρ Pbar f.range ≤ Ebar) : ⁅P, X⁆ ≤ E := by
  have hpre : (Subgroup.toAddSubgroup.symm Ebar.toAddSubgroup).comap q =
      E.subgroupOf U := by
    rw [hE, comap_map_eq, sup_eq_left.mpr hker]
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx p hp
  let xX : X := ⟨x, hx⟩
  let pU : U := ⟨p, hPU hp⟩
  let c : U := ⟨x * p * x⁻¹, le_normalizer_iff.mp hn x hx p (hPU hp)⟩
  have hd : ρ (f xX) (Additive.ofMul (q pU)) - Additive.ofMul (q pU) ∈ Ebar :=
    hcomm (Submodule.subset_span ⟨_, ⟨xX, rfl⟩, _, hP pU hp, rfl⟩)
  rw [hact] at hd
  have hmem : c * pU⁻¹ ∈ (Subgroup.toAddSubgroup.symm Ebar.toAddSubgroup).comap q := by
    change Additive.ofMul (q (c * pU⁻¹)) ∈ Ebar
    rw [map_mul, map_inv]
    change Additive.ofMul (q c) + -Additive.ofMul (q pU) ∈ Ebar
    simpa only [sub_eq_add_neg] using hd
  rw [hpre] at hmem
  exact hmem

end Representation.BinaryOffender
