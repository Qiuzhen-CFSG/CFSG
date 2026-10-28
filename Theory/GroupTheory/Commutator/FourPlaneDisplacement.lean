module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# A four-plane displacement forces a derived subgroup

Suppose a binary four-space W has a plane E contained in [R,R], and A ≤ R
acts trivially on W/E. For q ∈ R, assume its displacements on A lie in W
and their images modulo E have kernel A ∩ P of index four. The literal
commutator map A → W/E is a homomorphism. Its four-element image is all
of W/E, so W ≤ [R,R]. A preliminary index estimate identifies a proper
centralizer containing a subgroup of at least half the ambient order.

These are the cardinal and displacement steps in the fixed-line MS kernel
argument, Aschbacher--Smith, C.1.31(MS3), p.135, and 12.4.6, pp.813--814.
The source application is FixedBlockSpecializationProductsKernel.lean.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial action on a group of at most twice the fixed subgroup order
has exactly that fixed subgroup. -/
theorem centralizer_inter_eq_of_card_le_twice
    (P W : Subgroup G) (hWP : W ≤ P) (q : G)
    (hWq : W ≤ centralizer ({q} : Set G))
    (hPq : ¬ P ≤ centralizer ({q} : Set G))
    (hcard : Nat.card P ≤ 2 * Nat.card W) :
    P ⊓ centralizer ({q} : Set G) = W := by
  let C := P ⊓ centralizer ({q} : Set G)
  have hWC : W ≤ C := le_inf hWP hWq
  have hi0 : C.relIndex P ≠ 0 := (C.subgroupOf P).index_ne_zero_of_finite
  have hi1 : C.relIndex P ≠ 1 := fun he => hPq ((relIndex_eq_one.mp he).trans inf_le_right)
  have hi2 : 2 ≤ C.relIndex P := by omega
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) C P bot_le inf_le_left
  simp only [relIndex_bot_left] at hc
  have hCcard : Nat.card C ≤ Nat.card W := by nlinarith
  exact (eq_of_le_of_card_ge hWC hCcard).symm

/-- A displacement map with four-element image modulo the plane forces the
whole four-space into the derived subgroup. -/
theorem le_self_commutator_of_four_plane_displacement
    (A P W E R : Subgroup G) [IsElementaryAbelian 2 W]
    (hAE : ⁅A,W⁆ ≤ E) (hEW : E ≤ W) (hER : E ≤ ⁅R,R⁆)
    (hAR : A ≤ R) (hWc : Nat.card W = 16) (hEc : Nat.card E = 4)
    (hindex : P.relIndex A = 4) (q : G) (hq : q ∈ R)
    (hcomm : ∀ a ∈ A, ⁅a,q⁆ ∈ W)
    (hker : ∀ a ∈ A, ⁅a,q⁆ ∈ E ↔ a ∈ P) : W ≤ ⁅R,R⁆ := by
  let _ : CommGroup W := IsMulCommutative.instCommGroup
  let π := QuotientGroup.mk' (E.subgroupOf W)
  have hn : A ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hAE.trans hEW)
  have hinv (a : A) (v : W) :
      π ⟨(a : G) * (v : G) * (a : G)⁻¹,
        (mem_normalizer_iff.mp (hn a.property) v).mp v.property⟩ = π v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ((a : G) * (v : G) * (a : G)⁻¹) / (v : G) ∈ E
    simpa only [div_eq_mul_inv,commutatorElement_def] using
      hAE (commutator_mem_commutator a.property v.property)
  let f : A →* (W ⧸ E.subgroupOf W) := {
    toFun := fun a => π ⟨⁅(a : G),q⁆,hcomm a a.property⟩
    map_one' := by
      rw [show (⟨⁅((1 : A) : G),q⁆,hcomm 1 (one_mem A)⟩ : W) = 1 from
        Subtype.ext (by simp),map_one]
    map_mul' := by
      intro a b
      have he : (⟨⁅((a*b : A) : G),q⁆,hcomm (a*b) (a*b).property⟩ : W) =
          ⟨(a : G) * ⁅(b : G),q⁆ * (a : G)⁻¹,
            (mem_normalizer_iff.mp (hn a.property) _).mp (hcomm b b.property)⟩ *
          ⟨⁅(a : G),q⁆,hcomm a a.property⟩ :=
        Subtype.ext (commutatorElement_mul_left_eq_conj_mul (a : G) (b : G) q)
      rw [he,map_mul,hinv a ⟨⁅(b : G),q⁆,hcomm b b.property⟩,mul_comm] }
  have hk : f.ker = P.subgroupOf A := by
    ext a
    change π ⟨⁅(a : G),q⁆,hcomm a a.property⟩ = 1 ↔ (a : G) ∈ P
    exact (QuotientGroup.eq_one_iff (⟨⁅(a : G),q⁆,hcomm a a.property⟩ : W)).trans
      (hker a a.property)
  have hfc : Nat.card f.range = 4 := by
    rw [← index_ker,hk]
    exact hindex
  have hc : Nat.card (W ⧸ E.subgroupOf W) = 4 := by
    have hec : Nat.card (E.subgroupOf W) = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hEW).toEquiv).trans hEc
    have hh := card_eq_card_quotient_mul_card_subgroup (E.subgroupOf W)
    rw [hWc,hec] at hh
    omega
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (f.range.eq_top_of_card_eq (hfc.trans hc.symm))
  intro v hv
  obtain ⟨a,ha⟩ := hf (π ⟨v,hv⟩)
  have he : (⟨⁅(a : G),q⁆,hcomm a a.property⟩ : W) / ⟨v,hv⟩ ∈ E.subgroupOf W :=
    QuotientGroup.eq_iff_div_mem.mp ha
  have hd : ⁅(a : G),q⁆ ∈ ⁅R,R⁆ := commutator_mem_commutator (hAR a.property) hq
  have hh := (⁅R,R⁆).mul_mem ((⁅R,R⁆).inv_mem (hER he)) hd
  have hid : (⁅(a : G),q⁆ / v)⁻¹ * ⁅(a : G),q⁆ = v := by simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one]
  exact hid ▸ hh

end Subgroup
