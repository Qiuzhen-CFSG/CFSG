module
public import Theory.ElementaryAbelian.ExtraspecialPrimePairing
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group

/-!
# Inner automorphisms of extraspecial groups

The derived and Frattini subgroups of a finite extraspecial p-group are its
center. An automorphism trivial on the central quotient has a central
homomorphism as its displacement. This homomorphism kills the derived
subgroup, and commutator duality therefore realizes it by an inner
automorphism.

Source: Aschbacher–Smith, Lemma A.1.23, printed p.25, citing Aschbacher,
*Finite Group Theory*, (23.8).
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

private theorem quotientAut_kernel_congr {G : Type*} [Group G]
    (U V : Subgroup G) [U.Characteristic] [V.Characteristic] (h : U = V) :
    (quotientAut U).ker = (quotientAut V).ker := by
  subst V
  rfl

namespace IsExtraspecial
variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
  [IsExtraspecial p P]

include p

/-- The derived subgroup of an extraspecial group is its center. -/
public theorem commutator_eq_center : _root_.commutator P = center P := by
  let : IsElementaryAbelian p (P ⧸ center P) := quotient_elementary_abelian p P
  have hle : _root_.commutator P ≤ center P :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hne : _root_.commutator P ≠ ⊥ := by
    intro h
    let : Nontrivial (P ⧸ center P) := quotient_nontrivial p P
    exact QuotientGroup.nontrivial_iff.mp inferInstance
      ((commutator_eq_bot_iff_center_eq_top P).mp h)
  have hd : Nat.card (_root_.commutator P) ∣ p := by
    rw [← center_order_p p P]
    exact card_dvd_of_le hle
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with hc | hc
  · exact (hne (card_eq_one.mp hc)).elim
  · exact eq_of_le_of_card_ge hle (by rw [hc, center_order_p p P])

/-- The Frattini subgroup of an extraspecial group is its center. -/
public theorem frattini_eq_center : frattini P = center P := by
  have hP : IsPGroup p P := isPGroup p P
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsElementaryAbelian p (P ⧸ center P) := quotient_elementary_abelian p P
  let : Fact (IsPGroup p (P ⧸ center P)) := ⟨hP.to_quotient _⟩
  apply le_antisymm
  · have h := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective (center P))
    rw [frattini_eq_bot_of_isElementaryAbelian (R := P ⧸ center P) (p := p)] at h
    simpa using h
  · rw [← commutator_eq_center (p := p)]
    exact commutator_le_frattini_of_isPGroup (p := p)

/-- Every automorphism trivial modulo the center is a concrete conjugation. -/
public theorem exists_conj_of_central_displacement (α : MulAut P)
    (hα : ∀ x : P, α x * x⁻¹ ∈ center P) :
    ∃ r : P, MulAut.conj r = α := by
  let discrepancy : P →* center P := {
    toFun x := ⟨α x * x⁻¹, hα x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change α (x * y) * (x * y)⁻¹ = (α x * x⁻¹) * (α y * y⁻¹)
      have hc := mem_center_iff.mp (hα y) x⁻¹
      rw [map_mul, mul_inv_rev]
      calc
        α x * α y * (y⁻¹ * x⁻¹) = α x * ((α y * y⁻¹) * x⁻¹) := by group
        _ = α x * (x⁻¹ * (α y * y⁻¹)) := by rw [← hc]
        _ = _ := by group }
  have hker : center P ≤ discrepancy.ker := by
    exact (commutator_eq_center (p := p)).ge.trans
      (Abelianization.commutator_subset_ker discrepancy)
  obtain ⟨r, hr⟩ := extraspecial_commutator_represents_hom (p := p)
    (QuotientGroup.lift (center P) discrepancy hker)
  refine ⟨r, MulEquiv.ext fun x => ?_⟩
  have hx : α x * x⁻¹ = ⁅r, x⁆ := hr x
  have hh := congrArg (fun z : P => z * x) hx
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one,
    MulAut.conj_apply] using hh.symm

/-- The action on the central quotient has precisely the inner automorphisms
as its kernel. -/
public theorem quotientAut_center_ker_eq_range_conj :
    (quotientAut (center P)).ker = (MulAut.conj : P →* MulAut P).range := by
  ext α
  constructor
  · intro hα
    apply exists_conj_of_central_displacement (p := p) α
    intro x
    have hh := DFunLike.congr_fun hα (QuotientGroup.mk' (center P) x)
    rw [quotientAut_apply_mk] at hh
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (center P)) (α x * x⁻¹) = 1
    rw [map_mul, map_inv, hh]
    exact mul_inv_cancel _
  · rintro ⟨r, rfl⟩
    let : IsElementaryAbelian p (P ⧸ center P) := quotient_elementary_abelian p P
    apply MulEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center P) x
    rw [quotientAut_apply_mk, MulAut.conj_apply, map_mul, map_mul, map_inv]
    change _ = QuotientGroup.mk' (center P) x
    rw [mul_comm (QuotientGroup.mk' (center P) r), mul_inv_cancel_right]

/-- For an extraspecial group, the kernel of the full automorphism action
on the Frattini quotient is the group of inner automorphisms. -/
public theorem quotientAut_frattini_ker_eq_range_conj :
    (quotientAut (frattini P)).ker = (MulAut.conj : P →* MulAut P).range := by
  exact (quotientAut_kernel_congr (frattini P) (center P)
    (frattini_eq_center (p := p))).trans
    (quotientAut_center_ker_eq_range_conj (p := p))

end IsExtraspecial
