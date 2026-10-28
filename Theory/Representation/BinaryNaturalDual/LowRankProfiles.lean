module
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Theory.Representation.DualCommutator

/-!
# Low-rank commutator profiles on a binary three-space and its dual

Quadraticity puts the moved space in the fixed space. Duality identifies the
other moved dimension with the fixed codimension, so their sum is at most
three. Faithfulness makes both positive; cyclic duality gives 1+1 in rank
one, and the displacement-map rank bound gives 1+2 or 2+1 in rank two.
The two moved spaces are orthogonal under the literal evaluation pairing.

Source: Aschbacher--Smith, 14.6.24(4), printed p.1041. These are intrinsic
linear profiles; the original quotient and orbit matching are supplied by
the section and source consumers.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace BinaryNaturalDual.LowRankProfiles
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem moved_le_fixed {A : Subgroup G} (hq : IsQuadratic ρ A) :
    subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,v,_,rfl⟩ b
  exact hq b b.property a ha v

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem moved_orthogonal {A : Subgroup G} (hq : IsQuadratic ρ A)
    (x : V) (hx : x ∈ subspaceCommutator ρ ⊤ A)
    (f : Module.Dual (ZMod 2) V) (hf : f ∈ subspaceCommutator ρ.dual ⊤ A) : f x = 0 := by
  have hfix := moved_le_fixed ρ hq hx
  have hle : subspaceCommutator ρ.dual ⊤ A ≤ LinearMap.ker (Module.Dual.eval (ZMod 2) V x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,l,_,rfl⟩
    change l (ρ a⁻¹ x) - l x = 0
    have he : ρ a⁻¹ x = x := hfix ⟨a⁻¹,A.inv_mem ha⟩
    rw [he,sub_self]
  exact hle hf

omit [Finite G] in
theorem dual_moved_finrank (A : Subgroup G) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ A) = fixedCodim ρ A := by
  rw [subspaceCommutator_top_eq_coinvariants]
  exact (finrank_quotient_invariants_eq_dual_commutator (ρ.comp A.subtype)).symm

/-- A rank-one quadratic actor moves one line in each of the dual summands. -/
theorem rank_one_dimensions (hρ : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 3)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hr : rank A = 1)
    (hq : IsQuadratic ρ A) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) = 1 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ A) = 1 := by
  have hc : Nat.card A = 2 := by simpa only [hr,pow_one] using hA.card_eq_two_pow_rank
  let : IsCyclic A := isCyclic_of_prime_card hc
  obtain ⟨a,ha⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have he : fixedCodim ρ.dual A = fixedCodim ρ A := by
    rw [←ha,fixedCodim_zpowers_dual]
  have hm := Submodule.finrank_mono (moved_le_fixed ρ hq)
  have hs := fixedCodim_add_finrank ρ A
  have hp := fixedCodim_pos_of_faithful ρ hρ hA.1
  rw [←fixedCodim_dual_eq_moved_finrank,he] at hm
  rw [←fixedCodim_dual_eq_moved_finrank,dual_moved_finrank,he]
  omega

/-- A rank-two quadratic actor moves a plane and its annihilator line, in either order. -/
theorem rank_two_dimensions (hρ : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 3)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hr : rank A = 2)
    (hq : IsQuadratic ρ A) :
    (Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) = 1 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ A) = 2) ∨
    (Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) = 2 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ A) = 1) := by
  have hm := Submodule.finrank_mono (moved_le_fixed ρ hq)
  have hs := fixedCodim_add_finrank ρ A
  have hp := fixedCodim_pos_of_faithful ρ hρ hA.1
  have hqpos := fixedCodim_pos_of_faithful ρ.dual (faithful_dual ρ hρ) hA.1
  have hb := rank_le_fixedCodim_mul_dual ρ hρ A
  rw [hr] at hb
  rw [←fixedCodim_dual_eq_moved_finrank] at hm
  rw [←fixedCodim_dual_eq_moved_finrank,dual_moved_finrank]
  have hp2 : fixedCodim ρ A ≤ 2 := by omega
  have hq2 : fixedCodim ρ.dual A ≤ 2 := by omega
  interval_cases hpf : fixedCodim ρ A <;>
    interval_cases hqf : fixedCodim ρ.dual A <;> omega
end BinaryNaturalDual.LowRankProfiles
