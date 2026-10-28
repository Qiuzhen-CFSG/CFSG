module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Field.ZMod
public import Theory.ElementaryAbelian.Basic

/-!
# Binary module sections with a specified conjugation action

A surjective coordinate homomorphism with kernel B identifies the actual
section A/B with a binary vector space. Equivariance records the ambient
H-conjugation action, and normality is relative to H. The order formula
follows from the first isomorphism theorem. When the kernel is central of
exponent two and the actor is transitive on nonzero quotient vectors, one
square-one lift forces every lift to have square one. This gives elementary
abelianness of the original group, not just its quotient.

This interface is used for the natural, Steinberg and indecomposable sections
in Aschbacher–Smith, §J.1, conditions Ru1 and Ru2 (printed p.431).
-/

@[expose] public section
noncomputable section
namespace Representation
open Subgroup
variable {G : Type*} [Group G]

/-- A module section with its literal conjugation action and kernel. -/
structure BinaryConjugationSection (H A B : Subgroup G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) where
  section_le : A ≤ H
  kernel_le : B ≤ A
  normalized : H ≤ normalizer A
  coordinates : A →* Multiplicative W
  onto : Function.Surjective coordinates
  kernel_eq : coordinates.ker = B.subgroupOf A
  equivariant (h : H) (a : A) :
    (coordinates ⟨h * a * (h : G)⁻¹,
      (mem_normalizer_iff.mp (normalized h.property) a).mp a.property⟩).toAdd =
      ρ h (coordinates a).toAdd

namespace BinaryConjugationSection
variable {H A B : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (d : BinaryConjugationSection H A B ρ)

include d in
theorem card_section : Nat.card A = Nat.card W * Nat.card B := by
  rw [card_eq_card_quotient_mul_card_subgroup d.coordinates.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective d.coordinates d.onto).toEquiv]
  have hk : Nat.card d.coordinates.ker = Nat.card B := by
    rw [d.kernel_eq]
    exact Nat.card_congr (subgroupOfEquivOfLe d.kernel_le).toEquiv
  rw [hk]
  rfl

theorem coordinates_eq_one_iff (a : A) : d.coordinates a = 1 ↔ (a : G) ∈ B := by
  change a ∈ d.coordinates.ker ↔ _
  rw [d.kernel_eq]
  rfl

end BinaryConjugationSection

end Representation

namespace Representation.BinaryConjugationSection
open Subgroup
variable {G : Type*} [Group G] {H A B : Subgroup G}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (d : BinaryConjugationSection H A B ρ)

include d in
theorem kernel_normal : (B.subgroupOf A).Normal := by
  rw [← d.kernel_eq]
  infer_instance

/-- The coordinate map gives an isomorphism of the literal subgroup quotient. -/
def quotientEquiv [(B.subgroupOf A).Normal] : (A ⧸ B.subgroupOf A) ≃* Multiplicative W :=
  (QuotientGroup.quotientMulEquivOfEq d.kernel_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.coordinates d.onto)

theorem quotientEquiv_mk [(B.subgroupOf A).Normal] (a : A) :
    d.quotientEquiv (QuotientGroup.mk' (B.subgroupOf A) a) = d.coordinates a := rfl

include d in
theorem square_eq_one_of_trivial_kernel (hB : B = ⊥) (a : A) : a ^ 2 = 1 := by
  have hi : Function.Injective d.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [d.kernel_eq, hB, bot_subgroupOf]
  apply hi
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  change 2 • (d.coordinates a).toAdd = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]

include d in
theorem elementary_of_transitive
    (hcentral : B ≤ centralizer (A : Set G))
    (hBsq : ∀ b ∈ B, b ^ 2 = 1)
    (hseed : ∃ a : A, a ^ 2 = 1 ∧ d.coordinates a ≠ 1)
    (htrans : ∀ u v : W, u ≠ 0 → v ≠ 0 → ∃ h : H, ρ h u = v) :
    IsElementaryAbelian 2 A := by
  obtain ⟨v, hvsq, hv⟩ := hseed
  have hsquare (a : A) : a ^ 2 = 1 := by
    by_cases ha : d.coordinates a = 1
    · apply Subtype.ext
      exact hBsq a ((d.coordinates_eq_one_iff a).mp ha)
    have hv0 : (d.coordinates v).toAdd ≠ 0 := hv
    have ha0 : (d.coordinates a).toAdd ≠ 0 := ha
    obtain ⟨h, hh⟩ := htrans _ _ hv0 ha0
    let b : A := ⟨h * v * (h : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized h.property) v).mp v.property⟩
    have hcoord : d.coordinates b = d.coordinates a :=
      Multiplicative.toAdd.injective ((d.equivariant h v).trans hh)
    have hbsq : b ^ 2 = 1 := by
      apply Subtype.ext
      change (MulAut.conj (h : G) (v : G)) ^ 2 = 1
      rw [← map_pow, show (v : G) ^ 2 = 1 from congrArg Subtype.val hvsq, map_one]
    let c : A := b⁻¹ * a
    have hc : (c : G) ∈ B := by
      apply (d.coordinates_eq_one_iff c).mp
      change d.coordinates (b⁻¹ * a) = 1
      rw [map_mul, map_inv, hcoord, inv_mul_cancel]
    have hcsq : c ^ 2 = 1 := Subtype.ext (hBsq c hc)
    have hbc : Commute b c := Subtype.ext (hcentral hc b b.property)
    calc
      a ^ 2 = (b * c) ^ 2 := by simp [c]
      _ = b ^ 2 * c ^ 2 := hbc.mul_pow 2
      _ = 1 := by rw [hbsq, hcsq, mul_one]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsquare x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }

end Representation.BinaryConjugationSection
