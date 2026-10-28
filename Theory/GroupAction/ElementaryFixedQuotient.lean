module
public import Theory.GroupTheory.ElementaryFixedQuotientLifting
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# The exact fixed quotient through an elementary kernel

The fixed-group projection has precisely the fixed part of the original
characteristic kernel. If an involution has a square-root fixed subgroup on
that elementary kernel, the existing coboundary lifting theorem makes the
projection surjective. Thus the fixed subgroup modulo the fixed kernel is
the fixed subgroup of the original quotient, with its literal quotient map.

Source application: Aschbacher–Smith, 2.4.12(2) and 2.4.23(1,3),
printed pp.532 and537 of the combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace MulAut
variable {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic] (a : MulAut G)
@[expose] noncomputable def fixedQuotientProjection : a.fixedSubgroup →* (quotientAut N a).fixedSubgroup :=
  ((QuotientGroup.mk' N).comp a.fixedSubgroup.subtype).codRestrict _ (by
    intro x
    rw [mem_fixedSubgroup]
    change quotientAut N a (QuotientGroup.mk' N x.val) = QuotientGroup.mk' N x.val
    rw [quotientAut_apply_mk, (mem_fixedSubgroup a x.val).mp x.property])

@[simp] theorem fixedQuotientProjection_apply (x : a.fixedSubgroup) :
    (fixedQuotientProjection N a x : G ⧸ N) = QuotientGroup.mk' N x.val := rfl

@[simp] theorem fixedQuotientProjection_kernel :
    (fixedQuotientProjection N a).ker = N.subgroupOf a.fixedSubgroup := by
  ext x
  change (⟨QuotientGroup.mk' N x.val, _⟩ : (quotientAut N a).fixedSubgroup) = 1 ↔ x.val ∈ N
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff x.val

theorem fixedQuotientProjection_surjective [Finite G] [IsElementaryAbelian 2 N]
    (ha : a ^ 2 = 1)
    (hc : Nat.card (MulAut.characteristic N a).fixedSubgroup ^ 2 = Nat.card N) :
    Function.Surjective (fixedQuotientProjection N a) := by
  intro v
  have hN : ∀ x ∈ N, a x ∈ N := fun x hx => (MulAut.characteristic N a ⟨x,hx⟩).property
  have hinv : Function.Involutive a := fun x => DFunLike.congr_fun ha x
  have heq : (a.toMonoidHom.restrict hN).eqLocus (MonoidHom.id N) =
      (MulAut.characteristic N a).fixedSubgroup := by
    ext x
    rw [mem_fixedSubgroup]
    rfl
  have hquot : QuotientGroup.map N N a.toMonoidHom hN = (quotientAut N a).toMonoidHom := by
    apply QuotientGroup.monoidHom_ext
    ext x
    change QuotientGroup.mk' N (a x) = quotientAut N a (QuotientGroup.mk' N x)
    rw [quotientAut_apply_mk]
  obtain ⟨g,hg,he⟩ := Theory.GroupTheory.exists_fixed_quotient_lift_of_elementary_kernel
    N a.toMonoidHom hinv hN (heq ▸ hc) v.val (by
      rw [hquot]
      change quotientAut N a v.val = v.val
      exact (mem_fixedSubgroup _ _).mp v.property)
  exact ⟨⟨g,(mem_fixedSubgroup _ _).mpr hg⟩, Subtype.ext he⟩

/-- The original quotient map identifies the fixed group modulo its fixed kernel. -/
@[expose] noncomputable def fixedQuotientEquiv [Finite G] [IsElementaryAbelian 2 N]
    (ha : a ^ 2 = 1)
    (hc : Nat.card (MulAut.characteristic N a).fixedSubgroup ^ 2 = Nat.card N) :
    (a.fixedSubgroup ⧸ N.subgroupOf a.fixedSubgroup) ≃* (quotientAut N a).fixedSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq (fixedQuotientProjection_kernel N a).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fixedQuotientProjection_surjective N a ha hc))

end MulAut
