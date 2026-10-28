module

public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Faithful automorphism actions on perfect central quotients

An automorphism of a perfect group which is trivial modulo the center is
trivial. Indeed, its displacement `x⁻¹ * a(x)` is a homomorphism into the
abelian center, so it kills every commutator and hence the whole group.
Consequently the genuine quotient action embeds Aut(G) into Aut(G/Z(G));
innerness can also be detected there, by lifting a conjugating element.

This is the transport needed for the quasisimple component in GLS, Volume 2,
Theorem 26.24, Step 5. No finiteness or simplicity hypothesis is required.
-/

namespace MulAut
open scoped IsMulCommutative

variable {G H : Type*} [Group G] [Group H]

/-- Central displacement forces an automorphism of a perfect group to be trivial. -/
public theorem eq_one_of_central_displacement [Group.IsPerfect G]
    (a : MulAut G) (ha : ∀ x, x⁻¹ * a x ∈ Subgroup.center G) : a = 1 := by
  let d : G →* Subgroup.center G := {
    toFun x := ⟨x⁻¹ * a x, ha x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change (x * y)⁻¹ * a (x * y) = (x⁻¹ * a x) * (y⁻¹ * a y)
      rw [mul_inv_rev, map_mul]
      have hc := Subgroup.mem_center_iff.mp (ha x) y⁻¹
      calc
        y⁻¹ * x⁻¹ * (a x * a y) = (y⁻¹ * (x⁻¹ * a x)) * a y := by group
        _ = ((x⁻¹ * a x) * y⁻¹) * a y := by rw [hc]
        _ = _ := by group }
  have hd (x : G) : d x = 1 :=
    Abelianization.commutator_subset_ker d Group.IsPerfect.mem_commutator
  ext x
  have hx := congrArg Subtype.val (hd x)
  change x⁻¹ * a x = 1 at hx
  exact (inv_mul_eq_one.mp hx).symm

/-- The action on the actual central quotient is faithful for a perfect group. -/
public theorem quotient_center_injective [Group.IsPerfect G] :
    Function.Injective (Subgroup.quotientAut (Subgroup.center G)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro a ha
  apply eq_one_of_central_displacement a
  intro x
  have hx := DFunLike.congr_fun ha (QuotientGroup.mk' (Subgroup.center G) x)
  rw [Subgroup.quotientAut_apply_mk] at hx
  apply QuotientGroup.eq.mp
  simpa only [MulAut.one_apply, QuotientGroup.mk'_apply] using hx.symm

/-- Transport the genuine quotient action to a specified model. -/
@[expose] public def centralQuotientAction (e : G ⧸ Subgroup.center G ≃* H) :
    MulAut G →* MulAut H :=
  (MulAut.congr e).toMonoidHom.comp (Subgroup.quotientAut (Subgroup.center G))

public theorem centralQuotientAction_apply (e : G ⧸ Subgroup.center G ≃* H)
    (a : MulAut G) (x : G) :
    centralQuotientAction e a (e (QuotientGroup.mk' (Subgroup.center G) x)) =
      e (QuotientGroup.mk' (Subgroup.center G) (a x)) := by
  change e (Subgroup.quotientAut (Subgroup.center G) a
    (e.symm (e (QuotientGroup.mk' (Subgroup.center G) x)))) = _
  rw [e.symm_apply_apply, Subgroup.quotientAut_apply_mk]

public theorem centralQuotientAction_injective [Group.IsPerfect G]
    (e : G ⧸ Subgroup.center G ≃* H) :
    Function.Injective (centralQuotientAction e) :=
  (MulAut.congr e).injective.comp quotient_center_injective

public theorem centralQuotientAction_conj (e : G ⧸ Subgroup.center G ≃* H) (x : G) :
    centralQuotientAction e (MulAut.conj x) =
      MulAut.conj (e (QuotientGroup.mk' (Subgroup.center G) x)) := by
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) z
  rw [centralQuotientAction_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

/-- For a perfect group, an automorphism is inner exactly when its quotient
action is inner. -/
public theorem centralQuotientAction_inner_iff [Group.IsPerfect G]
    (e : G ⧸ Subgroup.center G ≃* H) (a : MulAut G) :
    (∃ y : H, centralQuotientAction e a = MulAut.conj y) ↔
      ∃ x : G, a = MulAut.conj x := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) z
    refine ⟨x, centralQuotientAction_injective e ?_⟩
    rw [centralQuotientAction_conj, hy]
  · rintro ⟨x, rfl⟩
    exact ⟨e (QuotientGroup.mk' (Subgroup.center G) x), centralQuotientAction_conj e x⟩

/-- Faithfulness of an action on a perfect group survives the central quotient. -/
public theorem centralQuotientAction_comp_injective [Group.IsPerfect G]
    {A : Type*} [Group A] (e : G ⧸ Subgroup.center G ≃* H)
    (ρ : A →* MulAut G) (hρ : Function.Injective ρ) :
    Function.Injective ((centralQuotientAction e).comp ρ) :=
  (centralQuotientAction_injective e).comp hρ

end MulAut
