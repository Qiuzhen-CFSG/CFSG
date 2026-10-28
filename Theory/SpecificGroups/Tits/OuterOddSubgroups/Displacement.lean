module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.LocalAction

/-!
# Parabolic overlaps control pointwise Sylow fixation

If an automorphism fixes S pointwise, then r⁻¹α(r) centralizes the elements
x of S for which r x r⁻¹ also lies in S. Intrinsic parabolic preservation
places this displacement in the corresponding parabolic. If that relative
centralizer lies in S, displacement is a homomorphism on the pointwise fixer.

The two reflection displacements jointly determine an automorphism, since
S and the two reflections generate the group. Thus the two relative
centralizer bounds embed the restriction kernel into S × S, proving that
it is a two-group. The two concrete centralizer bounds are explicit premises;
this module does not assert their certification or the final outer bound.

Source: Parrott (1972), p.683, and the local route to Aschbacher–Smith's
outer-group inspection on printed p.510; compare GLS3, 2.5.15.
-/

@[expose] public section
namespace Tits.OuterOddSubgroups
open Subgroup ExceptionalParabolics

/-- The elements of S whose conjugates by r also belong to S. -/
def reflectionOverlap (r : Atlas1600Group) : Subgroup Atlas1600Group :=
  atlas1600SylowTwoSubgroup ⊓
    atlas1600SylowTwoSubgroup.comap (MulAut.conj r).toMonoidHom

/-- A kernel element fixes each element of the marked Sylow subgroup. -/
theorem kernel_fixes_sylow (a : sylowRestriction.ker) {x : Atlas1600Group}
    (hx : x ∈ atlas1600SylowTwoSubgroup) : (a.val : MulAut Atlas1600Group) x = x :=
  (mem_sylowRestriction_ker_iff a.val).mp a.property x hx

/-- Pointwise fixation puts each reflection displacement in the overlap centralizer. -/
theorem displacement_mem_centralizer (a : sylowRestriction.ker) (r : Atlas1600Group) :
    r⁻¹ * (a.val : MulAut Atlas1600Group) r ∈
      centralizer (reflectionOverlap r : Set Atlas1600Group) := by
  intro x hx
  have hconj := kernel_fixes_sylow a hx.2
  change (a.val : MulAut Atlas1600Group) (r * x * r⁻¹) = r * x * r⁻¹ at hconj
  have he := congrArg (fun z : Atlas1600Group =>
    r⁻¹ * z * (a.val : MulAut Atlas1600Group) r) hconj
  simpa only [MulAut.conj_apply, map_mul, map_inv, kernel_fixes_sylow a hx.1,
    mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using he.symm

private theorem displacement_mem_sylow (P : Subgroup Atlas1600Group)
    (r : Atlas1600Group) (hr : r ∈ P)
    (hP : ∀ a : sylowStabilizer, P.map a.val.toMonoidHom = P)
    (hc : P ⊓ centralizer (reflectionOverlap r : Set Atlas1600Group) ≤ S)
    (a : sylowRestriction.ker) : r⁻¹ * (a.val : MulAut Atlas1600Group) r ∈ S := by
  apply hc
  refine ⟨P.mul_mem (P.inv_mem hr) ?_, displacement_mem_centralizer a r⟩
  rw [← hP a.val]
  exact mem_map_of_mem a.val.val.toMonoidHom hr

private def displacementHom (r : Atlas1600Group)
    (h : ∀ a : sylowRestriction.ker, r⁻¹ * (a.val : MulAut Atlas1600Group) r ∈ S) :
    sylowRestriction.ker →* S where
  toFun a := ⟨r⁻¹ * (a.val : MulAut Atlas1600Group) r, h a⟩
  map_one' := by apply Subtype.ext; exact inv_mul_cancel r
  map_mul' a b := by
    apply Subtype.ext
    change r⁻¹ * (a.val : MulAut Atlas1600Group) ((b.val : MulAut Atlas1600Group) r) =
      (r⁻¹ * (a.val : MulAut Atlas1600Group) r) *
        (r⁻¹ * (b.val : MulAut Atlas1600Group) r)
    have hf := kernel_fixes_sylow a (h b)
    rw [map_mul, map_inv] at hf
    rw [inv_mul_eq_iff_eq_mul] at hf
    rw [hf, mul_assoc]

/-- The two overlap-centralizer containments force a two-group restriction kernel. -/
theorem kernel_isPGroup_of_overlap_centralizers
    (hfirst : first ⊓ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r1) : Set Atlas1600Group) ≤ S)
    (hsecond : second ⊓ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r8) : Set Atlas1600Group) ≤ S) :
    IsPGroup 2 sylowRestriction.ker := by
  let d1 := displacementHom (atlas1600ParrottAssignment .r1)
    (displacement_mem_sylow first _ reflection_mem_first preserves_first hfirst)
  let d8 := displacementHom (atlas1600ParrottAssignment .r8)
    (displacement_mem_sylow second _ reflection_mem_second preserves_second hsecond)
  let d := d1.prod d8
  have hd : Function.Injective d := by
    intro a b hab
    have h1 : (a.val : MulAut Atlas1600Group) (atlas1600ParrottAssignment .r1) =
        (b.val : MulAut Atlas1600Group) (atlas1600ParrottAssignment .r1) := by
      exact mul_left_cancel (congrArg Subtype.val (congrArg Prod.fst hab))
    have h8 : (a.val : MulAut Atlas1600Group) (atlas1600ParrottAssignment .r8) =
        (b.val : MulAut Atlas1600Group) (atlas1600ParrottAssignment .r8) := by
      exact mul_left_cancel (congrArg Subtype.val (congrArg Prod.snd hab))
    let E := a.val.val.toMonoidHom.eqLocus b.val.val.toMonoidHom
    have hS : S ≤ E := by
      intro x hx
      exact (kernel_fixes_sylow a hx).trans (kernel_fixes_sylow b hx).symm
    have hr1 : closure {atlas1600ParrottAssignment .r1} ≤ E :=
      (closure_le _).mpr (by rintro x (rfl : x = _); exact h1)
    have hr8 : closure {atlas1600ParrottAssignment .r8} ≤ E :=
      (closure_le _).mpr (by rintro x (rfl : x = _); exact h8)
    have ht : (⊤ : Subgroup Atlas1600Group) ≤ E := by
      rw [← ExceptionalParabolics.generate]
      exact sup_le (sup_le hS hr1) (sup_le hS hr8)
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact ht (mem_top x)
  have hp : IsPGroup 2 (S × S) :=
    IsPGroup.of_card (n := 22) (by rw [Nat.card_prod, sylow_card]; norm_num)
  exact hp.of_injective d hd

end Tits.OuterOddSubgroups
end
