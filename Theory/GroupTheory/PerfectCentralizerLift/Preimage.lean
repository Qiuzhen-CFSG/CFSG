module
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.CentralExtensionSections

/-!
# Preimages of perfect subgroups in a central extension

The derived subgroup of the full preimage maps onto a perfect subgroup.
Uniqueness of homomorphisms from a perfect group makes its lifts commute
with any element whose image centralizes that subgroup. Every remaining
lift differs by a central kernel element, giving the same conclusion for
the entire preimage.

This is the centralizer lifting argument of Aschbacher--Smith B.1.11,
printed pp.72--73, used below in the exceptional Ree two-cover calculation.
-/

public section
open Subgroup
namespace PerfectCentralCovering

/-- Every preimage of an element of a perfect subgroup commutes with every
preimage of an element centralizing that subgroup in a central extension. -/
theorem commute_of_centralizing_image_of_perfect
    {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (S : Subgroup G) [Group.IsPerfect S]
    (x y : E) (hx : f x ∈ centralizer (S : Set G)) (hy : f y ∈ S) :
    Commute x y := by
  let g := f.subgroupComap S
  have hgk : g.ker ≤ center (S.comap f) := by
    intro a ha
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact mem_center_iff.mp (hk (congrArg Subtype.val (MonoidHom.mem_ker.mp ha))) b
  let c := CentralExtension.derivedCover g
    (f.subgroupComap_surjective_of_surjective S hf) hgk
  let j : commutator (S.comap f) →* E :=
    (S.comap f).subtype.comp (commutator (S.comap f)).subtype
  let : Group.IsPerfect (commutator (S.comap f)) := c.isPerfect
  have hj (a : commutator (S.comap f)) : f (j a) ∈ S := a.val.property
  have he : (MulAut.conj x).toMonoidHom.comp j = j := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq f hk
    apply MonoidHom.ext
    intro a
    change f (x * j a * x⁻¹) = f (j a)
    rw [map_mul, map_mul, map_inv]
    have hc : f x * f (j a) = f (j a) * f x :=
      (mem_centralizer_iff.mp hx _ (hj a)).symm
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨a,ha⟩ := c.surjective ⟨f y,hy⟩
  have ha' : f (j a) = f y := congrArg Subtype.val ha
  have hker : y * (j a)⁻¹ ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha', mul_inv_cancel])
  have hcomm : Commute x (j a) := by
    have h := DFunLike.congr_fun he a
    change x * j a * x⁻¹ = j a at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hcomm' : Commute x (y * (j a)⁻¹) := mem_center_iff.mp hker x
  simpa only [inv_mul_cancel_right] using hcomm'.mul_right hcomm
end PerfectCentralCovering
