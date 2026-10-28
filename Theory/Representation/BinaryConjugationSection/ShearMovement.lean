module
public import Theory.Representation.BinaryConjugationSection.InvariantImages

/-!
# Detecting quotient movement through a second section

Two literal binary sections overlap on a subgroup S. On the second section,
one actor fixes the image of S while its displacement on the image moved by
another actor recovers the original vector. If S has a nonzero image in that
section, the first actor's translate of S cannot have the same image in the
first section, provided its kernel on S lies in the second section's kernel.

The proof compares the two coordinate images of the actual conjugation
commutators. It uses no kernel containment outside S and does not require the
whole ambient subgroup to be elementary abelian. This supplies the quotient
movement step in the natural second-tensor row of Aschbacher–Smith 13.8.30,
*The Classification of Quasithin Groups*, printed p.964.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W Z : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  {H A N J B U : Subgroup G}
  {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) J Z}
  (q : BinaryConjugationSection H A N ρ)
  (p : BinaryConjugationSection J B U σ)

private def conjugated {T C D : Subgroup G} {Y : Type*}
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) T Y} (d : BinaryConjugationSection T C D τ)
    (a : T) (x : C) : C :=
  ⟨a * x * (a : G)⁻¹, (mem_normalizer_iff.mp (d.normalized a.property) x).mp x.property⟩

private theorem displacement_coordinates {T C D : Subgroup G} {Y : Type*}
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) T Y} (d : BinaryConjugationSection T C D τ)
    (a : T) (x : C) :
    (d.coordinates (conjugated d a x * x⁻¹)).toAdd =
      τ a (d.coordinates x).toAdd - (d.coordinates x).toAdd := by
  rw [map_mul, map_inv]
  change (d.coordinates (conjugated d a x)).toAdd + -(d.coordinates x).toAdd = _
  rw [show (d.coordinates (conjugated d a x)).toAdd = _ from d.equivariant a x]
  exact (sub_eq_add_neg _ _).symm

/-- A shear on a second literal section forces movement even after quotienting
by a kernel known only on the original span. -/
theorem image_moved_of_section_shear
    (S : Subgroup G) (hSA : S ≤ A) (hSB : S ≤ B) (hUS : U ≤ S)
    (hkernel : S ⊓ N ≤ U) (hproper : ¬ S ≤ U)
    (a b : H) (ha : (a : G) ∈ J) (hb : (b : G) ∈ J)
    (hfix : ∀ w ∈ p.imageSpace S, σ ⟨b,hb⟩ w = w)
    (hshear : ∀ w ∈ p.imageSpace S,
      σ ⟨b,hb⟩ (σ ⟨a,ha⟩ w) - σ ⟨a,ha⟩ w = w) :
    ∃ w ∈ q.imageSpace S, ρ a w ∉ q.imageSpace S := by
  classical
  by_contra h
  push Not at h
  apply hproper
  intro x hx
  let xA : A := ⟨x,hSA hx⟩
  let xB : B := ⟨x,hSB hx⟩
  have hxq : (q.coordinates xA).toAdd ∈ q.imageSpace S :=
    (q.mem_imageSpace_iff S _).mpr ⟨xA,hx,rfl⟩
  have hxp : (p.coordinates xB).toAdd ∈ p.imageSpace S :=
    (p.mem_imageSpace_iff S _).mpr ⟨xB,hx,rfl⟩
  obtain ⟨y,hy,he⟩ := (q.mem_imageSpace_iff S _).mp (h _ hxq)
  let yB : B := ⟨y,hSB hy⟩
  let axA := conjugated q a xA
  let axB := conjugated p ⟨a,ha⟩ xB
  let zA := conjugated q b axA * axA⁻¹
  let zB := conjugated p ⟨b,hb⟩ axB * axB⁻¹
  let cA := conjugated q b y * y⁻¹
  let cB := conjugated p ⟨b,hb⟩ yB * yB⁻¹
  have hcU : (cA : G) ∈ U := by
    change (cB : G) ∈ U
    apply (p.coordinates_eq_one_iff cB).mp
    apply Multiplicative.toAdd.injective
    change (p.coordinates cB).toAdd = 0
    rw [displacement_coordinates, hfix _ ((p.mem_imageSpace_iff S _).mpr ⟨yB,hy,rfl⟩), sub_self]
  have hez : (q.coordinates zA).toAdd = (q.coordinates cA).toAdd := by
    rw [displacement_coordinates, displacement_coordinates]
    rw [show (q.coordinates axA).toAdd = _ from q.equivariant a xA, he]
  have hpz : (p.coordinates zB).toAdd = (p.coordinates xB).toAdd := by
    rw [displacement_coordinates]
    rw [show (p.coordinates axB).toAdd = _ from p.equivariant ⟨a,ha⟩ xB]
    exact hshear _ hxp
  have hzU : ((zA * xA⁻¹ : A) : G) ∈ U := by
    change ((zB * xB⁻¹ : B) : G) ∈ U
    apply (p.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, Multiplicative.toAdd.injective hpz, mul_inv_cancel]
  have hximage : (q.coordinates xA).toAdd ∈ q.imageSpace U := by
    have hzimage : (q.coordinates zA).toAdd ∈ q.imageSpace U := by
      rw [hez]
      exact (q.mem_imageSpace_iff U _).mpr ⟨cA,hcU,rfl⟩
    have hdiff : (q.coordinates zA).toAdd - (q.coordinates xA).toAdd ∈ q.imageSpace U := by
      have hh := (q.mem_imageSpace_iff U _).mpr ⟨zA * xA⁻¹,hzU,rfl⟩
      rw [map_mul, map_inv] at hh
      change (q.coordinates zA).toAdd + -(q.coordinates xA).toAdd ∈ q.imageSpace U at hh
      simpa only [sub_eq_add_neg] using hh
    simpa only [sub_sub_cancel] using (q.imageSpace U).sub_mem hzimage hdiff
  obtain ⟨u,hu,heu⟩ := (q.mem_imageSpace_iff U _).mp hximage
  have hn : ((u⁻¹ * xA : A) : G) ∈ N := by
    apply (q.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, Multiplicative.toAdd.injective heu, inv_mul_cancel]
  have hs : ((u⁻¹ * xA : A) : G) ∈ S := S.mul_mem (S.inv_mem (hUS hu)) hx
  have hk := hkernel ⟨hs,hn⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using U.mul_mem hu hk

end Representation.BinaryConjugationSection
