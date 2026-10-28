module
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.ZMod

/-!
# Comparing overlapping literal binary sections

For two section maps on a common subgroup D, quotient the first coordinate
space by the image of the second kernel. The resulting map factors uniquely
through the second image of D. Its kernel is precisely the second image of
the first kernel intersected with D. The construction retains the coordinate
maps element by element and intertwines every common normalizing actor.
On a slice whose first kernel lies in the second kernel it is injective.

This supplies the common quotient used to compare both second tensor rows
with the same maximal quotient in Aschbacher--Smith, The Classification of
Quasithin Groups, 13.8.30, printed p.964. It does not assert that a moved
subgroup remains moved after passage to an arbitrary quotient.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G W Z : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  {H A N J B U : Subgroup G}
  {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) J Z}
  (q : BinaryConjugationSection H A N ρ)
  (p : BinaryConjugationSection J B U σ)
  (D : Subgroup G) (hDA : D ≤ A) (hDB : D ≤ B)

/-- Compare two literal sections after quotienting the first image by the
second kernel. The map is specified on every original group element. -/
theorem exists_image_quotient_comparison :
    ∃ f : p.imageSpace D →ₗ[ZMod 2] W ⧸ q.imageSpace U,
      ∀ x : D, f ⟨(p.coordinates (inclusion hDB x)).toAdd,
        (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB x,x.property,rfl⟩⟩ =
          (q.imageSpace U).mkQ (q.coordinates (inclusion hDA x)).toAdd := by
  let a : D →* Multiplicative (p.imageSpace D) := {
    toFun x := Multiplicative.ofAdd ⟨(p.coordinates (inclusion hDB x)).toAdd,
      (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB x,x.property,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one _)
    map_mul' x y := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (map_mul p.coordinates (inclusion hDB x) (inclusion hDB y)) }
  have ha : Function.Surjective a := by
    intro w
    obtain ⟨x,hx,he⟩ := (p.mem_imageSpace_iff D w.toAdd.val).mp w.toAdd.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let b : D →* Multiplicative (W ⧸ q.imageSpace U) :=
    (q.imageSpace U).mkQ.toAddMonoidHom.toMultiplicative.comp
      (q.coordinates.comp (inclusion hDA))
  have hab : a.ker ≤ b.ker := by
    intro x hx
    have hx0 : p.coordinates (inclusion hDB x) = 1 := by
      exact congrArg (fun w : Multiplicative (p.imageSpace D) => Multiplicative.ofAdd w.toAdd.val) hx
    have hxU := (p.coordinates_eq_one_iff _).mp hx0
    change (q.imageSpace U).mkQ (q.coordinates (inclusion hDA x)).toAdd = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((q.mem_imageSpace_iff U _).mpr ⟨inclusion hDA x,hxU,rfl⟩)
  let f := a.liftOfSurjective ha ⟨b,hab⟩
  refine ⟨(AddMonoidHom.toMultiplicative.symm f).toZModLinearMap 2,?_⟩
  intro x
  exact congrArg Multiplicative.toAdd
    (a.liftOfRightInverse_comp_apply (Function.surjInv ha)
      (Function.rightInverse_surjInv ha) ⟨b,hab⟩ x)

variable (f : p.imageSpace D →ₗ[ZMod 2] W ⧸ q.imageSpace U)
  (hf : ∀ x : D, f ⟨(p.coordinates (inclusion hDB x)).toAdd,
    (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB x,x.property,rfl⟩⟩ =
      (q.imageSpace U).mkQ (q.coordinates (inclusion hDA x)).toAdd)

include hf in
/-- The comparison kernel is exactly the second image of the first kernel
inside D. No containment of the first kernel in the second is assumed. -/
theorem image_quotient_comparison_kernel (hUD : U ≤ D) :
    LinearMap.ker f = (p.imageSpace (D ⊓ N)).comap (p.imageSpace D).subtype := by
  ext w
  obtain ⟨x,hx,he⟩ := (p.mem_imageSpace_iff D w.val).mp w.property
  let xD : D := ⟨x,hx⟩
  have hxw : (⟨(p.coordinates (inclusion hDB xD)).toAdd,
      (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB xD,hx,rfl⟩⟩ : p.imageSpace D) = w :=
    Subtype.ext he
  constructor
  · intro hw
    have hq : (q.coordinates (inclusion hDA xD)).toAdd ∈ q.imageSpace U := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (q.imageSpace U).mkQ (q.coordinates (inclusion hDA xD)).toAdd = 0
      rw [←hf xD,hxw]
      exact hw
    obtain ⟨u,hu,heu⟩ := (q.mem_imageSpace_iff U _).mp hq
    let y : B := ⟨(u:G)⁻¹ * (x:G),B.mul_mem (B.inv_mem (hDB (hUD hu))) x.property⟩
    have hyD : (y:G) ∈ D := D.mul_mem (D.inv_mem (hUD hu)) hx
    have hyN : (y:G) ∈ N := by
      apply (q.coordinates_eq_one_iff (u⁻¹ * inclusion hDA xD)).mp
      rw [map_mul,map_inv,Multiplicative.toAdd.injective heu,inv_mul_cancel]
    have hu1 : p.coordinates ⟨u,hDB (hUD hu)⟩ = 1 :=
      (p.coordinates_eq_one_iff _).mpr hu
    refine (p.mem_imageSpace_iff (D ⊓ N) _).mpr ⟨y,⟨hyD,hyN⟩,?_⟩
    change (p.coordinates ((⟨u,hDB (hUD hu)⟩ : B)⁻¹ * x)).toAdd = w.val
    rw [map_mul,map_inv,hu1,inv_one,one_mul]
    exact he
  · intro hw
    obtain ⟨y,hy,hey⟩ := (p.mem_imageSpace_iff (D ⊓ N) w.val).mp hw
    let yD : D := ⟨y,hy.1⟩
    have hyw : (⟨(p.coordinates (inclusion hDB yD)).toAdd,
      (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB yD,hy.1,rfl⟩⟩ : p.imageSpace D) = w :=
      Subtype.ext hey
    change f w = 0
    rw [←hyw,hf]
    have hy1 := (q.coordinates_eq_one_iff (inclusion hDA yD)).mpr hy.2
    rw [hy1]
    exact map_zero _

include hf in
/-- A full first coordinate image makes the comparison surjective. -/
theorem image_quotient_comparison_surjective (hD : q.imageSpace D = ⊤) :
    Function.Surjective f := by
  intro w
  obtain ⟨v,rfl⟩ := (q.imageSpace U).mkQ_surjective w
  obtain ⟨x,hx,he⟩ := (q.mem_imageSpace_iff D v).mp (hD ▸ Submodule.mem_top)
  let xD : D := ⟨x,hx⟩
  refine ⟨⟨(p.coordinates (inclusion hDB xD)).toAdd,
    (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB xD,hx,rfl⟩⟩,?_⟩
  rw [hf]
  exact congrArg (q.imageSpace U).mkQ he

include hf in
/-- The comparison has no kernel on a slice whose original kernel lies in U. -/
theorem image_quotient_comparison_injective_on_slice
    (hUD : U ≤ D) (S : Subgroup G) (hUS : U ≤ S) (hSN : S ⊓ N ≤ U)
    (w : p.imageSpace D) (hw : w.val ∈ p.imageSpace S) (hz : f w = 0) : w = 0 := by
  have hk : w ∈ LinearMap.ker f := hz
  rw [image_quotient_comparison_kernel q p D hDA hDB f hf hUD] at hk
  obtain ⟨x,hx,he⟩ := (p.mem_imageSpace_iff (D ⊓ N) w.val).mp hk
  have hxS : (x:G) ∈ S :=
    (p.coordinates_mem_imageSpace_iff_of_kernel_le S hUS x).mp (he.symm ▸ hw)
  have hx1 := (p.coordinates_eq_one_iff x).mpr (hSN ⟨hxS,hx.2⟩)
  apply Subtype.ext
  exact he.symm.trans (congrArg Multiplicative.toAdd hx1)

include hf in
/-- The same actor acts compatibly on the two images and their comparison.
All normalization is relative to the specified original subgroups. -/
theorem image_quotient_comparison_equivariant
    (a : H) (ha : (a:G) ∈ J) (haD : (a:G) ∈ normalizer D)
    (haU : (a:G) ∈ normalizer U) (w : p.imageSpace D) :
    f ⟨σ ⟨a,ha⟩ w, p.imageSpace_apply_mem D ⟨a,ha⟩ haD w w.property⟩ =
      (q.imageSpace U).mapQ (q.imageSpace U) (ρ a)
        (fun v hv => q.imageSpace_apply_mem U a haU v hv) (f w) := by
  obtain ⟨x,hx,he⟩ := (p.mem_imageSpace_iff D w.val).mp w.property
  let xD : D := ⟨x,hx⟩
  let yD : D := ⟨a * x * (a:G)⁻¹,(mem_normalizer_iff.mp haD x).mp hx⟩
  have hxw : (⟨(p.coordinates (inclusion hDB xD)).toAdd,
    (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB xD,hx,rfl⟩⟩ : p.imageSpace D) = w :=
    Subtype.ext he
  have hyw : (⟨(p.coordinates (inclusion hDB yD)).toAdd,
    (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB yD,yD.property,rfl⟩⟩ : p.imageSpace D) =
      ⟨σ ⟨a,ha⟩ w,p.imageSpace_apply_mem D ⟨a,ha⟩ haD w w.property⟩ := by
    apply Subtype.ext
    exact (p.equivariant ⟨a,ha⟩ (inclusion hDB xD)).trans (congrArg (σ ⟨a,ha⟩) he)
  rw [←hyw,hf,←hxw,hf]
  exact congrArg (q.imageSpace U).mkQ (q.equivariant a (inclusion hDA xD))

end Representation.BinaryConjugationSection
