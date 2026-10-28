module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Subgroup.Center
public import Theory.ElementaryAbelian.VectorSpace
/-!
# Conjugation on a commutative internal direct product

The actual multiplication map identifies an abelian subgroup Z=U join F
with U times F when the factors are disjoint. Projection onto U has kernel
exactly F and commutes with conjugation by an element normalizing U and
centralizing F. No global splitting of the ambient group is asserted.

This supports the natural-plus-fixed Z-layer in MS93 (4.1), and the
center-section application of Aschbacher–Smith C.1.34, pp.136–137.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup.CommutativeComplementProjection
variable {G : Type*} [Group G] (Z U F : Subgroup G) [IsMulCommutative Z]
  (hZ : Z = U ⊔ F) (hdis : Disjoint U F)

omit [IsMulCommutative Z] in
include hZ in
theorem u_le : U ≤ Z := hZ.symm ▸ le_sup_left
omit [IsMulCommutative Z] in
include hZ in
theorem f_le : F ≤ Z := hZ.symm ▸ le_sup_right

noncomputable def product : U × F →* Z :=
  (inclusion (u_le Z U F hZ)).coprod (inclusion (f_le Z U F hZ))

@[simp] theorem product_val (x : U × F) :
    (product Z U F hZ x : G) = (x.1 : G) * (x.2 : G) := rfl

include hdis in
theorem product_injective : Function.Injective (product Z U F hZ) := by
  intro x y he
  exact Subgroup.mul_injective_of_disjoint hdis (congrArg Subtype.val he)

theorem product_surjective : Function.Surjective (product Z U F hZ) := by
  intro z
  have htop : U.subgroupOf Z ⊔ F.subgroupOf Z = ⊤ := by
    rw [← subgroupOf_sup (u_le Z U F hZ) (f_le Z U F hZ),← hZ,subgroupOf_self]
  have hz : z ∈ U.subgroupOf Z ⊔ F.subgroupOf Z := htop ▸ mem_top z
  obtain ⟨u,hu,f,hf,he⟩ := Subgroup.mem_sup.mp hz
  refine ⟨(⟨u,hu⟩,⟨f,hf⟩),?_⟩
  exact he

noncomputable def productEquiv : U × F ≃* Z :=
  MulEquiv.ofBijective (product Z U F hZ)
    ⟨product_injective Z U F hZ hdis,product_surjective Z U F hZ⟩

noncomputable def projection : Z →* U :=
  (MonoidHom.fst U F).comp (productEquiv Z U F hZ hdis).symm.toMonoidHom

theorem projection_product (u : U) (f : F) :
    projection Z U F hZ hdis (product Z U F hZ (u,f)) = u := by
  change ((productEquiv Z U F hZ hdis).symm ((productEquiv Z U F hZ hdis) (u,f))).1 = u
  rw [MulEquiv.symm_apply_apply]

theorem projection_kernel : (projection Z U F hZ hdis).ker = F.subgroupOf Z := by
  ext z
  obtain ⟨⟨u,f⟩,rfl⟩ := product_surjective Z U F hZ z
  rw [MonoidHom.mem_ker,projection_product]
  change u = 1 ↔ (u : G) * (f : G) ∈ F
  constructor
  · intro he
    simp only [he,coe_one,one_mul]
    exact f.property
  · intro hf
    have hu : (u : G) ∈ F := by
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using F.mul_mem hf (F.inv_mem f.property)
    apply Subtype.ext
    exact (show U ⊓ F ≤ ⊥ from (disjoint_iff.mp hdis).le) ⟨u.property,hu⟩

theorem projection_conjugate {l : G}
    (hlU : l ∈ normalizer U) (hlF : l ∈ centralizer (F : Set G))
    (z z' : Z) (hz : (z' : G) = l * (z : G) * l⁻¹) :
    (projection Z U F hZ hdis z' : G) =
      l * (projection Z U F hZ hdis z : G) * l⁻¹ := by
  obtain ⟨⟨u,f⟩,rfl⟩ := product_surjective Z U F hZ z
  rw [projection_product]
  let u' : U := ⟨l * (u : G) * l⁻¹,(mem_normalizer_iff.mp hlU u).mp u.property⟩
  have he : z' = product Z U F hZ (u',f) := by
    apply Subtype.ext
    rw [hz,product_val,product_val]
    change l * ((u : G) * (f : G)) * l⁻¹ = (l * (u : G) * l⁻¹) * (f : G)
    have hc := hlF f f.property
    calc
      l * ((u : G) * (f : G)) * l⁻¹ = (l * (u : G) * l⁻¹) * (l * (f : G) * l⁻¹) := by group
      _ = _ := by rw [← hc,mul_inv_cancel_right]
  rw [he,projection_product]
end Subgroup.CommutativeComplementProjection
