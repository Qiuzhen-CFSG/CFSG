module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Elementary subgroup images in an exact kernel quotient

If a surjective group homomorphism has kernel N and the image of a subgroup
R is elementary abelian at p, then the image of R in the literal quotient
G/N is elementary abelian at p. The first isomorphism theorem identifies
the two images; transport by its inverse proves the assertion.

This keeps a faithful action's residual image and the ordinary two-core
quotient compatible in Stellmacher (9.8), printed p.55. Only general
quotient and elementary-group APIs are used here.
-/

namespace Subgroup

public theorem elementary_quotient_image_of_exact_kernel
    {G X : Type*} [Group G] [Group X] {p : ℕ} [Fact p.Prime]
    (R N : Subgroup G) [N.Normal]
    (f : G →* X) (hf : Function.Surjective f) (hker : f.ker = N)
    (hR : IsElementaryAbelian p (R.map f)) :
    IsElementaryAbelian p (R.map (QuotientGroup.mk' N)) := by
  let q := QuotientGroup.mk' N
  let e : (G ⧸ N) ≃* X := QuotientGroup.liftEquiv N hf hker.symm
  have hcomp : e.toMonoidHom.comp q = f := rfl
  have hmap : (R.map q).map e.toMonoidHom = R.map f := by
    rw [map_map,hcomp]
  let _ : IsElementaryAbelian p ((R.map q).map e.toMonoidHom) := hmap.symm ▸ hR
  have hback := IsElementaryAbelian.map (p := p) e.symm.toMonoidHom (A := (R.map q).map e.toMonoidHom)
  have hinverse : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id (G ⧸ N) := by
    ext point
    exact e.symm_apply_apply point
  rw [map_map,hinverse,map_id] at hback
  exact hback

end Subgroup
