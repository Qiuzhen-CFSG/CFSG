module
public import Theory.Representation.NormalElementaryQuotient.Thompson
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Thompson normality from a model of a supplement

Two surjections with the same kernel identify their quotient actors, and
an equivariant linear equivalence transports the FF property. Apply this
to a subgroup supplementing the centralizer of a normal elementary group.
If the centralizer is a two-group and the model is not FF, the actual
Sylow Thompson subgroup is normal. No full-actor marking is assumed.

Source: Aschbacher–Smith B.2.5–8, printed p.76; used in 13.4.7, pp.900–901.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
namespace Representation.BinaryOffender
variable {A H D M N : Type*} [Group A] [Group H] [Group D]
  [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup N] [Module (ZMod 2) N]

/-- Equal quotient kernels transport the FF obstruction between the actual actors. -/
theorem nonFF_of_common_quotient (f : A →* H) (hf : Function.Surjective f)
    (q : A →* D) (hq : Function.Surjective q) (hk : q.ker = f.ker)
    (σ : Representation (ZMod 2) H M) (τ : Representation (ZMod 2) D N)
    (E : Representation.Equiv (σ.comp f) (τ.comp q)) (hn : ¬ IsFFModule σ) :
    ¬ IsFFModule τ := by
  let a := QuotientGroup.quotientKerEquivOfSurjective q hq
  let b := (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let r := a.symm.trans b
  have hr (c : A) : r (q c) = f c := by
    change b (a.symm (q c)) = f c
    rw [show q c = a (QuotientGroup.mk c) from rfl,a.symm_apply_apply]
    rfl
  intro h
  apply hn
  apply h.map_equivariant τ σ r.toMonoidHom r.injective E.symm.toLinearEquiv
  intro d v
  obtain ⟨c,rfl⟩ := hq d
  apply E.toLinearEquiv.injective
  change E (E.symm (τ (q c) v)) = E (σ (r (q c)) (E.symm v))
  rw [hr,E.apply_symm_apply]
  have he := LinearMap.congr_fun (E.isIntertwining' c) (E.symm v)
  simpa only [MonoidHom.comp_apply,LinearMap.comp_apply,Representation.Equiv.coe_toLinearMap,
    E.apply_symm_apply] using he.symm
end Representation.BinaryOffender

open scoped IsMulCommutative
open Stellmacher
namespace Representation.NormalElementaryQuotient
variable {A H M : Type*} [Group A] [Finite A] [Group H]
  [AddCommGroup M] [Module (ZMod 2) M]

/-- A non-FF model of a centralizer supplement forces Thompson normality. -/
theorem thompson_normal_of_component_model
    (S : Sylow 2 A) (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E]
    (C : Subgroup A) (hgen : C ⊔ centralizer (E : Set A) = ⊤)
    (hcore : IsPGroup 2 (centralizer (E : Set A)))
    (f : C →* H) (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (E : Set A)).subgroupOf C)
    (σ : Representation (ZMod 2) H M) (e : M ≃ₗ[ZMod 2] Additive E)
    (he : ∀ (c : C) (v : M), e (σ (f c) v) =
      Additive.ofMul (MulAut.conjNormal c.val (e v).toMul))
    (hn : ¬ IsFFModule σ) : (elementaryAbelianMaxJ (S : Subgroup A)).Normal := by
  let N := centralizer (E : Set A)
  let q := QuotientGroup.mk' N
  let τ := representation E q (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
  let qC := q.comp C.subtype
  have hqC : Function.Surjective qC := by
    intro d
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective N d
    obtain ⟨c,hc,n,hn,hcn⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top a)
    refine ⟨⟨c,hc⟩,?_⟩
    change q c = q a
    rw [←hcn,map_mul,show q n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,mul_one]
  have hk : qC.ker = f.ker := by
    rw [hker,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    rfl
  let eC : Representation.Equiv (σ.comp f) (τ.comp qC) := {
    toLinearEquiv := e
    isIntertwining' c := by
      apply LinearMap.ext
      intro v
      change e (σ (f c) v) = τ (q c.val) (e v)
      rw [he]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (representation_apply E q _ _ c.val (e v)).symm }
  apply thompson_normal_of_nonFF S E q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
    (by rw [QuotientGroup.ker_mk']; exact hcore)
    ((IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal S)
  exact nonFF_of_common_quotient f hf qC hqC hk σ τ eC hn
end Representation.NormalElementaryQuotient
