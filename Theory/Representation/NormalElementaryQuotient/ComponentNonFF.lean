module
public import Theory.Representation.NormalElementaryQuotient.ComponentModel

/-!
# The faithful action of a marked component supplement

A model of a subgroup supplementing the literal module centralizer identifies
the full faithful action through their common quotient. The non-FF obstruction
therefore holds for the whole quotient, without any condition on the kernel.
This exposes the action fact needed for the sharp near-maximum comparison in
Aschbacher–Smith 13.4.7(2), printed p.902.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {A H M : Type*} [Group A] [Group H]
  [AddCommGroup M] [Module (ZMod 2) M]

/-- A non-FF component model supplies the non-FF faithful action of its supplement. -/
theorem nonFF_of_component_model
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E]
    (C : Subgroup A) (hgen : C ⊔ centralizer (E : Set A) = ⊤)
    (f : C →* H) (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (E : Set A)).subgroupOf C)
    (σ : Representation (ZMod 2) H M) (e : M ≃ₗ[ZMod 2] Additive E)
    (he : ∀ (c : C) (v : M), e (σ (f c) v) =
      Additive.ofMul (MulAut.conjNormal c.val (e v).toMul))
    (hn : ¬ IsFFModule σ) :
    let N := centralizer (E : Set A)
    ¬ IsFFModule (representation E (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)) := by
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
  exact nonFF_of_common_quotient f hf qC hqC hk σ τ eC hn
end Representation.NormalElementaryQuotient
