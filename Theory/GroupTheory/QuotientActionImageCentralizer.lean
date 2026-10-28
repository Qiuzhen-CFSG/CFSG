module
public import Theory.GroupTheory.NormalizerQuotientInner

/-!
# Centralizers in an image of a quotient action

Let K be normalized by J, and let f map J onto X. If the restriction of f
to K has kernel N, then K/N is the literal image of K in X. Equivariance
under conjugation identifies the image of the kernel of J's action on K/N
with the centralizer of this image of K.

This retains both original homomorphisms, rather than replacing either
quotient action by an abstract isomorphic action. The source application is
Aschbacher--Smith 5.1.23, printed p.645 of `refs/quasithin.pdf`.
-/

public noncomputable section

open Subgroup
namespace Subgroup
variable {G X : Type*} [Group G] [Group X]

theorem quotient_action_kernel_map_eq_centralizer
    (J K : Subgroup G) (hKJ : K ≤ J) (hJN : J ≤ normalizer (K : Set G))
    (N : Subgroup K) [N.Characteristic] (f : J →* X) (hf : Function.Surjective f)
    (hk : (f.comp (inclusion hKJ)).ker = N) :
    (((normalizerQuotientAction K N).comp (inclusion hJN)).ker).map f =
      centralizer (((K.subgroupOf J).map f) : Set X) := by
  let a := (normalizerQuotientAction K N).comp (inclusion hJN)
  let fK := f.comp (inclusion hKJ)
  have heq (u v : K) : QuotientGroup.mk' N u = QuotientGroup.mk' N v ↔ fK u = fK v := by
    change (u : K ⧸ N) = (v : K ⧸ N) ↔ fK u = fK v
    rw [QuotientGroup.eq_iff_div_mem, ← hk]
    change fK (u / v) = 1 ↔ fK u = fK v
    rw [map_div, div_eq_one]
  have hconj (x : J) (k : K) :
      fK (K.normalizerMonoidHom (inclusion hJN x) k) = f x * fK k * (f x)⁻¹ := by
    change f (inclusion hKJ _) = f x * f (inclusion hKJ k) * (f x)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg f
    apply Subtype.ext
    rfl
  have hker : a.ker = (centralizer (((K.subgroupOf J).map f) : Set X)).comap f := by
    ext x
    constructor
    · intro hx y hy
      obtain ⟨k,hkJ,rfl⟩ := hy
      let k' : K := ⟨k,hkJ⟩
      have hh := congrArg (fun b : MulAut (K ⧸ N) => b (QuotientGroup.mk' N k')) hx
      simp only [a, normalizerQuotientAction, MonoidHom.comp_apply,
        quotientAut_apply_mk, MulAut.one_apply] at hh
      have hh' := (heq _ _).mp hh
      rw [hconj] at hh'
      exact ((mul_inv_eq_iff_eq_mul).mp hh').symm
    · intro hx
      change a x = 1
      ext q
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective N q
      simp only [a, normalizerQuotientAction, MonoidHom.comp_apply,
        quotientAut_apply_mk, MulAut.one_apply]
      apply (heq _ _).mpr
      rw [hconj]
      apply mul_inv_eq_iff_eq_mul.mpr
      exact (hx (fK k) ⟨inclusion hKJ k,k.property,rfl⟩).symm
  change a.ker.map f = _
  rw [hker, map_comap_eq_self_of_surjective hf]

end Subgroup
