module

public import Theory.PGroupCore
public import Theory.GroupAction.AutomorphismOddOuter
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Centralizers with a faithful supplement

Let R be a p-group normalized by C. If C has trivial p-core and acts
faithfully on R, then the centralizer of R in RC lies in R.

Write a centralizing element as rc. Conjugation by c on R is the inner
automorphism induced by r⁻¹. The inverse image in C of Inn(R) is a normal
p-subgroup, because Inn(R) is a p-group and the action is faithful. The
trivial p-core of C forces c = 1. Only normalization of R by C is needed;
R need not be normal in the ambient group.

This elementary semidirect-product argument reduces the local
characteristic-p assertion in GLS3 Theorem 2.6.5(e) to the faithful
full-Levi action on the unipotent radical (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

namespace Subgroup
variable {G : Type*} [Group G]
open scoped Pointwise

theorem sup_inf_centralizer_le_of_faithful_supplement {p : ℕ}
    (R C : Subgroup G) (hCR : C ≤ normalizer (R : Set G))
    (hR : IsPGroup p R) (hcore : pCore p C = ⊥)
    (hfaithful : Function.Injective
      (R.normalizerMonoidHom.comp (inclusion hCR))) :
    (R ⊔ C) ⊓ centralizer (R : Set G) ≤ R := by
  let β := R.normalizerMonoidHom.comp (inclusion hCR)
  let I := (MulAut.conj : R →* MulAut R).range
  have hI : IsPGroup p I :=
    hR.of_surjective (MulAut.conj : R →* MulAut R).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hK : I.comap β ≤ pCore p C :=
    le_sSup ⟨inferInstance, hI.comap_of_injective β hfaithful⟩
  rw [hcore] at hK
  intro g hg
  have hgprod : g ∈ (R : Set G) * C := by
    rw [← coe_mul_of_right_le_normalizer_left R C hCR]
    exact hg.1
  obtain ⟨r, hr, c, hc, he⟩ := hgprod
  change r * c = g at he
  have hβc : β ⟨c, hc⟩ = MulAut.conj (⟨r, hr⟩ : R)⁻¹ := by
    ext x
    change c * x.val * c⁻¹ = r⁻¹ * x.val * (r⁻¹)⁻¹
    have hgx : g * x.val * g⁻¹ = x.val := by
      rw [← mem_centralizer_iff.mp hg.2 x.val x.property, mul_inv_cancel_right]
    calc
      c * x.val * c⁻¹ = r⁻¹ * (g * x.val * g⁻¹) * r := by rw [← he]; group
      _ = r⁻¹ * x.val * (r⁻¹)⁻¹ := by rw [hgx, inv_inv]
  have hcI : (⟨c, hc⟩ : C) ∈ I.comap β := by
    change β ⟨c, hc⟩ ∈ I
    rw [hβc]
    exact ⟨(⟨r, hr⟩ : R)⁻¹, rfl⟩
  have hc1 : c = 1 := congrArg Subtype.val (mem_bot.mp (hK hcI))
  rw [← he, hc1, mul_one]
  exact hr

end Subgroup
