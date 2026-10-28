module

public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Prime cores in automorphism overgroups

If G is centerless and O_p(G) is trivial, every subgroup of Aut(G)
containing Inn(G) has trivial p-core. Pull the p-core back along the
inner action. For an automorphism a in the core, its commutator with
conjugation by x is conjugation by a(x)x⁻¹; the trivial pullback forces
a(x)=x. An action containing Inn(G) with p-group kernel consequently has
that kernel as its whole p-core.

This is the elementary automorphism-overgroup argument used for the
local field extensions in Aschbacher--Smith F.1.12, printed p. 264.
-/

@[expose] public section

open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem conj_injective_of_center_eq_bot (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (MulAut.conj : G →* MulAut G).ker.eq_bot_iff_forall.mpr
  intro x hx
  have hx' : MulAut.conj x = 1 := hx
  have hz : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := MulEquiv.congr_fun hx' y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  simpa only [h, Subgroup.mem_bot] using hz

theorem automorphism_core_eq_bot (p : ℕ)
    (hc : Function.Injective (MulAut.conj : G →* MulAut G))
    (hp : pCore p G = ⊥) (A : Subgroup (MulAut G))
    (hA : ∀ x : G, MulAut.conj x ∈ A) : pCore p A = ⊥ := by
  let j : G →* A := (MulAut.conj : G →* MulAut G).codRestrict A hA
  have hj : Function.Injective j := by
    intro x y h
    exact hc (congrArg Subtype.val h)
  have hpre : (pCore p A).comap j ≤ pCore p G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective j hj⟩
  rw [hp] at hpre
  apply (pCore p A).eq_bot_iff_forall.mpr
  intro a ha
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  have hm : ⁅a, j x⁆ ∈ pCore p A := by
    change a * j x * a⁻¹ * (j x)⁻¹ ∈ pCore p A
    have := (inferInstance : (pCore p A).Normal).conj_mem a⁻¹
      ((pCore p A).inv_mem ha) (j x)
    convert (pCore p A).mul_mem ha this using 1; group
  have he : j (a.val x * x⁻¹) = ⁅a, j x⁆ := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    change (a.val x * x⁻¹) * y * (a.val x * x⁻¹)⁻¹ =
      a.val (x * (a.val.symm (x⁻¹ * y * x)) * x⁻¹)
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    group
  have hm' : j (a.val x * x⁻¹) ∈ pCore p A := he.symm ▸ hm
  have hx : a.val x * x⁻¹ = 1 := hpre hm'
  exact mul_inv_eq_one.mp hx

theorem core_eq_kernel_of_action {E : Type*} [Group E] [Finite E] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (hc : Function.Injective (MulAut.conj : G →* MulAut G))
    (hp : pCore p G = ⊥) (a : E →* MulAut G)
    (hi : ∀ x : G, MulAut.conj x ∈ a.range) (hk : IsPGroup p a.ker) :
    pCore p E = a.ker := by
  have hb := automorphism_core_eq_bot p hc hp a.range hi
  have hker : a.rangeRestrict.ker = a.ker := MonoidHom.ker_rangeRestrict a
  have hk' : IsPGroup p a.rangeRestrict.ker := hker.symm ▸ hk
  have ht := a.rangeRestrict.comap_pCore_of_ker_isPGroup
    a.rangeRestrict_surjective hk'
  rw [hb] at ht
  change a.rangeRestrict.ker = pCore p E at ht
  exact ht.symm.trans hker
end Theory.GroupTheory
