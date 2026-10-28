module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.IntervalCases
public import Mathlib.GroupTheory.Subgroup.Center
/-!
# Automorphisms fixing a noncentral dihedral involution

In D₈, the pointwise stabilizer of a noncentral involution s consists of
the identity and conjugation by s. The rotation generator has just two
possible images, and it generates D₈ together with s. Consequently any
group action fixing s lifts uniquely to conjugation by the group ⟨s⟩.
This supplies the central correction in the index-two E₄ × S₄ recognition.
-/

public noncomputable section
open Subgroup
namespace DihedralGroup
local notation "D8" => DihedralGroup 4

private theorem rotation_cases : ∀ x : D8, x^2 ≠ 1 → x = r 1 ∨ x = r 3 := by
  decide +kernel

private theorem reflection_data : ∀ s : D8, s^2 = 1 → s ∉ center D8 →
    s * r 1 * s⁻¹ = r 3 ∧
      ∀ x : D8, ∃ i : Fin 4, x = (r 1)^i.val ∨ x = s * (r 1)^i.val := by
  decide +kernel

theorem aut_eq_one_or_conj_of_fixed_involution (s : D8) (hs : s^2=1)
    (hn : s ∉ center D8) (f : MulAut D8) (hf : f s = s) :
    f = 1 ∨ f = MulAut.conj s := by
  obtain ⟨hinv,hgen⟩ := reflection_data s hs hn
  have hext (f g : MulAut D8) (hr : f (r 1) = g (r 1)) (hs : f s = g s) : f=g := by
    apply MulEquiv.ext
    intro x
    obtain ⟨i,rfl | rfl⟩ := hgen x
    · simp only [map_pow,hr]
    · simp only [map_mul,map_pow,hs,hr]
  have hr : f (r 1) ^ 2 ≠ 1 := by
    intro hh
    have hh' : f ((r 1)^2) = f 1 := by simpa only [map_pow,map_one] using hh
    exact (by decide : (r 1 : D8)^2 ≠ 1) (f.injective hh')
  rcases rotation_cases _ hr with h | h
  · exact Or.inl (hext f 1 h hf)
  · apply Or.inr
    apply hext f (MulAut.conj s)
    · exact h.trans hinv.symm
    · simpa only [MulAut.conj_apply,mul_inv_cancel_right] using hf

 theorem aut_eq_one_or_conj_of_fixed_involution_of_equiv
    {K : Type*} [Group K] (e : K ≃* D8) (s : K) (hs : s^2=1)
    (hn : s ∉ center K) (f : MulAut K) (hf : f s = s) :
    f = 1 ∨ f = MulAut.conj s := by
  have hse : (e s)^2=1 := by rw [←map_pow,hs,map_one]
  have hne : e s ∉ center D8 := by
    intro hh
    apply hn
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hh (e y)
  let f' : MulAut D8 := (MulAut.congr e) f
  have hfix : f' (e s) = e s := by
    change e (f (e.symm (e s))) = e s
    rw [e.symm_apply_apply,hf]
  rcases aut_eq_one_or_conj_of_fixed_involution (e s) hse hne f' hfix with h | h
  · left
    apply MulEquiv.ext
    intro y
    have hh := DFunLike.congr_fun h (e y)
    change e (f (e.symm (e y))) = e y at hh
    change f y = y
    exact e.injective (by simpa only [e.symm_apply_apply] using hh)
  · right
    apply MulEquiv.ext
    intro y
    apply e.injective
    have hh := DFunLike.congr_fun h (e y)
    change e (f (e.symm (e y))) = e s * e y * (e s)⁻¹ at hh
    simpa only [e.symm_apply_apply,MulAut.conj_apply,map_mul,map_inv] using hh

theorem exists_conj_lift_of_fixed_involution
    {K H : Type*} [Group K] [Finite K] [Group H] (e : K ≃* D8)
    (s : K) (hs : s^2=1) (hn : s ∉ center K)
    (a : H →* MulAut K) (hfix : ∀ h, a h s = s) :
    ∃ u : H →* zpowers s, ∀ h, MulAut.conj (u h : K) = a h := by
  classical
  have hs1 : s ≠ 1 := by intro hh; exact hn (hh ▸ (center K).one_mem)
  have ho : orderOf s = 2 := orderOf_eq_prime hs hs1
  have ht (x : zpowers s) : (x : K) = 1 ∨ (x : K) = s := by
    have hx := x.property
    rw [mem_zpowers_iff_mem_range_orderOf,ho] at hx
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hx
    rw [←he]
    have hn2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  let c : zpowers s →* MulAut K := MulAut.conj.comp (zpowers s).subtype
  have hci : Function.Injective c := by
    apply (MonoidHom.ker_eq_bot_iff c).mp
    apply bot_unique
    intro x hx
    rcases ht x with hx1 | hxs
    · exact Subtype.ext hx1
    · exfalso
      apply hn
      apply mem_center_iff.mpr
      intro y
      have hh := DFunLike.congr_fun hx y
      change (x : K) * y * (x : K)⁻¹ = y at hh
      rw [hxs] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have ha (h : H) : a h ∈ c.range := by
    rcases aut_eq_one_or_conj_of_fixed_involution_of_equiv e s hs hn (a h) (hfix h) with hh | hh
    · exact ⟨1,by simpa only [map_one] using hh.symm⟩
    · exact ⟨⟨s,mem_zpowers s⟩,hh.symm⟩
  let ec := MonoidHom.ofInjective hci
  let u := ec.symm.toMonoidHom.comp (a.codRestrict c.range ha)
  refine ⟨u,?_⟩
  intro h
  exact congrArg Subtype.val (ec.apply_symm_apply (⟨a h,ha h⟩ : c.range))

end DihedralGroup
