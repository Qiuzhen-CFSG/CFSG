module
public import Theory.SpecificGroups.PSL3Four.CentralCover.NonElementaryParabolic
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Elementary center forced by a Sylow-fixed inner involution

An inner involution fixing a Sylow two-subgroup has a conjugating element
in that Sylow's center: its square is central and the full center is a
two-group. For a perfect central cover of PSL₃(4), a non-elementary center
would equal this Sylow center, making the marked automorphism trivial.
Thus the center has trivial Frattini subgroup.

Source: Aschbacher–Smith I.2.2(3a), used in the inspection before 2.4.32,
printed p.547. The proof retains the entire central kernel.
-/

public section
open Subgroup Theory.GroupTheory

namespace Matrix.PSL3Four

private theorem conj_one_iff {E : Type*} [Group E] (x : E) :
    MulAut.conj x = 1 ↔ x ∈ center E := by
  constructor
  · intro h
    apply mem_center_iff.mpr
    intro y
    have he := DFunLike.congr_fun h y
    change x*y*x⁻¹=y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro h
    ext y
    change x*y*x⁻¹=y
    rw [←mem_center_iff.mp h y,mul_inv_cancel_right]

theorem inner_fixed_sylow_center_frattini {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (e : E ⧸ center E ≃* PSL)
    (hZ : IsPGroup 2 (center E)) (S : Sylow 2 E) (α : MulAut E)
    (hα : orderOf α = 2) (hi : α ∈ (MulAut.conj : E →* MulAut E).range)
    (hfix : ∀ y ∈ S, α y = y) : frattini (center E) = ⊥ := by
  obtain ⟨x,hx⟩ := hi
  have ha2 : α^2=1 := hα ▸ pow_orderOf_eq_one α
  have hx2 : x^2 ∈ center E := (conj_one_iff (x^2)).mp (by
    rw [(MulAut.conj : E →* MulAut E).map_pow,hx,ha2])
  obtain ⟨m,hm⟩ := hZ.exists_pow_pow_eq_one ⟨x^2,hx2⟩
  have hxpow : x^(2^(m+1))=1 := by
    have hh := congrArg Subtype.val hm
    change (x^2)^(2^m)=1 at hh
    simpa only [←pow_mul,Nat.pow_succ,Nat.mul_comm] using hh
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow
    (n:=m+1) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hxpow)
  have hc : x ∈ centralizer (S : Set E) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hh := hfix y hy
    rw [←hx] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hxS : x ∈ S := by
    have hh : x ∈ zpowers x ⊓ normalizer (S:Set E) :=
      ⟨mem_zpowers x,Subgroup.centralizer_le_normalizer _ hc⟩
    rw [hp.inf_normalizer_sylow S] at hh
    exact hh.2
  have hxC : (⟨x,hxS⟩ : (S:Subgroup E)) ∈ center (S:Subgroup E) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hc y y.property)
  by_contra hphi
  have hs := (NonElementaryKernel.source_nonElementary_center e hZ hphi S).1
  have hxZ : x ∈ center E := hs.le ⟨⟨x,hxS⟩,hxC,rfl⟩
  have hone : α=1 := hx.symm.trans ((conj_one_iff x).mpr hxZ)
  rw [hone,orderOf_one] at hα
  omega

end Matrix.PSL3Four
