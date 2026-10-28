module

public import Theory.Representation.BinaryInvolutionFreeness
public import Mathlib.FieldTheory.Finiteness

/-!
# The fixed line of a nonidentity binary plane involution

The displacement has nonzero rank and lies in its own kernel. Rank-nullity
on a binary plane forces both ranks to be one, hence exactly two fixed
vectors. This supplies the fixed-center count in Aschbacher–Smith J.4.1(4).
-/

public section
namespace Representation.BinaryInvolution
variable {Γ : Type*} [Monoid Γ]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- A nonidentity involution on a binary plane has exactly two fixed vectors. -/
theorem fixed_card_of_finrank_two [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) Γ W) (t : Γ)
    (ht : t * t = 1) (hdim : Module.finrank (ZMod 2) W = 2)
    (hne : ∃ v, ρ t v ≠ v) : Nat.card (ρ t - 1).ker = 2 := by
  let D := ρ t - 1
  have hbin (v : W) : v + v = 0 := by
    have h := @two_smul (ZMod 2) W _ _ _ v
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
    exact h.symm
  have hincl : D.range ≤ D.ker := by
    rintro _ ⟨w,rfl⟩
    change ρ t (ρ t w - w) - (ρ t w - w) = 0
    have haa : ρ t (ρ t w) = w := by
      rw [← Module.End.mul_apply,← map_mul,ht,map_one,Module.End.one_apply]
    rw [map_sub,haa]
    calc
      _ = (w+w) - (ρ t w+ρ t w) := by abel
      _ = 0 := by rw [hbin,hbin,sub_self]
  have hr0 : Module.finrank (ZMod 2) D.range ≠ 0 := by
    intro h
    have hz : D = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)
    obtain ⟨v,hv⟩ := hne
    exact hv (LinearMap.congr_fun (sub_eq_zero.mp hz) v)
  have hsum := D.finrank_range_add_finrank_ker
  rw [hdim] at hsum
  have hm := Submodule.finrank_mono hincl
  have hk : Module.finrank (ZMod 2) D.ker = 1 := by omega
  change Nat.card D.ker = 2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hk,Nat.card_zmod,pow_one]

end Representation.BinaryInvolution
