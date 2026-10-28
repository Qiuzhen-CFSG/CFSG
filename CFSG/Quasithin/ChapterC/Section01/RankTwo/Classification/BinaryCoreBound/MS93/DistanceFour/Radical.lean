module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear
import Mathlib.Tactic

/-!
# The radical of the pairing between two binary dual factors

A nonzero equivariant map between two dual natural factors has no nonzero
left or right radical, by transitivity on nonzero covectors. For an additive,
symmetric pairing on the sum of two factors, vanishing on each factor means
that only the cross pairing remains. If the whole pairing is nonzero, these
two separation results make its radical zero.

In the MS93 center argument, the pairing is the actual commutator modulo
U_alpha. The square-map calculation makes the pairing on each individual dual
factor zero. This file proves the linear calculation; realizing the source
quotient and constructing its actual commutator map remain separate steps.

Source: MS93 (1993), binary center passage in (4.6), using (4.6.11)--(4.6.12),
printed pp.909--912.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
open Matrix

theorem dual_inv (g : S) (v : W) : dual g (dual g⁻¹ v) = v := by
  simp only [dual, inv_inv, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
  simp

theorem cross_left_separating (c : W → W → W)
    (hzero : ∀ w, c 0 w = 0)
    (hequiv : ∀ g v w, c (dual g v) (dual g w) = g.val.mulVec (c v w))
    (hne : ∃ v w, c v w ≠ 0) (v : W) (hv : ∀ w, c v w = 0) : v = 0 := by
  by_contra hn
  obtain ⟨x, y, hxy⟩ := hne
  have hx : x ≠ 0 := by rintro rfl; exact hxy (hzero y)
  obtain ⟨g, hg⟩ := dual_orbit hn hx
  have hh := hequiv g v (dual g⁻¹ y)
  rw [hg, dual_inv, hv, Matrix.mulVec_zero] at hh
  exact hxy hh

theorem cross_right_separating (c : W → W → W)
    (hzero : ∀ v, c v 0 = 0)
    (hequiv : ∀ g v w, c (dual g v) (dual g w) = g.val.mulVec (c v w))
    (hne : ∃ v w, c v w ≠ 0) (w : W) (hw : ∀ v, c v w = 0) : w = 0 := by
  exact cross_left_separating (fun v w => c w v) hzero
    (fun g v w => hequiv g w v) (by obtain ⟨v, w, h⟩ := hne; exact ⟨w, v, h⟩) w hw

theorem alternating_pair_separating (b : (W × W) → (W × W) → W)
    (hadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hsymm : ∀ x y, b x y = b y x)
    (hfirst : ∀ v w, b (v, 0) (w, 0) = 0)
    (hsecond : ∀ v w, b (0, v) (0, w) = 0)
    (hequiv : ∀ g x y,
      b (dual g x.1, dual g x.2) (dual g y.1, dual g y.2) = g.val.mulVec (b x y))
    (hne : ∃ x y, b x y ≠ 0) (x : W × W) (hx : ∀ y, b x y = 0) : x = 0 := by
  have hz (y : W × W) : b 0 y = 0 := by
    have h := hadd 0 0 y
    rw [zero_add] at h
    exact add_eq_left.mp h.symm
  let c : W → W → W := fun v w => b (v, 0) (0, w)
  have he (g : S) (v w : W) : c (dual g v) (dual g w) = g.val.mulVec (c v w) := by
    simpa only [dual, Matrix.mulVec_zero] using hequiv g (v, 0) (0, w)
  have decomp (a b' : W × W) : b a b' = c a.1 b'.2 + c b'.1 a.2 := by
    have ha : a = (a.1, 0) + (0, a.2) := by ext <;> simp
    have hb : b' = (b'.1, 0) + (0, b'.2) := by ext <;> simp
    calc
      b a b' = b (a.1, 0) b' + b (0, a.2) b' := by conv_lhs => rw [ha, hadd]
      _ = b b' (a.1, 0) + b b' (0, a.2) := by rw [hsymm (a.1, 0), hsymm (0, a.2)]
      _ = c a.1 b'.2 + c b'.1 a.2 := by
        conv_lhs => rw [hb]
        rw [hadd, hadd, hfirst, hsecond, zero_add, add_zero,
          hsymm (0, b'.2) (a.1, 0)]
  have hc : ∃ v w, c v w ≠ 0 := by
    by_contra! hn
    obtain ⟨a, b', hab⟩ := hne
    rw [decomp, hn, hn, add_zero] at hab
    exact hab rfl
  apply Prod.ext
  · apply cross_left_separating c (fun w => hz (0, w)) he hc
    intro w
    have hh := hx (0, w)
    rw [decomp, show c 0 x.2 = 0 from hz (0, x.2), add_zero] at hh
    exact hh
  · apply cross_right_separating c (fun v => by change b (v, 0) (0, 0) = 0; exact hfirst v 0) he hc
    intro v
    have hh := hx (v, 0)
    rw [decomp, show c x.1 0 = 0 from hfirst x.1 0, zero_add] at hh
    exact hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
