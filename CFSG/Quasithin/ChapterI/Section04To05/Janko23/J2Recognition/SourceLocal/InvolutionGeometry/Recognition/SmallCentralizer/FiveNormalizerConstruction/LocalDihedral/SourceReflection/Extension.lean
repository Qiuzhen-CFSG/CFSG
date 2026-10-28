module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral.SourceReflection.ModelNorm
public import Theory.GroupTheory.MinusExtraspecialA5Fusion
import all Theory.GroupTheory.MinusExtraspecialA5Fusion

/-!
# Central-square lifts of quotient involutions

In a self-centralizing minus-extraspecial extension by A₅, an existing outside
involution is conjugated so its quotient image equals that of a prescribed
central-square lift x. Writing it d*x makes d*a(d) = x⁻² for the action a of x.
Centrality of x² makes a involutive. Faithfulness and parity of the five-point
action give the model central-norm theorem, so x² = 1.

The internal `import all` reuses the quotient-action kernel and parity proofs
from `MinusExtraspecialA5Fusion`; it does not assume an extension splitting or
repeat the outside-involution fusion theorem. `ModelNorm` discharges the only
finite-model premise of the argument.

Source: Aschbacher, *Sporadic Groups* (1994), the w = 2 case of 46.8 and
46.11, printed pp.253–255; applied to the five-normalizer in 47.1, p.260.
-/

open Subgroup
namespace MinusExtraspecial
open FixedFourCalculation.Outside

variable {H : Type*} [Group H]

private theorem square_action_one (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (x : H) (hx : x ^ 2 ∈ center H) : (modelAction Q e x) ^ 2 = 1 := by
  have hc : (MulAut.conjNormal (x ^ 2) : MulAut Q) = 1 := by
    ext q
    change x ^ 2 * (q : H) * (x ^ 2)⁻¹ = (q : H)
    rw [← Subgroup.mem_center_iff.mp hx q]
    group
  rw [← map_pow]
  change MulAut.congr e (MulAut.conjNormal (x ^ 2)) = 1
  rw [hc, map_one]

/-- If an outside quotient involution lifts with central square, an outside
involution forces that square to be trivial. -/
public theorem reflection_square_eq_one (Q : Subgroup H) [Q.Normal]
    (e : Q ≃* Model) (hc : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (u : H) (hu : orderOf u = 2) (huQ : u ∉ Q)
    (x : H) (hx : orderOf (QuotientGroup.mk' Q x) = 2)
    (hxZ : x ^ 2 ∈ center H) :
    x ^ 2 = 1 := by
  let π := QuotientGroup.mk' Q
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have huπ : orderOf (π u) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hu2, map_one])
    (fun hh => huQ ((QuotientGroup.eq_one_iff u).mp hh))
  have hconj := alternatingGroup.five_involutions_isConj (eA (π u)) (eA (π x))
    ((eA.orderOf_eq _).trans huπ) ((eA.orderOf_eq _).trans hx)
  have hconj' : IsConj (π u) (π x) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      eA.symm.toMonoidHom.map_isConj hconj
  obtain ⟨gbar, hgbar⟩ := isConj_iff.mp hconj'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q gbar
  let w := g * u * g⁻¹
  have hw2 : w ^ 2 = 1 := by
    change (MulAut.conj g u) ^ 2 = 1
    rw [← map_pow, hu2, map_one]
  have hwπ : π w = π x := by simpa only [w, map_mul, map_inv] using hgbar
  have hdmem : w * x⁻¹ ∈ Q := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hwπ
  let d : Q := ⟨w * x⁻¹, hdmem⟩
  let a := modelAction Q e x
  have ha : a ^ 2 = 1 := square_action_one Q e x hxZ
  have heven : Equiv.Perm.sign (fivePointAction a) = 1 := pointAction_even Q e hc eA x
  have hne : fivePointAction a ≠ 1 := by
    intro heq
    have hxQ : x ∈ Q := by
      rw [← pointAction_kernel Q e hc]
      exact heq
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hxQ
    change orderOf (π x) = 2 at hx
    simp only [hx1, orderOf_one] at hx
    norm_num at hx
  have hn : ((d * MulAut.conjNormal x d : Q) : H) = (x ^ 2)⁻¹ := by
    change (w * x⁻¹) * (x * (w * x⁻¹) * x⁻¹) = (x ^ 2)⁻¹
    calc
      _ = w ^ 2 * (x ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = (x ^ 2)⁻¹ := by rw [hw2, one_mul]
  have hnZ : d * MulAut.conjNormal x d ∈ center Q := by
    apply Subgroup.mem_center_iff.mpr
    intro q
    apply Subtype.ext
    change (q : H) * ((d * MulAut.conjNormal x d : Q) : H) =
      ((d * MulAut.conjNormal x d : Q) : H) * (q : H)
    rw [hn]
    exact Subgroup.mem_center_iff.mp (inv_mem hxZ) q
  have he : e d * a (e d) = e (d * MulAut.conjNormal x d) := by
    change e d * e (MulAut.conjNormal x (e.symm (e d))) = _
    rw [e.symm_apply_apply, map_mul]
  have hnZ' : e d * a (e d) ∈ center Model := by
    rw [he]
    apply Subgroup.mem_center_iff.mpr
    intro q
    obtain ⟨q, rfl⟩ := e.surjective q
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hnZ q)
  have hh := FixedFourCalculation.Reflection.central_norm_eq_one a ha heven hne (e d) hnZ'
  rw [he, e.map_eq_one_iff] at hh
  have hh' := congrArg Subtype.val hh
  rw [hn] at hh'
  exact inv_eq_one.mp hh'
end MinusExtraspecial
