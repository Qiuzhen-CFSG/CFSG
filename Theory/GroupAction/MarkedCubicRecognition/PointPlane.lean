module
public import Theory.GroupAction.MarkedCubicRecognition.BinaryNorm
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# A point-plane obstruction for a normal Heisenberg action

Suppose a binary point spans a four-plane under the first marked cubic,
is centralized by the second, and spans the whole normal elementary
subgroup under the ambient group. The cubic norm identity makes the
Heisenberg center fix the point. Its relative normality then propagates
centralization to the entire span. The theorem keeps the given quotient
map and its literal conjugation action.

Source application: Aschbacher–Smith, proof of 14.5.3 after 14.5.13,
printed p.1017, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace MarkedCubicRecognition

private theorem axis_zpowers (f : C3 →* HeisenbergPrime 3) :
    f.range = zpowers (f (Multiplicative.ofAdd 1)) := by
  rw [MonoidHom.range_eq_map, ←zpowers_eq_top_of_prime_card (p := 3)
    (by simp : Nat.card C3 = 3) (by decide : (Multiplicative.ofAdd 1 : C3) ≠ 1),
    MonoidHom.map_zpowers]

/-- A normal Heisenberg center fixes the entire span of a binary point
whose first cubic orbit is a four-plane and whose second cubic fixes it. -/
theorem center_kernel_of_point_plane
    {D E : Type*} [Group D] [Finite D] [Group E]
    (U Z P X Y : Subgroup D) [U.Normal] [IsElementaryAbelian 2 U]
    (π : D →* E) (hπ : Function.Surjective π)
    (β : E →* MulAut U) (hβ : β.comp π = MulAut.conjNormal)
    (R : Subgroup E) [R.Normal] (e : HeisenbergPrime 3 ≃* R)
    (hX : leftAxis.range.map (R.subtype.comp e.toMonoidHom) = X.map π)
    (hY : rightAxis.range.map (R.subtype.comp e.toMonoidHom) = Y.map π)
    (hZP : Z ≤ P) (hPU : P ≤ U) (hZ : Nat.card Z = 2) (hP : Nat.card P = 4)
    (hXP : X ≤ normalizer (P : Set D)) (hYZ : Y ≤ centralizer (Z : Set D))
    (hplane : conjugateSpanBy Z X = P) (hspan : conjugateSpanBy Z ⊤ = U) :
    (center R).map R.subtype ≤ β.ker := by
  let r := R.subtype.comp e.toMonoidHom
  let α := β.comp r
  have hXgen : zpowers (r leftGenerator) = X.map π := by
    rw [←hX,axis_zpowers,MonoidHom.map_zpowers,leftAxis_generator]
  obtain ⟨x,hx,hqx⟩ := hXgen ▸ mem_zpowers (r leftGenerator)
  let a : MulAut P := P.normalizerMonoidHom ⟨x,hXP hx⟩
  let j := inclusion hPU
  have hact (d : D) (w : U) : (β (π d) w : D) = d * w * d⁻¹ := by
    have hh := DFunLike.congr_fun hβ d
    exact congrArg (fun f : MulAut U => (f w : D)) hh
  have hj (w : P) : j (a w) = α leftGenerator (j w) := by
    apply Subtype.ext
    change x * (w : D) * x⁻¹ = (β (r leftGenerator) (j w) : D)
    rw [←hqx,hact]
    rfl
  have ha : a ^ 3 = 1 := by
    apply MulEquiv.ext
    intro w
    apply (inclusion_injective hPU)
    change j ((a ^ 3) w) = j w
    have hp : (α leftGenerator) ^ 3 = 1 := by
      rw [←map_pow,HeisenbergPrime.pow_prime (by decide),map_one]
    have hh := congrArg (fun f : MulAut U => f (j w)) hp
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply,←hj] using hh
  have hne : a ≠ 1 := by
    intro ha1
    have halpha (w : P) : α leftGenerator (j w) = j w := by rw [←hj,ha1]; rfl
    have hcentral : X ≤ centralizer (P : Set D) := by
      intro d hd
      apply mem_centralizer_iff.mpr
      intro w hw
      have hmem : π d ∈ zpowers (r leftGenerator) := hXgen ▸ mem_map_of_mem π hd
      obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hmem
      have hh : β (π d) (j ⟨w,hw⟩) = j ⟨w,hw⟩ := by
        rw [←hn,map_zpow]
        exact smul_eq_self_of_mem_zpowers (zpow_mem (mem_zpowers (β (r leftGenerator))) n)
          (halpha ⟨w,hw⟩)
      have hv := congrArg Subtype.val hh
      rw [hact] at hv
      exact (mul_inv_eq_iff_eq_mul.mp hv).symm
    have heq : P = Z := le_antisymm
      (hplane ▸ (conjugateSpanBy_le le_rfl
        ((hcentral.trans (centralizer_le hZP)).trans (centralizer_le_normalizer _)))) hZP
    rw [heq,hZ] at hP
    contradiction
  have hseed : ((center R).map R.subtype).comap π ≤ centralizer (Z : Set D) := by
    intro d hd
    obtain ⟨z,hzc,hz⟩ := hd
    let t := e.symm z
    have ht : t ∈ center (HeisenbergPrime 3) := by
      apply mem_center_iff.mpr
      intro w
      apply e.injective
      simpa only [map_mul,t,e.apply_symm_apply] using (mem_center_iff.mp hzc (e w))
    apply mem_centralizer_iff.mpr
    intro v hv
    have hy : α rightGenerator (j ⟨v,hZP hv⟩) = j ⟨v,hZP hv⟩ := by
      have hm : r rightGenerator ∈ Y.map π := by
        rw [←hY]
        exact mem_map_of_mem r ⟨Multiplicative.ofAdd 1,rfl⟩
      obtain ⟨y,hy,hqy⟩ := hm
      apply Subtype.ext
      change (β (r rightGenerator) (j ⟨v,hZP hv⟩) : D) = v
      rw [←hqy,hact]
      exact mul_inv_eq_of_eq_mul ((mem_centralizer_iff.mp (hYZ hy) v hv).symm)
    let : IsMulCommutative P := ⟨⟨fun x y => (inclusion_injective hPU) (by simp only [map_mul,mul_comm])⟩⟩
    have hc := heisenberg_center_fixed_of_four_plane α j a hP ha hne hj
      ⟨v,hZP hv⟩ hy t ht
    have he : r t = π d := by
      change (e (e.symm z) : E) = π d
      rw [e.apply_symm_apply]
      exact hz
    change β (r t) (j ⟨v,hZP hv⟩) = j ⟨v,hZP hv⟩ at hc
    rw [he] at hc
    have hh := congrArg Subtype.val hc
    rw [hact] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let B := (center R).map R.subtype
  let : B.Normal := inferInstance
  have hcent : B.comap π ≤ centralizer (U : Set D) := by
    rw [←hspan]
    exact le_centralizer_conjugateSpanBy_of_normalizes _ _ _ le_normalizer_of_normal hseed
  intro b hb
  obtain ⟨d,rfl⟩ := hπ b
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  rw [hact]
  exact mul_inv_eq_of_eq_mul ((mem_centralizer_iff.mp (hcent hb) w w.property).symm)

end MarkedCubicRecognition
