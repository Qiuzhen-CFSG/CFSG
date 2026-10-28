module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.PlanePermutation.Model
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections


/-!
# The two involution classes in the actual GL₄(2)

For a nonidentity involution `t`, the nonzero displacement `N = t - 1`
has square zero. Choose `x` with `N x ≠ 0`. If the image of `N` lies in
its span, a coordinate functional expresses `t` as a transvection, so the
existing transvection conjugacy theorem applies. Otherwise choose `y` with
`N y` outside that line. The four vectors `N x, x, N y, y` are independent:
apply `N` to a relation first, then use the independence of `N x, N y`.
Their coordinate map conjugates the two-block representative to `t`.

This intrinsic calculation supplies the conjugacy-coverage premise of the
plane-permutation exclusion; it makes no claim about that exclusion's
separate centralizer relations or its final source-theorem assembly.

Source motivation: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), 13.8.4(5), printed p.947; 13.8.11(1),
p.950; and the plane-parabolic case of 13.8.25, pp.960–962.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.PlanePermutation

private theorem coefficients_zero {w u : Space} (hw : w ≠ 0)
    (hu : u ∉ Submodule.span (ZMod 2) {w}) {a b : ZMod 2}
    (h : a • w + b • u = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · simp only [hb, zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hw, hb⟩
  · have hb1 : b = 1 := (by decide : ∀ b : ZMod 2, b ≠ 0 → b = 1) b hb
    rw [hb1, one_smul] at h
    exact False.elim (hu ((Submodule.add_mem_iff_right _
      (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w))).mp
        (h.symm ▸ Submodule.zero_mem _)))

private theorem transvection_of_line (t : Actor) (N : Space →ₗ[ZMod 2] Space)
    (hN : ∀ v, t v = v + N v) (hNN : ∀ v, N (N v) = 0)
    (x : Space) (hx : N x ≠ 0)
    (hline : ∀ v, N v ∈ Submodule.span (ZMod 2) {N x}) :
    BinaryLinear.OuterCyclic.IsTransvection t := by
  let f := (LinearEquiv.coord (ZMod 2) Space (N x) hx).toLinearMap.comp
    (N.codRestrict (Submodule.span (ZMod 2) {N x}) hline)
  have hf (v : Space) : f v • N x = N v :=
    LinearEquiv.coord_apply_smul (ZMod 2) Space (N x) hx ⟨N v, hline v⟩
  have hfx : f (N x) = 0 :=
    (smul_eq_zero.mp ((hf (N x)).trans (hNN x))).resolve_right hx
  have hf0 : f ≠ 0 := by
    intro h
    exact hx (by simpa [h] using (hf x).symm)
  refine ⟨N x, f, hx, hf0, hfx, ?_⟩
  apply LinearEquiv.ext
  intro v
  change t v = v + f v • N x
  rw [hf, hN]

private theorem conjugate_of_two_images (t : Actor) (N : Space →ₗ[ZMod 2] Space)
    (hN : ∀ v, t v = v + N v) (hNN : ∀ v, N (N v) = 0)
    (x y : Space) (hx : N x ≠ 0)
    (hy : N y ∉ Submodule.span (ZMod 2) {N x}) :
    IsConj secondInvolution t := by
  let e₀ : Space →ₗ[ZMod 2] Space :=
    (LinearMap.proj 0).smulRight (N x) + (LinearMap.proj 1).smulRight x +
    (LinearMap.proj 2).smulRight (N y) + (LinearMap.proj 3).smulRight y
  have he₀ (v : Space) : e₀ v = v 0 • N x + v 1 • x + v 2 • N y + v 3 • y := rfl
  have hNe₀ (v : Space) : N (e₀ v) = v 1 • N x + v 3 • N y := by
    simp only [he₀, map_add, map_smul, hNN, smul_zero, zero_add, add_zero]
  -- Applying the displacement first separates the two lifted columns.
  have hinj : Function.Injective e₀ := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hn := congrArg N hv
    rw [hNe₀, map_zero] at hn
    obtain ⟨h1, h3⟩ := coefficients_zero hx hy hn
    simp only [he₀, h1, h3, zero_smul, add_zero] at hv
    obtain ⟨h0, h2⟩ := coefficients_zero hx hy hv
    ext i
    fin_cases i <;> assumption
  let e : Actor := LinearEquiv.ofInjectiveEndo e₀ hinj
  apply isConj_iff.mpr
  refine ⟨e, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply LinearEquiv.ext
  intro v
  change e₀ (secondInvolution v) = t (e₀ v)
  rw [hN, hNe₀]
  simp only [he₀, secondInvolution, firstInvolution, LinearEquiv.mul_apply, root_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply]
  norm_num
  simp only [add_smul]
  abel_nf
  simp

/-- Every nonidentity involution of the actual binary four-dimensional linear
group is conjugate to one of the two published representatives. -/
theorem involution_classes (t : Actor) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsConj firstInvolution t ∨ IsConj secondInvolution t := by
  classical
  let N : Space →ₗ[ZMod 2] Space := t.toLinearMap - LinearMap.id
  have hN (v : Space) : t v = v + N v := by
    change t v = v + (t v - v)
    abel
  have htt (v : Space) : t (t v) = v := by
    have h := congrArg (fun g : Actor => g v) ht2
    simpa [pow_two] using h
  have hNN (v : Space) : N (N v) = 0 := by
    change t (t v - v) - (t v - v) = 0
    rw [map_sub, htt]
    calc
      v - t v - (t v - v) = (v + v) - (t v + t v) := by abel
      _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, sub_self]
  obtain ⟨x, hx⟩ : ∃ x, N x ≠ 0 := by
    by_contra h
    push Not at h
    apply ht
    apply LinearEquiv.ext
    intro v
    simpa [h v] using hN v
  by_cases hline : ∀ v, N v ∈ Submodule.span (ZMod 2) {N x}
  · left
    have hf : BinaryLinear.OuterCyclic.IsTransvection firstInvolution := by
      refine ⟨Pi.single 0 1, LinearMap.proj 1, ?_, ?_, ?_, rfl⟩
      · intro h
        have := congrFun h 0
        norm_num at this
      · intro h
        have := congrArg (fun f : Space →ₗ[ZMod 2] ZMod 2 => f (Pi.single 1 1)) h
        norm_num at this
      · simp
    obtain ⟨e, he⟩ := BinaryLinear.OuterCyclic.transvections_conjugate hf
      (transvection_of_line t N hN hNN x hx hline)
    exact isConj_iff.mpr ⟨e, he⟩
  · right
    push Not at hline
    obtain ⟨y, hy⟩ := hline
    exact conjugate_of_two_images t N hN hNN x y hx hy

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.PlanePermutation
