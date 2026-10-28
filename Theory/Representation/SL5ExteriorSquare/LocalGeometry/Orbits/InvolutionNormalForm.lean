module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Conjugacy
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections

/-!
# The two involution normal forms in SL₅(2)

For a nonidentity involution, the natural displacement N is nonzero and has
square zero. If its image is a line, the binary transvection conjugacy theorem
applies. Otherwise choose independent images N x and N y. Rank-nullity gives
a vector z in ker N outside im N, and the five columns N x, N y, x, y, z form
an invertible coordinate map intertwining j₂ with the given involution.
The existing binary SL/GL equivalence realizes both linear conjugators by
actual determinant-one matrices: the only nonzero binary determinant is one.

The two-image argument adapts the four-dimensional calculation in Chapter 13's
PlanePermutation/InvolutionClasses, with the additional fixed column supplied
by the kernel/image dimension inequality. All dependencies here lie in Theory.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 12.5.5(1), printed p.819/PDF p.836. This module proves
conjugacy exhaustion; the representative ranks and separation are in Conjugacy.
-/

public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private abbrev Space := Fin 5 → ZMod 2
private abbrev Actor := Space ≃ₗ[ZMod 2] Space

private theorem natural_j₁ (v : Space) :
    BinaryLinear.OuterCyclic.slEquivLinear 5 j₁ v = v + v 4 • Pi.single 0 1 := by
  change j₁.val.mulVec v = _
  ext i
  fin_cases i <;> simp [j₁, elementary, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

private theorem natural_j₂ (v : Space) :
    BinaryLinear.OuterCyclic.slEquivLinear 5 j₂ v =
      ![v 0 + v 2, v 1 + v 3, v 2, v 3, v 4] := by
  change j₂.val.mulVec v = _
  ext i
  fin_cases i <;> simp [j₂, elementary, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply, Matrix.mul_apply]

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
    (x y z : Space) (hx : N x ≠ 0)
    (hy : N y ∉ Submodule.span (ZMod 2) {N x})
    (hz : N z = 0) (hzr : z ∉ LinearMap.range N) :
    IsConj (BinaryLinear.OuterCyclic.slEquivLinear 5 j₂) t := by
  let e₀ : Space →ₗ[ZMod 2] Space :=
    (LinearMap.proj 0).smulRight (N x) + (LinearMap.proj 1).smulRight (N y) +
    (LinearMap.proj 2).smulRight x + (LinearMap.proj 3).smulRight y +
    (LinearMap.proj 4).smulRight z
  have he₀ (v : Space) :
      e₀ v = v 0 • N x + v 1 • N y + v 2 • x + v 3 • y + v 4 • z := rfl
  have hNe₀ (v : Space) : N (e₀ v) = v 2 • N x + v 3 • N y := by
    simp only [he₀, map_add, map_smul, hNN, hz, smul_zero, zero_add, add_zero]
  -- Apply N first to remove the lifted columns, then use z outside its image.
  have hinj : Function.Injective e₀ := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hn := congrArg N hv
    rw [hNe₀, map_zero] at hn
    obtain ⟨h2, h3⟩ := coefficients_zero hx hy hn
    simp only [he₀, h2, h3, zero_smul, add_zero] at hv
    have h4 : v 4 = 0 := by
      by_contra h4
      have h41 : v 4 = 1 := (by decide : ∀ b : ZMod 2, b ≠ 0 → b = 1) _ h4
      rw [h41, one_smul] at hv
      exact hzr ((Submodule.add_mem_iff_right (LinearMap.range N)
        (Submodule.add_mem _ (Submodule.smul_mem _ _ (LinearMap.mem_range_self N x))
          (Submodule.smul_mem _ _ (LinearMap.mem_range_self N y)))).mp
            (hv.symm ▸ Submodule.zero_mem _))
    simp only [h4, zero_smul, add_zero] at hv
    obtain ⟨h0, h1⟩ := coefficients_zero hx hy hv
    ext i
    fin_cases i <;> assumption
  let e : Actor := LinearEquiv.ofInjectiveEndo e₀ hinj
  apply isConj_iff.mpr
  refine ⟨e, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply LinearEquiv.ext
  intro v
  change e₀ (BinaryLinear.OuterCyclic.slEquivLinear 5 j₂ v) = t (e₀ v)
  rw [hN, hNe₀, natural_j₂]
  simp only [he₀, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    add_smul]
  abel

/-- Every nonidentity involution of the actual binary special linear group in
five dimensions is conjugate to one of its two marked representatives. -/
theorem involution_conjugacy_exhaustion (g : Group) (hne : g ≠ 1) (hg : g * g = 1) :
    IsConj j₁ g ∨ IsConj j₂ g := by
  classical
  let φ := BinaryLinear.OuterCyclic.slEquivLinear 5
  let t : Actor := φ g
  let N := naturalDisplacement g
  have hN (v : Space) : t v = v + N v := by
    change specialLinearNatural 5 g v = v + (specialLinearNatural 5 g v - v)
    abel
  have hNN (v : Space) : N (N v) = 0 := naturalDisplacement_square_zero hg v
  obtain ⟨x, hx⟩ : ∃ x, N x ≠ 0 := by
    by_contra! h
    apply hne
    apply (naturalDisplacement_eq_zero_iff g).mp
    exact LinearMap.ext h
  have transport {a : Group} (h : IsConj (φ a) t) : IsConj a g := by
    have he := φ.symm.toMonoidHom.map_isConj h
    simpa only [t, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.symm_apply_apply] using he
  by_cases hline : ∀ v, N v ∈ Submodule.span (ZMod 2) {N x}
  · left
    apply transport
    have hf : BinaryLinear.OuterCyclic.IsTransvection (φ j₁) := by
      refine ⟨Pi.single 0 1, LinearMap.proj 4, ?_, ?_, ?_, ?_⟩
      · intro h
        have := congrFun h 0
        norm_num at this
      · intro h
        have := congrArg (fun f : Space →ₗ[ZMod 2] ZMod 2 => f (Pi.single 4 1)) h
        norm_num at this
      · simp
      · exact LinearEquiv.ext natural_j₁
    obtain ⟨e, he⟩ := BinaryLinear.OuterCyclic.transvections_conjugate hf
      (transvection_of_line t N hN hNN x hx hline)
    exact isConj_iff.mpr ⟨e, he⟩
  · right
    push Not at hline
    obtain ⟨y, hy⟩ := hline
    have hle : Module.finrank (ZMod 2) (LinearMap.range N) ≤ 2 :=
      finrank_naturalDisplacement_le_two hg
    have hd := LinearMap.finrank_range_add_finrank_ker N
    have hdim : Module.finrank (ZMod 2) Space = 5 := by simp [Space]
    -- In dimension five, the kernel has dimension at least three, the image at most two.
    have hnot : ¬ LinearMap.ker N ≤ LinearMap.range N := by
      intro h
      have hm := Submodule.finrank_mono h
      change Module.finrank (ZMod 2) (LinearMap.range N) +
        Module.finrank (ZMod 2) (LinearMap.ker N) = Module.finrank (ZMod 2) Space at hd
      omega
    obtain ⟨z, hz, hzr⟩ : ∃ z, N z = 0 ∧ z ∉ LinearMap.range N := by
      by_contra! h
      exact hnot (fun z hz => h z hz)
    exact transport (conjugate_of_two_images t N hN hNN x y z hx hy hz hzr)

end Representation.SL5ExteriorSquare
