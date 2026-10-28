module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NativeRankOne

/-!
# Source and native Suzuki coordinates in the full Ree group

Fong--Seitz II (10.32) uses the cocycle `a*pi(c)`, whereas the native signed
chart uses `pi(a)*c`. Adding `a*pi(a)` to the second coordinate gives the
bijection between them. The proofs retain both signs, the full Cartan and
literal reflection, and transport the existing native Gauss equation through
this bijection. No identification of an unknown source group is asserted.

Source: Fong--Seitz, Groups with a (B,N)-pair of rank 2, II, pp.229--232,
(10.32)--(10.43); GLS3, Table 2.4 type V. Source theta is `titsEnd`, the
inverse of `FieldRecovery.theta`. All statements include the field of order two.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SuzukiConvention
variable {m : ℕ}

/-- Fong--Seitz's second coordinate differs from the native one by its diagonal cocycle. -/
def change (m : ℕ) : (CoefficientField m × CoefficientField m) ≃
    (CoefficientField m × CoefficientField m) where
  toFun a := (a.1, a.2 + a.1 * titsEnd m a.1)
  invFun a := (a.1, a.2 + a.1 * titsEnd m a.1)
  left_inv a := by
    refine Prod.ext (by rfl) ?_
    simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  right_inv a := by
    refine Prod.ext (by rfl) ?_
    simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Source (10.32), with source theta equal to the native Tits map. -/
def sourceMul (a b : CoefficientField m × CoefficientField m) :=
  (a.1 + b.1, a.2 + b.2 + a.1 * titsEnd m b.1)

def nativeMul (a b : CoefficientField m × CoefficientField m) :=
  (a.1 + b.1, a.2 + b.2 + titsEnd m a.1 * b.1)

theorem change_mul (a b : CoefficientField m × CoefficientField m) :
    change m (sourceMul a b) = nativeMul (change m a) (change m b) := by
  refine Prod.ext (by rfl) ?_
  dsimp [change, sourceMul, nativeMul]
  rw [map_add]
  have htwo : (2 : CoefficientField m) = 0 := by
    simpa only [one_add_one_eq_two] using CharTwo.add_self_eq_zero (1 : CoefficientField m)
  ring_nf
  simp only [htwo, mul_zero, add_zero]

/-- The source convention on the actual signed fixed root chart. -/
def chart (m : ℕ) (p : Bool) (a : CoefficientField m × CoefficientField m) : Model m :=
  suzuki m p (change m a).1 (change m a).2

theorem chart_mul (p : Bool) (a b : CoefficientField m × CoefficientField m) :
    chart m p a * chart m p b = chart m p (sourceMul a b) := by
  rw [chart, chart, suzuki_mul, chart, change_mul]
  rfl

@[simp] theorem chart_zero (p : Bool) : chart m p (0,0) = 1 := by
  simp [chart, change]

theorem chart_injective (p : Bool) : Function.Injective (chart m p) :=
  (suzuki_injective p).comp (change m).injective

theorem chart_mem (p : Bool) (a : CoefficientField m × CoefficientField m) :
    chart m p a ∈ rootBlock m .suzuki p := suzuki_mem p _ _

theorem chart_cover (p : Bool) (x : Model m) (hx : x ∈ rootBlock m .suzuki p) :
    ∃ a, chart m p a = x := by
  obtain ⟨t,u,he⟩ := suzuki_cover p x hx
  refine ⟨(change m).symm (t,u), ?_⟩
  simpa only [chart, Equiv.apply_symm_apply] using he

/-- Bijective parameters on the same native signed root subgroup. -/
def chartEquiv (m : ℕ) (p : Bool) :
    (CoefficientField m × CoefficientField m) ≃ rootBlock m .suzuki p :=
  Equiv.ofBijective (fun a => ⟨chart m p a, chart_mem p a⟩) ⟨
    fun a b h => chart_injective p (congrArg Subtype.val h),
    fun x => by obtain ⟨a,ha⟩ := chart_cover (m := m) p x.val x.property; exact ⟨a,Subtype.ext ha⟩⟩

theorem chart_inv (p : Bool) (a : CoefficientField m × CoefficientField m) :
    (chart m p a)⁻¹ = chart m p (a.1, a.2+a.1*titsEnd m a.1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [chart_mul]
  have hz : sourceMul a (a.1, a.2+a.1*titsEnd m a.1) = (0,0) := by
    simp only [sourceMul, CharTwo.add_self_eq_zero, add_assoc, add_zero]
  rw [hz, chart_zero]

/-- Coordinate change commutes with the forced first and central characters. -/
theorem change_scale (c : CoefficientField m) (a : CoefficientField m × CoefficientField m) :
    change m (c*a.1, (c*titsEnd m c)*a.2) =
      (c*(change m a).1, (c*titsEnd m c)*(change m a).2) := by
  refine Prod.ext (by rfl) ?_
  dsimp [change]
  rw [map_mul]
  ring

open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

private theorem signed_central (c : (CoefficientField m)ˣ) (p : Bool) :
    (signedScale (centralScale c) p : CoefficientField m) =
      (signedScale c p : CoefficientField m)*titsEnd m (signedScale c p) := by
  cases p <;> simp only [signedScale, Bool.false_eq_true, ↓reduceIte,
    centralScale, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map,
    Units.val_inv_eq_inv_val, map_inv₀, mul_inv, MonoidHom.coe_coe, theta_sq]

/-- Source coordinates retain the whole native Cartan and both sign characters. -/
theorem torus_chart (a : TorusParameter m) (p : Bool)
    (v : CoefficientField m × CoefficientField m) :
    torus m a * chart m p v * (torus m a)⁻¹ =
      chart m p ((signedScale a.2 p : CoefficientField m)*v.1,
        (signedScale (centralScale a.2) p : CoefficientField m)*v.2) := by
  rw [chart, torus_suzuki, signed_central]
  rw [chart, change_scale]

/-- The same literal reflection exchanges signs in the source convention. -/
theorem reflection_chart (a : CoefficientField m × CoefficientField m) :
    reflection m .suzuki * chart m false a * reflection m .suzuki = chart m true a :=
  reflection_suzuki _ _

open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData

/-- Source Gauss parameters are obtained by the actual coordinate conversion,
not by copying the native reciprocal formulas unchanged. -/
theorem gauss_chart (a : CoefficientField m × CoefficientField m)
    (hn : norm (change m a).1 (change m a).2 ≠ 0) :
    reflection m .suzuki * chart m false a =
      chart m false ((change m).symm
        (negativeFirst (change m a).1 (change m a).2,
         negativeSecond (change m a).1 (change m a).2)) *
      torus m (suzukiTau (Units.mk0 (norm (change m a).1 (change m a).2) hn)) *
      chart m true ((change m).symm
        (positiveFirst (change m a).1 (change m a).2,
         positiveSecond (change m a).1 (change m a).2)) := by
  simpa only [chart, Equiv.apply_symm_apply] using
    suzuki_gauss (change m a).1 (change m a).2 hn

/-- The binary source chart is still cyclic of order four. -/
theorem binary_square (p : Bool) : chart 0 p (1,0) * chart 0 p (1,0) = chart 0 p (0,1) := by
  rw [chart_mul]
  simp only [sourceMul, CharTwo.add_self_eq_zero, map_one, one_mul, zero_add]


/-- Native parameters recovered from the source-coordinate equivalence. -/
def nativeChartEquiv (m : ℕ) (p : Bool) :
    (CoefficientField m × CoefficientField m) ≃ rootBlock m .suzuki p :=
  (change m).symm.trans (chartEquiv m p)

@[simp] theorem nativeChartEquiv_apply (p : Bool)
    (a : CoefficientField m × CoefficientField m) :
    (nativeChartEquiv m p a : Model m) = suzuki m p a.1 a.2 := by
  change chart m p ((change m).symm a) = _
  simp only [chart, Equiv.apply_symm_apply]

@[simp] theorem nativeChartEquiv_zero (p : Bool) :
    nativeChartEquiv m p (0,0) = 1 := Subtype.ext (by rw [nativeChartEquiv_apply,suzuki_zero]; rfl)

/-- Multiplication in the actual root subgroup recovers the native nonlinear law. -/
theorem nativeChartEquiv_mul (p : Bool) (a b : CoefficientField m × CoefficientField m) :
    nativeChartEquiv m p (nativeMul a b) = nativeChartEquiv m p a * nativeChartEquiv m p b := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul,nativeChartEquiv_apply,nativeMul] using
    (suzuki_mul p a.1 a.2 b.1 b.2).symm

end ReeF4.RootPresentationRecognition.SuzukiConvention
