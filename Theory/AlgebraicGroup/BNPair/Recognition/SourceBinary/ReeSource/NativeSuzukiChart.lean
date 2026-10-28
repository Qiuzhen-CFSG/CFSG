module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiCoordinates
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates

/-!
# The source Suzuki chart in the native Ree fixed root

The source Tits map is `titsEnd`, whereas native `FieldRecovery.theta`
is its inverse. The triangular correction `(a,b) ↦ (a,b+a*pi(a))`
converts the source law `b+d+a*pi(c)` to the native law `b+d+pi(a)*c`.
The correction is involutive, preserves both full signed fixed roots,
and commutes with the actual fixed opposition representative.

Composing the proved source simple-root coordinates with these corrected
native charts gives an actual group isomorphism to each signed fixed
root, with its parameter formula. This compares one root, not the
unknown source group or either full parabolic. Mixed equations and a
common field with the linear root remain to be proved.

Source: Fong–Seitz II §10, p.230, the law preceding (10.32), compared
with GLS3 Table 2.4 type V as implemented in native `SuzukiCoordinates`.
All parameters, including m = 0, are retained.
-/

@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.NativeSuzukiChart
open ReeF4
open ReeF4.LocalBlockInput ReeF4.LocalBlockInput.PairRigidity
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open SuzukiChart
variable {m : ℕ}
noncomputable def correction (a : CoefficientField m) : CoefficientField m :=
  a * ReeF4.titsEnd m a

def sourceWord (positive : Bool) (a b : CoefficientField m) : SplitGroup m :=
  suzukiWord m positive a (b + correction a)

theorem theta_sq (a : CoefficientField m) :
    (theta m a) ^ 2 = titsEnd m a := by
  change (a ^ (2 ^ m)) ^ 2 = a ^ (2 ^ (m+1))
  rw [← pow_mul, pow_succ]

theorem sourceWord_mul_pos (a b c d : CoefficientField m) :
    sourceWord (m := m) true a b * sourceWord true c d =
      sourceWord true (a + c) (b + d + a * ReeF4.titsEnd m c) := by
  rw [sourceWord, sourceWord, SuzukiChart.positive_mul, sourceWord]
  rw [theta_sq]
  congr 1
  simp only [correction, map_add]
  linear_combination (norm := ring_nf) -(CharTwo.add_self_eq_zero (a * titsEnd m c))

theorem sourceWord_mul_neg (a b c d : CoefficientField m) :
    sourceWord (m := m) false a b * sourceWord false c d =
      sourceWord false (a + c) (b + d + a * ReeF4.titsEnd m c) := by
  rw [sourceWord, sourceWord, SuzukiChart.negative_mul, sourceWord]
  rw [theta_sq]
  congr 1
  simp only [correction, map_add]
  linear_combination (norm := ring_nf) -(CharTwo.add_self_eq_zero (a * titsEnd m c))

/-- The triangular correction is its own inverse in characteristic two. -/
def coordinateCorrection : (CoefficientField m × CoefficientField m) ≃
    (CoefficientField m × CoefficientField m) where
  toFun p := (p.1, p.2 + correction p.1)
  invFun p := (p.1, p.2 + correction p.1)
  left_inv p := by simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  right_inv p := by simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem sourceWord_injective (positive : Bool) : Function.Injective
    (fun p : CoefficientField m × CoefficientField m => sourceWord positive p.1 p.2) := by
  intro p q hpq
  apply (coordinateCorrection (m := m)).injective
  cases positive
  · exact SuzukiChart.negative_injective (a₁ := coordinateCorrection p)
      (a₂ := coordinateCorrection q) hpq
  · exact SuzukiChart.positive_injective (a₁ := coordinateCorrection p)
      (a₂ := coordinateCorrection q) hpq

theorem sourceWord_fixed (d : LocalBlockInput m) (positive : Bool) (a b : CoefficientField m) :
    sourceWord positive a b ∈ d.fixedGroup := by
  cases positive
  · exact SuzukiChart.negative_fixed d _ _
  · exact SuzukiChart.positive_fixed d _ _

theorem sourceWord_mem (positive : Bool) (a b : CoefficientField m) :
    sourceWord positive a b ∈ splitSimpleBlock m .suzuki positive := by
  cases positive
  · exact SuzukiChart.negative_mem _ _
  · exact SuzukiChart.positive_mem _ _

theorem sourceWord_cover (d : LocalBlockInput m) (positive : Bool) (x : d.fixedGroup)
    (hx : x ∈ simpleBlock d .suzuki positive) :
    ∃ a b, sourceWord positive a b = x.val := by
  have hc : ∃ a b, suzukiWord m positive a b = x.val := by
    cases positive
    · exact SuzukiChart.negative_cover d x hx
    · exact SuzukiChart.positive_cover d x hx
  obtain ⟨a,b,hab⟩ := hc
  refine ⟨a,b+correction a,?_⟩
  simpa only [sourceWord, add_assoc, CharTwo.add_self_eq_zero, add_zero] using hab

theorem sourceWord_mul (positive : Bool) (a b c d : CoefficientField m) :
    sourceWord positive a b * sourceWord positive c d =
      sourceWord positive (a+c) (b+d+a*titsEnd m c) := by
  cases positive
  · exact sourceWord_mul_neg a b c d
  · exact sourceWord_mul_pos a b c d

/-- The correction commutes with the model's fixed opposition representative. -/
theorem sourceWord_opposition (a b : CoefficientField m) :
    MulAut.conj (PairNormalization.splitOpposition m) (sourceWord true a b) =
      sourceWord false a b := SuzukiChart.opposition_word _ _

/-- An actual element of the whole signed fixed root, not just an ambient word. -/
def nativeRootPoint (d : LocalBlockInput m) (positive : Bool) (a b : CoefficientField m) :
    simpleBlock d .suzuki positive :=
  ⟨⟨sourceWord positive a b, sourceWord_fixed d positive a b⟩, sourceWord_mem positive a b⟩

theorem nativeRootPoint_bijective (d : LocalBlockInput m) (positive : Bool) : Function.Bijective
    (fun p : CoefficientField m × CoefficientField m => nativeRootPoint d positive p.1 p.2) := by
  constructor
  · intro p q hpq
    exact sourceWord_injective positive (congrArg (fun x : simpleBlock d .suzuki positive => x.val.val) hpq)
  · intro x
    obtain ⟨a,b,hab⟩ := sourceWord_cover d positive x.val x.property
    exact ⟨(a,b),Subtype.ext (Subtype.ext hab)⟩

theorem nativeRootPoint_mul (d : LocalBlockInput m) (positive : Bool) (a b c e : CoefficientField m) :
    nativeRootPoint d positive a b * nativeRootPoint d positive c e =
      nativeRootPoint d positive (a+c) (b+e+a*titsEnd m c) := by
  apply Subtype.ext
  apply Subtype.ext
  exact sourceWord_mul positive a b c e

open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- Source and native Tits maps are the same field map; native `theta` is its inverse. -/
theorem suzukiTits_eq_titsEnd (a : CoefficientField m) : suzukiTits m a = titsEnd m a :=
  (suzukiTits_apply m a).trans (titsEnd_apply m a).symm

private def sourceRootEquivAux (d : LocalBlockInput m) (positive : Bool) :
    simpleRoot Q split i ≃ simpleBlock d .suzuki positive :=
  (Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm.trans
    (Equiv.ofBijective _ (nativeRootPoint_bijective d positive))

private theorem sourceRootEquivAux_parameter (d : LocalBlockInput m) (positive : Bool)
    (a b : CoefficientField m) :
    sourceRootEquivAux Q split i μ hB d positive (suzukiParameter Q split i m μ hB a b) =
      nativeRootPoint d positive a b := by
  change (Equiv.ofBijective _ (nativeRootPoint_bijective d positive))
    ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm
      ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)) (a,b))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The actual source Suzuki root is identified with a full native signed fixed root.
This is a root isomorphism, not a recognition theorem for the whole source group. -/
def sourceRootEquiv (d : LocalBlockInput m) (positive : Bool) :
    simpleRoot Q split i ≃* simpleBlock d .suzuki positive where
  toEquiv := (Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm.trans
    (Equiv.ofBijective _ (nativeRootPoint_bijective d positive))
  map_mul' x y := by
    change sourceRootEquivAux Q split i μ hB d positive (x*y) =
      sourceRootEquivAux Q split i μ hB d positive x *
      sourceRootEquivAux Q split i μ hB d positive y
    obtain ⟨⟨a,b⟩,hp⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective x
    obtain ⟨⟨c,e⟩,hq⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective y
    change suzukiParameter Q split i m μ hB a b = x at hp
    change suzukiParameter Q split i m μ hB c e = y at hq
    rw [← hp, ← hq, suzukiParameter_mul]
    rw [sourceRootEquivAux_parameter, sourceRootEquivAux_parameter, sourceRootEquivAux_parameter]
    rw [nativeRootPoint_mul, suzukiTits_eq_titsEnd]

@[simp] theorem sourceRootEquiv_parameter (d : LocalBlockInput m) (positive : Bool)
    (a b : CoefficientField m) :
    sourceRootEquiv Q split i μ hB d positive (suzukiParameter Q split i m μ hB a b) =
      nativeRootPoint d positive a b := sourceRootEquivAux_parameter Q split i μ hB d positive a b

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.NativeSuzukiChart
