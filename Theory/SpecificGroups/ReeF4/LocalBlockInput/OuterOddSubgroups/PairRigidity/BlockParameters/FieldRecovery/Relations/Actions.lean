module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Parameters

/-!
# The parameter maps induced on the Ree Suzuki blocks

In the supplied complete type V coordinates, the elements whose square is
one are exactly those with first parameter zero. Every block automorphism
therefore induces additive equivalences on the first and central parameters.
Its remaining central displacement satisfies the explicit product identity
`suzukiShear_defect`.

The square parameter is `N(t) = theta(t)^2 * t`. It is surjective, with
preimage `titsEnd(t) / t`, because the Tits endomorphism squared is Frobenius.
Consequently a semilinear first parameter forces the central scale
`N(c) = c * theta(c)^2`, regardless of the displacement. For `m ≥ 1`, `N`
is not additive; this also eliminates an additive displacement whenever its
central-character homogeneity has been proved.

`PureSuzukiAction` and `SignedLinearAction` state the two outstanding group
calculations used by `Relations`. They are intermediate obligations, not
consequences asserted here of pair preservation. The full two-parameter
Suzuki action is proved from the pure-curve action by squaring and factoring.

Source: GLS3, Table 2.4 type V, 2.4.1, 2.4.5(d), and 2.5.1(b,c), in
`refs/KGroup/GLS3/chapter2.tex`. Throughout, `theta = 2^m` is the inverse
Tits power, so `theta(t)^2 = titsEnd(t)`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
variable {m : ℕ}

theorem theta_sq (t : CoefficientField m) : (theta m t)^2 = titsEnd m t := by
  rw [theta_apply, titsEnd_apply, ← pow_mul, ← pow_succ]

def suzukiSquareParameter (t : CoefficientField m) : CoefficientField m :=
  (theta m t)^2 * t

theorem suzukiSquareParameter_eq (t : CoefficientField m) :
     suzukiSquareParameter t = titsEnd m t * t := by
  rw [suzukiSquareParameter, theta_sq]

theorem suzukiSquareParameter_inverse (t : CoefficientField m) :
     suzukiSquareParameter (titsEnd m t / t) = t := by
  rw [suzukiSquareParameter_eq, map_div₀, titsEnd_twice]
  by_cases ht : t = 0
  · simp [ht]
  · have hpi : titsEnd m t ≠ 0 := (map_ne_zero (titsEnd m)).mpr ht
    field_simp

theorem suzukiSquareParameter_surjective :
     Function.Surjective (suzukiSquareParameter (m := m)) :=
  fun t => ⟨titsEnd m t / t, suzukiSquareParameter_inverse t⟩

theorem suzukiSquareParameter_eq_zero {t : CoefficientField m} :
     suzukiSquareParameter t = 0 ↔ t = 0 := by
  simp [suzukiSquareParameter, map_eq_zero]

namespace SuzukiCoordinates
variable {d : LocalBlockInput m} (C : SuzukiCoordinates d)

theorem element_injective (positive : Bool) {t u v w : CoefficientField m}
     (h : C.element positive t u = C.element positive v w) : t = v ∧ u = w := by
  exact Prod.mk.inj (C.suzuki_injective positive (congrArg Subtype.val h))

theorem element_mul (positive : Bool) (t u v w : CoefficientField m) :
     C.element positive t u * C.element positive v w =
       C.element positive (t + v) (u + w + (theta m t)^2 * v) :=
  Subtype.ext (C.suzuki_mul positive t u v w)

@[simp] theorem element_zero (positive : Bool) : C.element positive 0 0 = 1 := by
  have h := C.element_mul positive 0 0 0 0
  simp only [map_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

theorem element_square (positive : Bool) (t u : CoefficientField m) :
     C.element positive t u ^ 2 = C.element positive 0 (suzukiSquareParameter t) := by
  rw [pow_two, C.element_mul]
  simp only [CharTwo.add_self_eq_zero, zero_add, suzukiSquareParameter]

theorem element_square_eq_one_iff (positive : Bool) (t u : CoefficientField m) :
     C.element positive t u ^ 2 = 1 ↔ t = 0 := by
  rw [C.element_square, ← C.element_zero positive]
  constructor
  · intro h
    exact suzukiSquareParameter_eq_zero.mp (C.element_injective positive h).2
  · intro h
    subst t
    simp [suzukiSquareParameter]

theorem element_factor (positive : Bool) (t u : CoefficientField m) :
     C.element positive t u = C.element positive t 0 * C.element positive 0 u := by
  rw [C.element_mul]
  simp

def blockEquiv (positive : Bool) :
     (CoefficientField m × CoefficientField m) ≃ simpleBlock d .suzuki positive :=
  Equiv.ofBijective (fun p => ⟨C.element positive p.1 p.2, C.element_mem positive p.1 p.2⟩)
    ⟨fun p q h => Prod.ext (C.element_injective positive (congrArg Subtype.val h)).1
        (C.element_injective positive (congrArg Subtype.val h)).2,
      fun x => by
        obtain ⟨t, u, h⟩ := C.element_cover positive x.property
        exact ⟨(t,u), Subtype.ext h⟩⟩

end SuzukiCoordinates

def suzukiParameterEquiv (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d) (positive : Bool) :
     (CoefficientField m × CoefficientField m) ≃ (CoefficientField m × CoefficientField m) :=
  (C.blockEquiv positive).trans
    ((blockRestriction d a hb .suzuki positive).toEquiv.trans (C.blockEquiv positive).symm)

theorem suzukiParameterEquiv_action (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
     (positive : Bool) (t u : CoefficientField m) :
     a (C.element positive t u) = C.element positive
       (suzukiParameterEquiv d a hb C positive (t,u)).1
       (suzukiParameterEquiv d a hb C positive (t,u)).2 := by
  change _ = ((C.blockEquiv positive) ((C.blockEquiv positive).symm
    (blockRestriction d a hb .suzuki positive (C.blockEquiv positive (t,u))))).val
  rw [Equiv.apply_symm_apply]
  rfl


section InducedAction
variable (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
  (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d) (positive : Bool)

def suzukiFirstParameter (t : CoefficientField m) : CoefficientField m :=
  (suzukiParameterEquiv d a hb C positive (t,0)).1

def suzukiShear (t : CoefficientField m) : CoefficientField m :=
  (suzukiParameterEquiv d a hb C positive (t,0)).2

def suzukiCentralParameter (u : CoefficientField m) : CoefficientField m :=
  (suzukiParameterEquiv d a hb C positive (0,u)).2

theorem suzukiParameterEquiv_zero_first (u : CoefficientField m) :
     (suzukiParameterEquiv d a hb C positive (0,u)).1 = 0 := by
  apply (C.element_square_eq_one_iff positive _ _).mp
  rw [← suzukiParameterEquiv_action, ← map_pow]
  rw [(C.element_square_eq_one_iff positive 0 u).mpr rfl, map_one]

theorem suzuki_action_central (u : CoefficientField m) :
     a (C.element positive 0 u) =
       C.element positive 0 (suzukiCentralParameter d a hb C positive u) := by
  rw [suzukiParameterEquiv_action, suzukiParameterEquiv_zero_first]
  rfl

theorem suzuki_action_pure (t : CoefficientField m) :
     a (C.element positive t 0) = C.element positive
       (suzukiFirstParameter d a hb C positive t) (suzukiShear d a hb C positive t) :=
  suzukiParameterEquiv_action d a hb C positive t 0

theorem suzuki_action (t u : CoefficientField m) :
     a (C.element positive t u) = C.element positive
       (suzukiFirstParameter d a hb C positive t)
       (suzukiShear d a hb C positive t + suzukiCentralParameter d a hb C positive u) := by
  rw [C.element_factor positive t u, map_mul, suzuki_action_pure d a hb C positive, suzuki_action_central d a hb C positive,
    C.element_mul]
  simp

theorem suzukiFirstParameter_add (t v : CoefficientField m) :
     suzukiFirstParameter d a hb C positive (t + v) =
       suzukiFirstParameter d a hb C positive t + suzukiFirstParameter d a hb C positive v := by
  have h := congrArg a (C.element_mul positive t 0 v 0)
  rw [map_mul, suzuki_action_pure, suzuki_action_pure, C.element_mul, suzuki_action] at h
  exact (C.element_injective positive h).1.symm

theorem suzukiCentralParameter_add (u w : CoefficientField m) :
     suzukiCentralParameter d a hb C positive (u + w) =
       suzukiCentralParameter d a hb C positive u + suzukiCentralParameter d a hb C positive w := by
  have h := congrArg a (C.element_mul positive 0 u 0 w)
  simp only [map_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at h
  rw [map_mul, suzuki_action_central, suzuki_action_central, suzuki_action_central,
    C.element_mul] at h
  simpa only [map_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
    using (C.element_injective positive h).2.symm

theorem suzukiFirstParameter_zero : suzukiFirstParameter d a hb C positive 0 = 0 :=
  suzukiParameterEquiv_zero_first d a hb C positive 0

theorem suzukiCentralParameter_zero : suzukiCentralParameter d a hb C positive 0 = 0 := by
  refine (C.element_injective positive (t := 0) (v := 0) ?_).2
  rw [← suzuki_action_central, C.element_zero, map_one]

theorem suzukiShear_zero : suzukiShear d a hb C positive 0 = 0 := by
  have h := suzuki_action_pure d a hb C positive 0
  rw [C.element_zero, map_one, suzukiFirstParameter_zero] at h
  exact (C.element_injective positive (h.symm.trans (C.element_zero positive).symm)).2

def suzukiFirstHom : CoefficientField m →+ CoefficientField m where
  toFun := suzukiFirstParameter d a hb C positive
  map_zero' := suzukiFirstParameter_zero d a hb C positive
  map_add' := suzukiFirstParameter_add d a hb C positive

def suzukiCentralHom : CoefficientField m →+ CoefficientField m where
  toFun := suzukiCentralParameter d a hb C positive
  map_zero' := suzukiCentralParameter_zero d a hb C positive
  map_add' := suzukiCentralParameter_add d a hb C positive

theorem suzukiCentralParameter_injective :
     Function.Injective (suzukiCentralParameter d a hb C positive) := by
  intro u w h
  refine (C.element_injective positive (t := 0) (v := 0) ?_).2
  apply a.injective
  rw [suzuki_action_central d a hb C positive, suzuki_action_central d a hb C positive, h]

theorem suzukiFirstParameter_injective :
     Function.Injective (suzukiFirstParameter d a hb C positive) := by
  apply (injective_iff_map_eq_zero (suzukiFirstHom d a hb C positive)).mpr
  intro t ht
  apply (C.element_square_eq_one_iff positive t 0).mp
  apply a.injective
  rw [map_one, map_pow, suzuki_action_pure d a hb C positive]
  exact (C.element_square_eq_one_iff positive _ _).mpr ht

def suzukiFirstAut : CoefficientField m ≃+ CoefficientField m :=
  AddEquiv.ofBijective (suzukiFirstHom d a hb C positive)
    (Finite.injective_iff_bijective.mp (suzukiFirstParameter_injective d a hb C positive))

def suzukiCentralAut : CoefficientField m ≃+ CoefficientField m :=
  AddEquiv.ofBijective (suzukiCentralHom d a hb C positive)
    (Finite.injective_iff_bijective.mp (suzukiCentralParameter_injective d a hb C positive))

theorem suzukiCentralParameter_square (t : CoefficientField m) :
     suzukiCentralParameter d a hb C positive (suzukiSquareParameter t) =
       suzukiSquareParameter (suzukiFirstParameter d a hb C positive t) := by
  have h := congrArg a (C.element_square positive t 0)
  rw [map_pow, suzuki_action_pure, C.element_square, suzuki_action_central] at h
  exact (C.element_injective positive h).2.symm

theorem suzukiShear_defect (t v : CoefficientField m) :
     suzukiShear d a hb C positive (t + v) +
         suzukiCentralParameter d a hb C positive ((theta m t)^2 * v) =
       suzukiShear d a hb C positive t + suzukiShear d a hb C positive v +
         (theta m (suzukiFirstParameter d a hb C positive t))^2 *
           suzukiFirstParameter d a hb C positive v := by
  have h := congrArg a (C.element_mul positive t 0 v 0)
  simp only [zero_add] at h
  rw [map_mul, suzuki_action_pure, suzuki_action_pure, C.element_mul, suzuki_action] at h
  exact (C.element_injective positive h).2.symm

end InducedAction

theorem suzukiSquareParameter_mul (t v : CoefficientField m) :
     suzukiSquareParameter (t * v) = suzukiSquareParameter t * suzukiSquareParameter v := by
  simp only [suzukiSquareParameter, map_mul, mul_pow]
  ring

theorem suzukiSquareParameter_field (σ : CoefficientField m ≃+* CoefficientField m)
     (t : CoefficientField m) : σ (suzukiSquareParameter t) = suzukiSquareParameter (σ t) := by
  simp only [suzukiSquareParameter, map_mul, map_pow, theta_field]

theorem centralScale_coe (c : (CoefficientField m)ˣ) :
     (centralScale c : CoefficientField m) = suzukiSquareParameter (c : CoefficientField m) := by
  change (c : CoefficientField m) * (theta m c)^2 = (theta m c)^2 * c
  exact mul_comm _ _

theorem suzukiSquareParameter_signedScale (c : (CoefficientField m)ˣ) (positive : Bool) :
     suzukiSquareParameter (signedScale c positive : CoefficientField m) =
       (signedScale (centralScale c) positive : CoefficientField m) := by
  cases positive
  · simp only [signedScale, Bool.false_eq_true, ↓reduceIte, Units.val_inv_eq_inv_val]
    rw [centralScale_coe]
    simp only [suzukiSquareParameter, map_inv₀, inv_pow, mul_inv_rev]
    exact mul_comm _ _
  · exact (centralScale_coe c).symm

theorem suzukiCentralParameter_of_first
     (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d) (positive : Bool)
     (c : CoefficientField m) (σ : CoefficientField m ≃+* CoefficientField m)
     (hfirst : ∀ t, suzukiFirstParameter d a hb C positive t = c * σ t)
     (u : CoefficientField m) :
     suzukiCentralParameter d a hb C positive u = suzukiSquareParameter c * σ u := by
  obtain ⟨t, rfl⟩ := suzukiSquareParameter_surjective u
  rw [suzukiCentralParameter_square, hfirst, suzukiSquareParameter_mul,
    suzukiSquareParameter_field]

/-- Once the first parameter is semilinear, its possible central displacement is additive. -/
theorem suzukiShear_add_of_first
     (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d) (positive : Bool)
     (c : CoefficientField m) (σ : CoefficientField m ≃+* CoefficientField m)
     (hfirst : ∀ t, suzukiFirstParameter d a hb C positive t = c * σ t)
     (t v : CoefficientField m) :
     suzukiShear d a hb C positive (t + v) =
       suzukiShear d a hb C positive t + suzukiShear d a hb C positive v := by
  have hcross : suzukiSquareParameter c * σ ((theta m t)^2 * v) =
      (theta m (c * σ t))^2 * (c * σ v) := by
    simp only [suzukiSquareParameter, map_mul, map_pow, theta_field, mul_pow]
    ring
  have h := suzukiShear_defect d a hb C positive t v
  rw [suzukiCentralParameter_of_first d a hb C positive c σ hfirst,
    hfirst, hfirst, hcross] at h
  exact add_right_cancel h

theorem suzukiSquareParameter_not_additive (hm : 1 ≤ m) : ∃ t : CoefficientField m, suzukiSquareParameter (t+1) ≠ suzukiSquareParameter t + 1 := by
  classical
  have hcard : 2 < Fintype.card (CoefficientField m) := by
    rw [← Nat.card_eq_fintype_card, field_card]
    calc
      2 < 2 ^ 3 := by decide
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hfin : ({0, 1} : Finset (CoefficientField m)).card < (Finset.univ : Finset (CoefficientField m)).card := by
    simpa using hcard
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hfin
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  have hpi : titsEnd m t ≠ t := by
    intro he
    have hsq := titsEnd_twice m t
    rw [he, he] at hsq
    apply ht.2
    exact mul_left_cancel₀ ht.1 (by simpa [pow_two] using hsq.symm)
  refine ⟨t, fun he => hpi ?_⟩
  have he' : titsEnd m t + t = 0 := by
    simp only [suzukiSquareParameter_eq, map_add, map_one] at he
    linear_combination he
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left he'

/-- A displacement with the central root character vanishes for the large Ree fields. -/
theorem suzukiShear_eq_zero_of_homogeneous
     (hm : 1 ≤ m) (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d) (positive : Bool)
     (c : CoefficientField m) (σ : CoefficientField m ≃+* CoefficientField m)
     (hfirst : ∀ t, suzukiFirstParameter d a hb C positive t = c * σ t)
     (hhom : ∀ t, suzukiShear d a hb C positive t =
       suzukiSquareParameter (σ t) * suzukiShear d a hb C positive 1)
     (t : CoefficientField m) : suzukiShear d a hb C positive t = 0 := by
  obtain ⟨r, hr⟩ := suzukiSquareParameter_not_additive hm
  have h := suzukiShear_add_of_first d a hb C positive c σ hfirst (σ.symm r) 1
  rw [hhom (σ.symm r + 1), hhom (σ.symm r), map_add, map_one,
    RingEquiv.apply_symm_apply] at h
  have hz : (suzukiSquareParameter (r + 1) - (suzukiSquareParameter r + 1)) *
      suzukiShear d a hb C positive 1 = 0 := by linear_combination h
  have h1 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hr)
  rw [hhom, h1, mul_zero]

/-- The first-parameter curves have no central displacement, and share the
field map of the linear blocks. The two signs use inverse scales. -/
def PureSuzukiAction (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (C : SuzukiCoordinates d) (c : (CoefficientField m)ˣ)
     (σ : CoefficientField m ≃+* CoefficientField m) : Prop :=
  ∀ positive t, a (C.element positive t 0) =
    C.element positive ((signedScale c positive : CoefficientField m) * σ t) 0

/-- The full central action follows from squares of first-parameter elements. -/
theorem suzuki_central_action_of_pure
     (d : LocalBlockInput m) (a : MulAut d.fixedGroup) (C : SuzukiCoordinates d)
     (c : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
     (h : PureSuzukiAction d a C c σ) (positive : Bool) (u : CoefficientField m) :
     a (C.element positive 0 u) = C.element positive 0
       ((signedScale (centralScale c) positive : CoefficientField m) * σ u) := by
  obtain ⟨t, rfl⟩ := suzukiSquareParameter_surjective u
  rw [← C.element_square positive t 0, map_pow, h, C.element_square,
    suzukiSquareParameter_mul, suzukiSquareParameter_signedScale,
    suzukiSquareParameter_field]

/-- Both type V parameters are determined by the pure-curve action. -/
theorem suzuki_action_of_pure
     (d : LocalBlockInput m) (a : MulAut d.fixedGroup) (C : SuzukiCoordinates d)
     (c : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
     (h : PureSuzukiAction d a C c σ) (positive : Bool) (t u : CoefficientField m) :
     a (C.element positive t u) = C.element positive
       ((signedScale c positive : CoefficientField m) * σ t)
       ((signedScale (centralScale c) positive : CoefficientField m) * σ u) := by
  rw [C.element_factor positive t u, map_mul, h,
    suzuki_central_action_of_pure d a C c σ h, C.element_mul]
  simp

/-- Common field action on the two opposite type VI blocks. -/
def SignedLinearAction (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m) : Prop :=
  ∀ positive t, a (linearElement d positive t) =
    linearElement d positive ((signedScale b positive : CoefficientField m) * σ t)


end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
end
