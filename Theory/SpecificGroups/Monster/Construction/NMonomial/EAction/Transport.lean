module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.Forms
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.NaturalAction

/-!
# Signed coordinate transport for the full Parker triality group

The action is recovered from the images of the actual coordinate halfspaces
on all three Parker axes. Every generator has a common coordinate permutation,
an axis permutation, and coordinate signs whose sum over the axes is zero.
These properties are closed under composition and inversion. Uniqueness of
halfspace labels makes the recovered permutations homomorphisms.

Source: Aschbacher, *Sporadic Groups*, 27.4 and 29.10, printed pp. 146, 158–159.
Products here act on the left: `g * h` first applies `h`, then `g`. Thus the
source's right-action word `psi1(d) psi2(e) psi1(alpha)` is represented by
`psiAut1N alpha * psi2N e * psi1N d`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace Sporadic.Monster.Construction.NMonomial.EAction
open TrialitySpin SignedModules.Natural Atlas.Codes Atlas.Fischer

private theorem point_axis_injective {i j : Axis} {d e : ParkerLoop}
    (h : point i d = point j e) : i = j := by
  fin_cases i <;> fin_cases j <;> first | rfl | simp [point, axis1, axis2, axis3] at h

/-- A halfspace remembers its axis as well as its signed coordinate. -/
theorem halfspace_axis_label_injective :
    Function.Injective (fun p : Axis × Label => halfspace p.1 p.2) := by
  rintro ⟨i,l⟩ ⟨j,m⟩ h
  obtain ⟨a,ha⟩ := halfspace_nonempty i l
  have hb : a ∈ halfspace j m := Set.ext_iff.mp h a |>.mp ha
  obtain ⟨d,_,hd⟩ := ha
  obtain ⟨e,_,he⟩ := hb
  have hij := point_axis_injective (hd.trans he.symm)
  subst j
  exact Prod.ext rfl (halfspace_injective i h)

/-- Coordinate data of a signed action on the three genuine halfspace families. -/
structure TransportData where
  axes : Equiv.Perm Axis
  coords : Equiv.Perm Omega
  shift : Axis → Omega → ParkerBit

/-- The data describe images of actual subsets of the Parker triple carrier. -/
def TransportData.Realizes (D : TransportData) (g : Equiv.Perm Triple) : Prop :=
  ∀ i x ε, g '' halfspace i (x,ε) =
    halfspace (D.axes i) (D.coords x, ε + D.shift i x)

/-- The signs on the three axes multiply to one at every marked coordinate. -/
def TransportData.Balanced (D : TransportData) : Prop :=
  ∀ x, ∑ i, D.shift i x = 0

private def identityData : TransportData := ⟨1,1,fun _ _ => 0⟩

private theorem identity_realizes : identityData.Realizes 1 := by
  intro i x ε
  simp [identityData]

private theorem identity_balanced : identityData.Balanced := by
  intro x
  simp [identityData]

private def multiplyData (D E : TransportData) : TransportData :=
  ⟨D.axes * E.axes, D.coords * E.coords,
    fun i x => E.shift i x + D.shift (E.axes i) (E.coords x)⟩

private theorem multiply_realizes {D E : TransportData} {g h : Equiv.Perm Triple}
    (hg : D.Realizes g) (hh : E.Realizes h) : (multiplyData D E).Realizes (g * h) := by
  intro i x ε
  change (g ∘ h) '' halfspace i (x,ε) = _
  rw [Set.image_comp, hh, hg]
  simp [multiplyData, add_assoc]

private theorem multiply_balanced {D E : TransportData}
    (hD : D.Balanced) (hE : E.Balanced) : (multiplyData D E).Balanced := by
  intro x
  change (∑ i, (E.shift i x + D.shift (E.axes i) (E.coords x))) = 0
  rw [Finset.sum_add_distrib, hE, Equiv.sum_comp E.axes (fun i => D.shift i (E.coords x)), hD, add_zero]

private def inverseData (D : TransportData) : TransportData :=
  ⟨D.axes⁻¹, D.coords⁻¹, fun i x => -D.shift (D.axes⁻¹ i) (D.coords⁻¹ x)⟩

private theorem inverse_realizes {D : TransportData} {g : Equiv.Perm Triple}
    (hg : D.Realizes g) : (inverseData D).Realizes g⁻¹ := by
  intro i x ε
  apply g.injective.image_injective
  rw [← Set.image_comp]
  simp only [Equiv.Perm.inv_def, Equiv.self_comp_symm, Set.image_id]
  rw [hg]
  simp [inverseData, add_assoc]

private theorem inverse_balanced {D : TransportData} (hD : D.Balanced) :
    (inverseData D).Balanced := by
  intro x
  change (∑ i, -D.shift (D.axes⁻¹ i) (D.coords⁻¹ x)) = 0
  rw [Finset.sum_neg_distrib, Equiv.sum_comp D.axes⁻¹ (fun i => D.shift i (D.coords⁻¹ x)), hD, neg_zero]

/-- The loop generators as an indexed family of actual elements of `N`. -/
def loopGenerator : Axis → ParkerLoop → N
  | 0 => psi1N
  | 1 => psi2N
  | 2 => psi3N

@[simp] theorem loopGenerator_val (i : Axis) (d : ParkerLoop) :
    (loopGenerator i d).val = psiAt i d := by fin_cases i <;> rfl

/-- All three families of genuine standard-automorphism generators. -/
def standardGenerator (i : Axis) (α : ParkerStandardGroup) : N :=
  ⟨psiAutAt i α.val, by
    fin_cases i
    · exact psiAut1_mem_N α.val α.prop
    · exact psiAut2_mem_N α.val α.prop
    · exact psiAut3_mem_N α.val α.prop⟩

/-- The axis permutation fixes its own axis and, for odd parity, swaps the other two. -/
def standardAxes (i : Axis) (α : ParkerStandardGroup) : Equiv.Perm Axis where
  toFun := autTarget i α.val
  invFun := autTarget i α.val
  left_inv j := by
    by_cases h : α.val parkerOmega = parkerOmega
    · simp [autTarget, h]
    · fin_cases i <;> fin_cases j <;> simp [autTarget, h, oddAxis]
  right_inv j := by
    by_cases h : α.val parkerOmega = parkerOmega
    · simp [autTarget, h]
    · fin_cases i <;> fin_cases j <;> simp [autTarget, h, oddAxis]

private def loopData (i : Axis) (d : ParkerLoop) : TransportData :=
  ⟨1, 1, fun j x => if i = j then 0 else d.1.val x⟩

private theorem loop_realizes (i : Axis) (d : ParkerLoop) :
    (loopData i d).Realizes (psiAt i d) := by
  intro j x ε
  exact psi_halfspace i j d x ε

private theorem loop_balanced (i : Axis) (d : ParkerLoop) : (loopData i d).Balanced := by
  intro x
  fin_cases i <;> simp [loopData, Fin.sum_univ_three]

private def standardData (i : Axis) (α : ParkerStandardGroup) : TransportData :=
  ⟨standardAxes i α, (parkerStandardProjection α).val, fun _ _ => 0⟩

private theorem standard_realizes (i : Axis) (α : ParkerStandardGroup) :
    (standardData i α).Realizes (psiAutAt i α.val) := by
  intro j x ε
  simpa [standardData, standardAxes] using standard_halfspace i j α x ε

private theorem standard_balanced (i : Axis) (α : ParkerStandardGroup) :
    (standardData i α).Balanced := by intro x; simp [standardData]

/-- Existence is proved from the actual generators of `N`, including inverse words. -/
theorem exists_transportData (g : N) : ∃ D : TransportData, D.Realizes g.val ∧ D.Balanced := by
  rcases g with ⟨g,hg⟩
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ((⟨d,rfl⟩ | ⟨d,rfl⟩) | ⟨d,rfl⟩) | ⟨e,he,hg⟩
    · exact ⟨loopData 0 d, loop_realizes 0 d, loop_balanced 0 d⟩
    · exact ⟨loopData 1 d, loop_realizes 1 d, loop_balanced 1 d⟩
    · exact ⟨loopData 2 d, loop_realizes 2 d, loop_balanced 2 d⟩
    · rcases hg with rfl | rfl | rfl
      · exact ⟨standardData 0 ⟨e,he⟩, standard_realizes 0 ⟨e,he⟩, standard_balanced 0 ⟨e,he⟩⟩
      · exact ⟨standardData 1 ⟨e,he⟩, standard_realizes 1 ⟨e,he⟩, standard_balanced 1 ⟨e,he⟩⟩
      · exact ⟨standardData 2 ⟨e,he⟩, standard_realizes 2 ⟨e,he⟩, standard_balanced 2 ⟨e,he⟩⟩
  | one => exact ⟨identityData, identity_realizes, identity_balanced⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨D,hD,bD⟩ := ihg
    obtain ⟨E,hE,bE⟩ := ihh
    exact ⟨multiplyData D E, multiply_realizes hD hE, multiply_balanced bD bE⟩
  | inv g _ ih =>
    obtain ⟨D,hD,bD⟩ := ih
    exact ⟨inverseData D, inverse_realizes hD, inverse_balanced bD⟩

/-- Coordinate data are intrinsic: no word or chosen presentation changes them. -/
theorem TransportData.ext_of_realizes {D E : TransportData} {g : Equiv.Perm Triple}
    (hD : D.Realizes g) (hE : E.Realizes g) : D = E := by
  have hp (i : Axis) (x : Omega) :
      (D.axes i, (D.coords x, D.shift i x)) = (E.axes i, (E.coords x, E.shift i x)) := by
    apply halfspace_axis_label_injective
    simpa using (hD i x 0).symm.trans (hE i x 0)
  have ha : D.axes = E.axes := by
    apply Equiv.ext
    intro i
    exact congrArg Prod.fst (hp i (((0,0),0) : Omega))
  have hc : D.coords = E.coords := by
    apply Equiv.ext
    intro x
    exact congrArg (fun p => p.2.1) (hp 0 x)
  have hs : D.shift = E.shift := by
    funext i x
    exact congrArg (fun p => p.2.2) (hp i x)
  cases D; cases E; cases ha; cases hc; cases hs; rfl

/-- The unique signed coordinate description of the actual triality permutation. -/
def transportData (g : N) : TransportData := (exists_transportData g).choose

theorem transportData_realizes (g : N) : (transportData g).Realizes g.val :=
  (exists_transportData g).choose_spec.1

theorem transportData_balanced (g : N) : (transportData g).Balanced :=
  (exists_transportData g).choose_spec.2

private theorem transportData_one : transportData 1 = identityData :=
  TransportData.ext_of_realizes (transportData_realizes 1) identity_realizes

private theorem transportData_mul (g h : N) :
    transportData (g*h) = multiplyData (transportData g) (transportData h) :=
  TransportData.ext_of_realizes (transportData_realizes (g*h))
    (multiply_realizes (transportData_realizes g) (transportData_realizes h))

/-- The genuine permutation of the three Parker axes. -/
def axisPermutation : N →* Equiv.Perm Axis where
  toFun g := (transportData g).axes
  map_one' := by exact congrArg TransportData.axes transportData_one
  map_mul' g h := by exact congrArg TransportData.axes (transportData_mul g h)

/-- The common marked coordinate permutation in the signed natural construction.
This is also the permutation needed on the diagonal Griess summand. -/
def coordinatePermutation : N →* Equiv.Perm Omega where
  toFun g := (transportData g).coords
  map_one' := by exact congrArg TransportData.coords transportData_one
  map_mul' g h := by exact congrArg TransportData.coords (transportData_mul g h)

/-- A bit records the sign of each transported natural coordinate. -/
def coordinateShift (g : N) (i : Axis) (x : Omega) : ParkerBit :=
  (transportData g).shift i x

@[simp] theorem coordinateShift_one (i : Axis) (x : Omega) : coordinateShift 1 i x = 0 := by
  simp [coordinateShift, transportData_one, identityData]

theorem coordinateShift_mul (g h : N) (i : Axis) (x : Omega) :
    coordinateShift (g*h) i x = coordinateShift h i x +
      coordinateShift g (axisPermutation h i) (coordinatePermutation h x) := by
  simp [coordinateShift, transportData_mul, multiplyData, axisPermutation, coordinatePermutation]

/-- The three signs cancel in the mixed three-axis cubic coefficient. -/
theorem coordinateShift_sum (g : N) (x : Omega) : ∑ i, coordinateShift g i x = 0 :=
  transportData_balanced g x

/-- Forward coordinate transport, including the source halfspace bit. -/
theorem image_halfspace (g : N) (i : Axis) (x : Omega) (ε : ParkerBit) :
    g.val '' halfspace i (x,ε) = halfspace (axisPermutation g i)
      (coordinatePermutation g x, ε + coordinateShift g i x) :=
  transportData_realizes g i x ε

private theorem transportData_loop (i : Axis) (d : ParkerLoop) :
    transportData (loopGenerator i d) = loopData i d :=
  TransportData.ext_of_realizes (transportData_realizes _) (by
    rw [loopGenerator_val]; exact loop_realizes i d)

private theorem transportData_standard (i : Axis) (α : ParkerStandardGroup) :
    transportData (standardGenerator i α) = standardData i α :=
  TransportData.ext_of_realizes (transportData_realizes _) (standard_realizes i α)

@[simp] theorem axisPermutation_loop (i : Axis) (d : ParkerLoop) :
    axisPermutation (loopGenerator i d) = 1 :=
  congrArg TransportData.axes (transportData_loop i d)

@[simp] theorem coordinatePermutation_loop (i : Axis) (d : ParkerLoop) :
    coordinatePermutation (loopGenerator i d) = 1 :=
  congrArg TransportData.coords (transportData_loop i d)

@[simp] theorem coordinateShift_loop (i j : Axis) (d : ParkerLoop) (x : Omega) :
    coordinateShift (loopGenerator i d) j x = if i = j then 0 else d.1.val x :=
  congrArg (fun D => D.shift j x) (transportData_loop i d)

@[simp] theorem axisPermutation_standard (i : Axis) (α : ParkerStandardGroup) :
    axisPermutation (standardGenerator i α) = standardAxes i α :=
  congrArg TransportData.axes (transportData_standard i α)

@[simp] theorem coordinatePermutation_standard (i : Axis) (α : ParkerStandardGroup) :
    coordinatePermutation (standardGenerator i α) = (parkerStandardProjection α).val :=
  congrArg TransportData.coords (transportData_standard i α)

@[simp] theorem coordinateShift_standard (i j : Axis) (α : ParkerStandardGroup) (x : Omega) :
    coordinateShift (standardGenerator i α) j x = 0 :=
  congrArg (fun D => D.shift j x) (transportData_standard i α)

/-- The global action restricts to the actual first-axis natural action of `N1`. -/
theorem axisPermutation_n1 (g : N1) : axisPermutation g.val 0 = 0 := by
  let x : Omega := ((0,0),0)
  have h : (axisPermutation g.val 0,
      (coordinatePermutation g.val x, 0 + coordinateShift g.val 0 x)) =
      (0, labelMap (SpinAction.permutations g) (NaturalAction.preserves_halfspaces g) (x,0)) :=
    halfspace_axis_label_injective
    ((image_halfspace g.val 0 x 0).symm.trans
      (SignedModules.Natural.image_halfspace (SpinAction.permutations g)
        (NaturalAction.preserves_halfspaces g) (x,0)))
  exact congrArg Prod.fst h

/-- This equality retains the coordinate sign; the permutation alone is not the natural action. -/
theorem naturalAction_L (g : N1) (x : Omega) (ε : ParkerBit) :
    NaturalAction.representation g (L 0 ε x) =
      L 0 (ε + coordinateShift g.val 0 x) (coordinatePermutation g.val x) := by
  change SignedModules.Natural.representation SpinAction.permutations
    NaturalAction.preserves_halfspaces g (L 0 ε x) = _
  rw [SignedModules.Natural.representation_L]
  have h := image_halfspace g.val 0 x ε
  rw [axisPermutation_n1] at h
  rw [labelEquiv_of_image (SpinAction.permutations g)
    (NaturalAction.preserves_halfspaces g) (x,ε) _ h]

theorem carries_halfspaces (g : N) (i : Axis) :
    Carries i (axisPermutation g i) g.val :=
  fun l => ⟨_, image_halfspace g i l.1 l.2⟩

/-- Transport on a single natural axis is induced by the literal triple permutation. -/
def naturalTransport (g : N) (i : Axis) : Space i ≃ₗ[ℝ] Space (axisPermutation g i) :=
  transport g.val (carries_halfspaces g i)

theorem naturalTransport_L (g : N) (i : Axis) (x : Omega) (ε : ParkerBit) :
    naturalTransport g i (L i ε x) =
      L (axisPermutation g i) (ε + coordinateShift g i x) (coordinatePermutation g x) := by
  unfold naturalTransport
  rw [transport_L, labelEquiv_of_image _ _ _ _ (image_halfspace g i x ε)]

theorem naturalTransport_isometry (g : N) (i : Axis) (v w : Space i) :
    form (axisPermutation g i) (naturalTransport g i v) (naturalTransport g i w) =
      form i v w := transport_isometry _ _ v w

/-- The coordinate permutation agrees with the actual standard projection in a collected word. -/
theorem coordinatePermutation_normalForm (d e : ParkerLoop) (α : ParkerStandardGroup) :
    coordinatePermutation (normalForm d e α).val = (parkerStandardProjection α).val := by
  change coordinatePermutation
    (standardGenerator 0 α * loopGenerator 1 e * loopGenerator 0 d) = _
  simp

theorem coordinateShift_normalForm (d e : ParkerLoop) (α : ParkerStandardGroup) (x : Omega) :
    coordinateShift (normalForm d e α).val 0 x = e.1.val x := by
  change coordinateShift
    (standardGenerator 0 α * loopGenerator 1 e * loopGenerator 0 d) 0 x = _
  simp [coordinateShift_mul]

/-- The actual natural action sends each marked basis vector to its globally transported
coordinate, with the computed possible minus sign. -/
theorem naturalAction_basis (g : N1) (x : Omega) :
    NaturalAction.representation g (basis 0 x) = basis 0 (coordinatePermutation g.val x) ∨
    NaturalAction.representation g (basis 0 x) = -basis 0 (coordinatePermutation g.val x) := by
  rw [basis_eq_L, naturalAction_L]
  have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
  rcases hb (coordinateShift g.val 0 x) with h | h
  · left; simp [h, basis_eq_L]
  · right; simp [h, L_zero]

/-- In particular the common coordinate permutation kills the prescribed kernel `K`. -/
theorem coordinatePermutation_of_mem_K {g : N} (hg : g ∈ TrialitySpin.K) : coordinatePermutation g = 1 := by
  apply (show TrialitySpin.K ≤ coordinatePermutation.ker from ?_) hg
  apply (Subgroup.closure_le _).2
  intro k hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl | rfl
  · change coordinatePermutation (loopGenerator 1 (parkerSign 1 parkerOmega) *
      loopGenerator 2 parkerOmega) = 1
    simp
  · change coordinatePermutation (loopGenerator 2 (parkerSign 1 parkerOmega) *
      loopGenerator 0 parkerOmega) = 1
    simp
  · change coordinatePermutation (loopGenerator 0 (parkerSign 1 parkerOmega) *
      loopGenerator 1 parkerOmega) = 1
    simp

end Sporadic.Monster.Construction.NMonomial.EAction
