module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootPoints
public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalDiagonalTorus

/-!
# The closed diagonal preimage and its Spin coroot point coordinates

The inverse image of the ordinary orthogonal diagonal torus under the regular
Spin cover is a closed subgroup of the actual Clifford carrier. The product of
the four source coroot words bijects onto this subgroup in characteristic two.
Its natural-action coordinates are
`(t₀⁻¹, t₀t₁⁻¹, t₁t₂⁻¹t₃⁻¹, t₂t₃⁻¹)`.

Injectivity uses injectivity of squaring in characteristic two; surjectivity
uses algebraic closedness. These are point arguments, not a regular inverse.
The regular map `ordinaryCoordinates` records precisely which coordinates are
already supplied by the orthogonal cover. Recovering a Spin coefficient and
proving regularity of the forward product remain separate obligations.

Source: GLS3, Theorems 1.12.1(c,d,f,g), 1.12.5(b), and §§1.14.1–2,
`refs/KGroup/GLS3/Chapter1.tex`. The signs use `h(t) = n(1)⁻¹ n(t)`.
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.CorootTorus
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The ordered product of the four published simple coroots. -/
def parameter (t : Fin 4 → kˣ) : Points k :=
  (List.ofFn fun i : Fin 4 => simpleCoroot k i (t i)).prod

/-- Ordinary orthogonal coordinates of the simple-coroot product. -/
def diagonal (t : Fin 4 → kˣ) : Fin 4 → kˣ :=
  ![(t 0)⁻¹, t 0 * (t 1)⁻¹, t 1 * (t 2)⁻¹ * (t 3)⁻¹, t 2 * (t 3)⁻¹]

omit [IsAlgClosed k] [CharP k 2] in
private theorem diagonalPoint_mul (d e : Fin 4 → kˣ) :
    hyperbolicDiagonalPoint 4 (d * e) =
      hyperbolicDiagonalPoint 4 d * hyperbolicDiagonalPoint 4 e := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext i <;>
    simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
      hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv, mul_assoc, mul_comm]

omit [IsAlgClosed k] [CharP k 2] in
private theorem diagonalPoint_one :
    hyperbolicDiagonalPoint (k := k) 4 1 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext i <;>
    simp [hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv]

theorem naturalAction_parameter (t : Fin 4 → kˣ) :
    naturalAction k (parameter k t) = hyperbolicDiagonalPoint 4 (diagonal k t) := by
  simp only [parameter, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, map_mul, map_one, simpleCoroot, naturalAction_corootWord]
  rw [← diagonalPoint_one k]
  simp only [← diagonalPoint_mul]
  congr 1
  funext i
  fin_cases i <;>
    norm_num [corootDiagonal, simpleRoot, typeDSimpleRootIndex, diagonal,
      Pi.mul_apply, mul_assoc, Fin.ext_iff, Fin.val_last] <;> rfl

omit [IsAlgClosed k] [CharP k 2] in
theorem diagonal_mul (t s : Fin 4 → kˣ) :
    diagonal k (t * s) = diagonal k t * diagonal k s := by
  funext i
  fin_cases i <;> simp [diagonal, mul_assoc, mul_comm, mul_left_comm]

theorem parameter_mul (t s : Fin 4 → kˣ) :
    parameter k (t * s) = parameter k t * parameter k s := by
  apply naturalAction_injective k
  rw [map_mul, naturalAction_parameter, naturalAction_parameter,
    naturalAction_parameter, diagonal_mul, diagonalPoint_mul]

@[simp] theorem parameter_one : parameter k 1 = 1 := by
  simp [parameter, corootWord_one]

def pointHom : (Fin 4 → kˣ) →* Points k where
  toFun := parameter k
  map_one' := parameter_one k
  map_mul' := parameter_mul k

/-- Algebraic pullback of the ordinary diagonal subgroup. -/
def closedSubgroup : ClosedSubgroup (groupVariety k) :=
  ClosedSubgroup.ofSubgroup
    ((evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).toSubgroup.comap
      (cliffordModel k).spinCover.onPoints)
    ((cliffordModel k).spinCover.toVariety.isZariskiClosed_preimage
      (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).isZariskiClosed)

instance closedSubgroupAlgebraicGroup : AlgebraicGroup (closedSubgroup k).carrierVariety :=
  (closedSubgroup k).carrierAlgebraicGroup

local instance ordinaryTorusAlgebraicGroup :
    AlgebraicGroup (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).carrierVariety :=
  (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).carrierAlgebraicGroup

omit [IsAlgClosed k] in
theorem diagonal_injective : Function.Injective (diagonal k) := by
  intro t s h
  have h3sq : t 3 ^ 2 = s 3 ^ 2 := by
    calc
      t 3 ^ 2 = (diagonal k t 0 * diagonal k t 1 *
          diagonal k t 2 * diagonal k t 3)⁻¹ := by simp [diagonal, mul_comm, mul_left_comm, mul_assoc, pow_two]
      _ = (diagonal k s 0 * diagonal k s 1 *
          diagonal k s 2 * diagonal k s 3)⁻¹ := by rw [h]
      _ = s 3 ^ 2 := by simp [diagonal, mul_comm, mul_left_comm, mul_assoc, pow_two]
  have h3 : t 3 = s 3 := by
    apply Units.ext
    apply CharTwo.sq_injective
    exact congrArg Units.val h3sq
  have h0 : t 0 = s 0 := inv_injective (congrFun h 0)
  have h1 : t 1 = s 1 := by
    have he := congrFun h 1
    change t 0 * (t 1)⁻¹ = s 0 * (s 1)⁻¹ at he
    rw [h0] at he
    exact inv_injective (mul_left_cancel he)
  have h2 : t 2 = s 2 := by
    have he := congrFun h 3
    change t 2 * (t 3)⁻¹ = s 2 * (s 3)⁻¹ at he
    rw [h3] at he
    exact mul_right_cancel he
  funext i
  fin_cases i <;> assumption

omit [CharP k 2] in
theorem diagonal_surjective : Function.Surjective (diagonal k) := by
  intro d
  obtain ⟨a, ha⟩ := units_zpow_surjective_of_isAlgClosed (k := k) 2 (by decide)
    ((d 0 * d 1 * d 2 * d 3)⁻¹)
  have haa : a * a = (d 0 * d 1 * d 2 * d 3)⁻¹ := by
    simpa only [zpow_ofNat, pow_two] using ha
  refine ⟨![(d 0)⁻¹, (d 0 * d 1)⁻¹, d 3 * a, a], ?_⟩
  funext i
  fin_cases i
  · simp [diagonal]
  · simp [diagonal]
  · change (d 0 * d 1)⁻¹ * (d 3 * a)⁻¹ * a⁻¹ = d 2
    calc
      _ = (d 0 * d 1 * d 3 * (a * a))⁻¹ := by simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
      _ = d 2 := by rw [haa]; simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  · simp [diagonal]

omit [IsAlgClosed k] [CharP k 2] in
private theorem diagonalPoint_injective :
    Function.Injective (hyperbolicDiagonalPoint (k := k) 4) := by
  intro d e h
  funext i
  apply Units.ext
  have hi := congrArg (fun f : quadraticIsometrySubgroup (quadraticForm k) =>
    (f.1 (Pi.single i 1, 0)).1 i) h
  simpa [hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
    hyperbolicDiagonalLinearEquiv] using hi

theorem parameter_injective : Function.Injective (parameter k) := by
  intro t s h
  apply diagonal_injective k
  apply diagonalPoint_injective k
  rw [← naturalAction_parameter, ← naturalAction_parameter, h]

omit [CharP k 2] in
private theorem omegaPoints_diagonal (x : Variety.Point (dVariety k 4)) :
    ((cliffordModel k).omegaPoints
      ((evenOrthogonalDiagonalMorphism (k := k) 4 (le_refl 4)).onPoints x)).1 =
        hyperbolicDiagonalPoint 4 (dPointEquiv 4 x) := by
  apply Subtype.ext
  exact ((cliffordModel k).omegaLinear_points _).symm.trans
    (evenOrthogonalDiagonalMorphism_linear_points 4 (le_refl 4) x)

theorem cover_parameter (t : Fin 4 → kˣ) :
    (cliffordModel k).spinCover.onPoints (parameter k t) =
      (evenOrthogonalDiagonalMorphism (k := k) 4 (le_refl 4)).onPoints
        ((dPointEquiv 4).symm (diagonal k t)) := by
  apply (cliffordModel k).omegaPoints.injective
  apply Subtype.ext
  change naturalAction k (parameter k t) = _
  rw [naturalAction_parameter, omegaPoints_diagonal, Equiv.apply_symm_apply]

theorem parameter_mem (t : Fin 4 → kˣ) :
    parameter k t ∈ (closedSubgroup k).toSubgroup := by
  exact ⟨(dPointEquiv 4).symm (diagonal k t), (cover_parameter k t).symm⟩

theorem mem_iff_parameter (g : Points k) :
    g ∈ (closedSubgroup k).toSubgroup ↔ ∃ t, parameter k t = g := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ := diagonal_surjective k (dPointEquiv 4 x)
    refine ⟨t, naturalAction_injective k ?_⟩
    change naturalAction k (parameter k t) =
      ((cliffordModel k).omegaPoints ((cliffordModel k).spinCover.onPoints g)).1
    rw [naturalAction_parameter, ← hx, omegaPoints_diagonal, ht]
  · rintro ⟨t, rfl⟩
    exact parameter_mem k t

/-- The coroot product regarded as a point of the closed diagonal preimage. -/
def parameterPoint (t : Fin 4 → kˣ) : Variety.Point (closedSubgroup k).carrierVariety :=
  (closedSubgroup k).pointEquiv.symm ⟨parameter k t, parameter_mem k t⟩

@[simp] theorem inclusion_parameterPoint (t : Fin 4 → kˣ) :
    (closedSubgroup k).inclusion.onPoints (parameterPoint k t) = parameter k t :=
  congrArg Subtype.val ((closedSubgroup k).pointEquiv.apply_symm_apply _)

/-- The exact product map on the points of the two varieties. -/
def coordinateHom : Variety.Point (dVariety k 4) →*
    Variety.Point (closedSubgroup k).carrierVariety where
  toFun x := parameterPoint k (dPointEquiv 4 x)
  map_one' := by
    apply (closedSubgroup k).inclusion_injective
    simp only [inclusion_parameterPoint, dPointEquiv_one, parameter_one, map_one]
  map_mul' x y := by
    apply (closedSubgroup k).inclusion_injective
    simp only [inclusion_parameterPoint, dPointEquiv_mul, parameter_mul, map_mul]

theorem coordinateHom_bijective : Function.Bijective (coordinateHom k) := by
  constructor
  · intro x y h
    apply (dPointEquiv 4).injective
    apply parameter_injective k
    simpa only [coordinateHom, MonoidHom.coe_mk, OneHom.coe_mk,
      inclusion_parameterPoint] using congrArg (closedSubgroup k).inclusion.onPoints h
  · intro y
    obtain ⟨t, ht⟩ := (mem_iff_parameter k _).mp ((closedSubgroup k).pointEquiv y).property
    refine ⟨(dPointEquiv 4).symm t, ?_⟩
    apply (closedSubgroup k).inclusion_injective
    change (closedSubgroup k).inclusion.onPoints
        (parameterPoint k (dPointEquiv 4 ((dPointEquiv 4).symm t))) = _
    rw [Equiv.apply_symm_apply, inclusion_parameterPoint]
    exact ht

/-- Point coordinates only; regularity in both directions is a separate obligation. -/
def coordinateEquiv : Variety.Point (dVariety k 4) ≃*
    Variety.Point (closedSubgroup k).carrierVariety :=
  MulEquiv.ofBijective (coordinateHom k) (coordinateHom_bijective k)

@[simp] theorem coordinateEquiv_apply (x : Variety.Point (dVariety k 4)) :
    coordinateEquiv k x = parameterPoint k (dPointEquiv 4 x) := rfl

/-- A single nonidentity parameter gives precisely the published simple coroot. -/
theorem parameter_single (i : Fin 4) (t : kˣ) :
    parameter k (Function.update (fun _ => 1) i t) = simpleCoroot k i t := by
  simp only [parameter, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  fin_cases i <;> norm_num [Function.update, corootWord_one, Fin.ext_iff] <;> rfl

/-- Restriction of the Spin cover to the closed diagonal preimage. -/
def ordinaryCover : AlgebraicGroup.Morphism (closedSubgroup k).carrierVariety
    (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).carrierVariety :=
  ((cliffordModel k).spinCover.comp (closedSubgroup k).inclusion).codRestrictClosedSubgroup
    (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4))
    (fun x => ((closedSubgroup k).pointEquiv x).property)

/-- The regular map forgetting Spin coordinates and retaining the ordinary
orthogonal diagonal coordinates. Its inverse is not asserted to be regular. -/
def ordinaryCoordinates : AlgebraicGroup.Morphism (closedSubgroup k).carrierVariety
    (dVariety k 4) :=
  (evenOrthogonalDiagonalTorusIso (k := k) 4 (le_refl 4)).inv.comp (ordinaryCover k)

theorem ordinaryCoordinates_parameter (t : Fin 4 → kˣ) :
    (ordinaryCoordinates k).onPoints (parameterPoint k t) =
      (dPointEquiv 4).symm (diagonal k t) := by
  let e := evenOrthogonalDiagonalTorusIso (k := k) 4 (le_refl 4)
  have h : (ordinaryCover k).onPoints (parameterPoint k t) =
      e.hom.onPoints ((dPointEquiv 4).symm (diagonal k t)) := by
    apply (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).inclusion_injective
    change (cliffordModel k).spinCover.onPoints
        ((closedSubgroup k).inclusion.onPoints (parameterPoint k t)) = _
    rw [inclusion_parameterPoint, cover_parameter]
    exact (evenOrthogonalDiagonalTorusIso_inclusion_hom 4 (le_refl 4) _).symm
  change e.inv.onPoints ((ordinaryCover k).onPoints (parameterPoint k t)) = _
  rw [h, e.hom_inv_id]

end Triality.SimplyConnected.Pinning.CorootTorus
