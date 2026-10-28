module

public import Theory.Representation.HexacodeAction
public import Theory.Representation.HexacodeAction.Cover
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Four-element field coordinates for the hexacode action

The first three code coordinates identify the binary hexacode with `F₄³`.
Orienting a letter by its coordinate parity makes the coordinate-kernel
generator `hexZ` act as multiplication by the root of `x² + x + 1`.
This transports an actual four-element field module structure to the code,
compatible with its existing binary structure. Even automorphisms are
field-linear and have determinant one, by perfectness of the even group.
The explicit odd involution `hexLift 4` acts as coordinatewise squaring;
all odd automorphisms are semilinear for this nontrivial field automorphism.

A binary subspace stable under `hexZ` is consequently an actual `F₄`
submodule, and the tower formula identifies its two dimensions. These
results establish the concrete field action used as the model in K.1.3.
They do not classify other representations or recognize a source plane.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464), and A.3.5, printed p.43. The underlying code,
coordinate lifts and their relations are from the licensed ATLAS ports
under `Theory.AtlasPort.OtherSporadic.Codes`; the quadratic field and its
Frobenius are reused from `Theory.Representation.SL2FourNaturalOrbits.Model`.
-/

@[expose] public section

open Atlas.Codes
namespace Representation.Hexacode
/-- The computable quadratic field with four elements. -/
abbrev F := SL2FourNatural.F

/-- Identify a binary letter with its quadratic-field coefficients. -/
def letterField : K ≃ₗ[Bit] F where
  toFun u := ⟨u.1, u.2⟩
  invFun u := (u.re, u.im)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Orient the local scalar consistently at both coordinate parities. -/
def orientedLetter (i : HexIndex) : K ≃ₗ[Bit] F :=
  (if i.2 = 0 then LinearEquiv.refl Bit K else localU).trans letterField

/-- The first three oriented coordinates give the actual binary equivalence. -/
noncomputable def binaryCoordinates : hexacode ≃ₗ[Bit] (Fin 3 → F) :=
  (LinearEquiv.ofBijective (hexProjection firstThree) (hexProjection_bijective firstThree)).trans
    (LinearEquiv.piCongrRight fun i => orientedLetter (firstThree i))

/-- The field action transported along the binary coordinates. -/
noncomputable instance fieldModule : Module F hexacode :=
  binaryCoordinates.toAddEquiv.module F

/-- The field action extends the original binary scalar action. -/
noncomputable instance fieldTower : IsScalarTower Bit F hexacode :=
  binaryCoordinates.isScalarTower (A := F)

/-- The same coordinate map, now linear over the four-element field. -/
noncomputable def fieldCoordinates : hexacode ≃ₗ[F] (Fin 3 → F) :=
  binaryCoordinates.toAddEquiv.linearEquiv F

/-- The code is finite dimensional over the four-element field. -/
instance fieldFinite : Module.Finite F hexacode := Module.Finite.equiv fieldCoordinates.symm

/-- The field and binary coordinate maps are the same function. -/
theorem fieldCoordinates_apply (w : hexacode) : fieldCoordinates w = binaryCoordinates w := rfl

/-- The primitive cubic scalar in the concrete quadratic field. -/
def omega : F := QuadraticAlgebra.omega

/-- The coordinate-kernel generator is multiplication by the cubic scalar. -/
theorem scalar_coordinates (w : hexacode) :
    binaryCoordinates (action hexZ w) = omega • binaryCoordinates w := by
  funext i
  change orientedLetter (firstThree i)
      ((if (firstThree i).2 = 0 then localKappa else localKappa⁻¹) (w.val (firstThree i))) =
    omega * orientedLetter (firstThree i) (w.val (firstThree i))
  have h : ∀ (i : HexIndex) (u : K),
      orientedLetter i ((if i.2 = 0 then localKappa else localKappa⁻¹) u) =
        omega * orientedLetter i u := by decide
  exact h _ _

/-- The concrete central generator acts by the field scalar on the code. -/
theorem scalar_eq_omega_smul (w : hexacode) : action hexZ w = omega • w := by
  apply binaryCoordinates.injective
  rw [scalar_coordinates]
  exact (fieldCoordinates.map_smul omega w).symm

/-- Field scalar multiplication is the binary combination of identity and `hexZ`. -/
theorem field_smul_formula (r : F) (w : hexacode) :
    r • w = r.re • w + r.im • action hexZ w := by
  apply binaryCoordinates.injective
  rw [map_add, binaryCoordinates.map_smul, binaryCoordinates.map_smul, scalar_coordinates]
  rw [show binaryCoordinates (r • w) = r • binaryCoordinates w from
    fieldCoordinates.map_smul r w]
  funext i
  change r * binaryCoordinates w i =
    r.re • binaryCoordinates w i + r.im • (omega * binaryCoordinates w i)
  have h : ∀ r u : F, r * u = r.re • u + r.im • (omega * u) := by decide
  exact h _ _

/-- The hexacode has dimension three over the four-element field. -/
theorem field_finrank : Module.finrank F hexacode = 3 := by
  rw [fieldCoordinates.finrank_eq]
  simp

/-- Even automorphisms commute with the cubic scalar action. -/
theorem action_commutes_scalar (g : HexAutomorphisms) (hg : hexSign g = 1)
    (w : hexacode) : action g (action hexZ w) = action hexZ (action g w) := by
  have hgz : g * hexZ = hexZ * g := mul_inv_eq_iff_eq_mul.mp (hex_conjugation_even g hg)
  change (hexAction g * hexAction hexZ) w = (hexAction hexZ * hexAction g) w
  rw [← map_mul, ← map_mul, hgz]

/-- The even action is linear over the four-element field. -/
theorem action_even_smul (g : HexAutomorphisms) (hg : hexSign g = 1)
    (r : F) (w : hexacode) : action g (r • w) = r • action g w := by
  rw [field_smul_formula, map_add, map_smul, map_smul, action_commutes_scalar g hg,
    ← field_smul_formula]

/-- An explicit odd coordinate lift fixing the first three coordinate positions. -/
def fieldInvolution : HexAutomorphisms := hexLift 4

/-- The chosen odd element is an involution. -/
theorem fieldInvolution_sq : fieldInvolution * fieldInvolution = 1 := hexLift_sq 4

/-- The chosen field involution lies outside the even cover. -/
theorem fieldInvolution_odd : hexSign fieldInvolution = -1 := hexSign_lift 4

/-- In the chosen basis the odd involution is coordinatewise Frobenius. -/
theorem fieldInvolution_coordinates (w : hexacode) (i : Fin 3) :
    binaryCoordinates (action fieldInvolution w) i =
      SL2FourNatural.fieldFrobenius (binaryCoordinates w i) := by
  change orientedLetter (firstThree i)
      (Monomial.act (hexLiftRaw 4) w.val (firstThree i)) = _
  have hp : ∀ i : Fin 3, (hexLiftRaw 4).perm.symm (firstThree i) = firstThree i := by decide
  change orientedLetter (firstThree i)
      ((hexLiftRaw 4).localMap (firstThree i)
        (w.val ((hexLiftRaw 4).perm.symm (firstThree i)))) = _
  rw [hp]
  have h : ∀ (i : Fin 3) (u : K),
      orientedLetter (firstThree i) ((hexLiftRaw 4).localMap (firstThree i) u) =
        SL2FourNatural.fieldFrobenius (orientedLetter (firstThree i) u) := by decide
  exact h i _

/-- The explicit involution is semilinear for the nontrivial field automorphism. -/
theorem fieldInvolution_smul (r : F) (w : hexacode) :
    action fieldInvolution (r • w) = SL2FourNatural.fieldFrobenius r •
      action fieldInvolution w := by
  apply fieldCoordinates.injective
  rw [fieldCoordinates.map_smul]
  funext i
  rw [fieldCoordinates_apply, fieldInvolution_coordinates]
  change SL2FourNatural.fieldFrobenius (fieldCoordinates (r • w) i) = _
  rw [fieldCoordinates.map_smul]
  change SL2FourNatural.fieldFrobenius (r * binaryCoordinates w i) = _
  rw [map_mul, ← fieldInvolution_coordinates]
  rfl

/-- Every odd automorphism is semilinear for Frobenius. -/
theorem action_odd_smul (g : HexAutomorphisms) (hg : hexSign g = -1)
    (r : F) (w : hexacode) :
    action g (r • w) = SL2FourNatural.fieldFrobenius r • action g w := by
  have he : hexSign (g * fieldInvolution) = 1 := by
    rw [map_mul, hg, fieldInvolution_odd, neg_mul_neg, one_mul]
  have hm : g = (g * fieldInvolution) * fieldInvolution := by
    rw [mul_assoc, fieldInvolution_sq, mul_one]
  conv_lhs => rw [hm, map_mul]
  change action (g * fieldInvolution) (action fieldInvolution (r • w)) = _
  rw [fieldInvolution_smul, action_even_smul _ he]
  congr 1
  change (action (g * fieldInvolution) * action fieldInvolution) w = _
  rw [← map_mul, ← hm]

/-- The actual field-linear action of the even hexacode group. -/
noncomputable def evenFieldAction : HexEvenAutomorphisms →* (hexacode ≃ₗ[F] hexacode) where
  toFun g :=
    { hexAction g.val with
      map_smul' r w := action_even_smul g.val g.property r w }
  map_one' := by
    apply LinearEquiv.ext
    intro w
    exact LinearEquiv.congr_fun hexAction.map_one w
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    exact LinearEquiv.congr_fun (hexAction.map_mul g.val h.val) w

/-- The field-linear action remains faithful. -/
theorem evenFieldAction_injective : Function.Injective evenFieldAction := by
  intro g h he
  apply Subtype.ext
  apply action_injective
  apply LinearMap.ext
  intro w
  exact LinearEquiv.congr_fun he w

/-- Perfectness puts the even action in the special linear group. -/
theorem evenFieldAction_det (g : HexEvenAutomorphisms) :
    LinearEquiv.det (evenFieldAction g) = 1 := by
  let f : HexEvenAutomorphisms →* Fˣ := LinearEquiv.det.comp evenFieldAction
  let _ : Group.IsPerfect HexEvenAutomorphisms := even_isPerfect
  let _ : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (⟨f g, ⟨g, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

/-- The scalar field has exactly four elements. -/
theorem field_card : Fintype.card F = 4 := SL2FourNatural.card_field

/-- The field automorphism in the odd action is nontrivial. -/
theorem fieldFrobenius_ne_id : SL2FourNatural.fieldFrobenius ≠ RingEquiv.refl F := by
  intro h
  have h' := RingEquiv.congr_fun h omega
  exact (by decide : SL2FourNatural.fieldFrobenius omega ≠ omega) h'

/-- The field-linear even action agrees with the original binary action. -/
theorem evenFieldAction_apply (g : HexEvenAutomorphisms) (w : hexacode) :
    evenFieldAction g w = action g.val w := rfl

/-- A binary subspace stable under the cubic scalar is a field submodule. -/
noncomputable def scalarSubmodule (P : Submodule Bit hexacode)
    (hP : hexZ ∈ BinaryOffender.subspaceStabilizer action P) : Submodule F hexacode where
  carrier := P
  zero_mem' := P.zero_mem
  add_mem' := P.add_mem
  smul_mem' r w hw := by
    rw [field_smul_formula]
    exact P.add_mem (P.smul_mem _ hw) (P.smul_mem _ ((hP w).mpr hw))

/-- The field submodule has the same underlying binary subspace. -/
noncomputable def scalarSubmoduleBinaryEquiv (P : Submodule Bit hexacode)
    (hP : hexZ ∈ BinaryOffender.subspaceStabilizer action P) :
    P ≃ₗ[Bit] scalarSubmodule P hP where
  toFun w := ⟨w.val, w.property⟩
  invFun w := ⟨w.val, w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Binary dimension is twice the field dimension on a scalar-stable subspace. -/
theorem scalarSubmodule_finrank (P : Submodule Bit hexacode)
    (hP : hexZ ∈ BinaryOffender.subspaceStabilizer action P) :
    2 * Module.finrank F (scalarSubmodule P hP) = Module.finrank Bit P := by
  rw [(scalarSubmoduleBinaryEquiv P hP).finrank_eq]
  let _ : Module.Free F (scalarSubmodule P hP) :=
    Module.Free.of_divisionRing F (scalarSubmodule P hP)
  have h := Module.finrank_mul_finrank Bit F (scalarSubmodule P hP)
  have hd : Module.finrank Bit F = 2 := QuadraticAlgebra.finrank_eq_two _ _
  rwa [hd] at h

end Representation.Hexacode
