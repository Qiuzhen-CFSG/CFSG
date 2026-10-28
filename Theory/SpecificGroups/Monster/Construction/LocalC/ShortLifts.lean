module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortVectors
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticQuotient
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Core

/-!
# The signed module on short extraspecial elements

Given the Section 27 coordinate isometry, use the actual extraspecial image
of `Q1` in `N/K`. Two elements have the same lattice class exactly when they
differ by its central involution. Consequently the unsigned short orbits
are in bijection with the 98,280 minimal Leech classes. Anti-invariant real
functions give the source signed vectors, positive form and dimension.
Compatible automorphisms act orthogonally by transporting these vectors.

All assertions in this module are conditional on the explicit comparison
`e`; existence and source equivariance of that comparison are separate
obligations. In particular the auxiliary compatible-automorphism group is
not asserted to be the source spin tensor image `C`.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.2 and the construction of
`B_r` before Lemma 27.8, printed pp. 144–150. Lattice geometry and Parker
identities are the attributed ATLAS ports imported below.
-/

@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
open Atlas.Codes Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin TrialitySpin.SignedModules

/-- Input for the independent signed-lift construction. The final local group
must supply the source coordinate comparison, including its equivariance. -/
abbrev LatticeComparison := coordinateQuadraticForm.IsometryEquiv leechQuadraticForm

variable (e : LatticeComparison)

def latticeClass (q : Q1Image) : LeechModTwo := e (q1ImageCoordinates q).toAdd

theorem latticeClass_surjective : Function.Surjective (latticeClass e) := by
  intro a
  obtain ⟨q, hq⟩ := q1ImageCoordinates_surjective (Multiplicative.ofAdd (e.symm a))
  refine ⟨q, ?_⟩
  simp [latticeClass, hq]

@[simp] theorem latticeClass_one : latticeClass e 1 = 0 := by
  simp [latticeClass]

theorem latticeClass_mul (q r : Q1Image) :
    latticeClass e (q * r) = latticeClass e q + latticeClass e r := by
  unfold latticeClass
  rw [map_mul]
  exact map_add e _ _

theorem centerGenerator_mem : q1ImageCenterGenerator ∈ Subgroup.center Q1Image := by
  rw [Q1Image_center]
  exact Subgroup.mem_zpowers _

theorem image_center_iff (q : Q1Image) :
    q ∈ Subgroup.center Q1Image ↔ q = 1 ∨ q = q1ImageCenterGenerator := by
  classical
  rw [Q1Image_center, mem_zpowers_iff_mem_range_orderOf,
    orderOf_eq_prime q1ImageCenterGenerator_sq q1ImageCenterGenerator_ne_one]
  constructor
  · intro hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    have hn' : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
    · exact Finset.mem_image.mpr ⟨1, by simp, by simp⟩

@[simp] theorem latticeClass_centerGenerator : latticeClass e q1ImageCenterGenerator = 0 := by
  have h : q1ImageCoordinates q1ImageCenterGenerator = 1 := by
    exact (show q1ImageCenterGenerator ∈ q1ImageCoordinates.ker from
      q1ImageCoordinates_kernel.symm ▸ centerGenerator_mem)
  simp [latticeClass, h]

theorem latticeClass_eq_iff (q r : Q1Image) :
    latticeClass e q = latticeClass e r ↔ q = r ∨ q = r * q1ImageCenterGenerator := by
  constructor
  · intro h
    have hc : q1ImageCoordinates q = q1ImageCoordinates r := by
      exact e.injective h
    have hk : r⁻¹ * q ∈ Subgroup.center Q1Image := by
      rw [← q1ImageCoordinates_kernel, MonoidHom.mem_ker, map_mul, map_inv, hc,
        inv_mul_cancel]
    rcases (image_center_iff _).mp hk with h | h
    · exact Or.inl (inv_mul_eq_one.mp h).symm
    · exact Or.inr (by simpa using congrArg (fun x => r * x) h)
  · rintro (rfl | rfl)
    · rfl
    · rw [latticeClass_mul, latticeClass_centerGenerator, add_zero]

/-- Actual short elements of the extraspecial group, rather than lattice vectors. -/
def ShortLift := {q : Q1Image // latticeClass e q ∈ shellClasses 4}

instance : Finite (ShortLift e) := inferInstanceAs (Finite {q : Q1Image // latticeClass e q ∈ shellClasses 4})
instance : Fintype (ShortLift e) := Fintype.ofFinite _

def shortLiftClass (q : ShortLift e) : ShortClass := ⟨latticeClass e q.val, q.prop⟩

theorem shortLiftClass_surjective : Function.Surjective (shortLiftClass e) := by
  intro a
  obtain ⟨q, hq⟩ := latticeClass_surjective e a.val
  exact ⟨⟨q, hq ▸ a.prop⟩, Subtype.ext hq⟩

def shortLiftSigns : SignedSet (ShortLift e) where
  flip :=
    { toFun q := ⟨q.val * q1ImageCenterGenerator, by
        rw [latticeClass_mul, latticeClass_centerGenerator, add_zero]
        exact q.prop⟩
      invFun q := ⟨q.val * q1ImageCenterGenerator, by
        rw [latticeClass_mul, latticeClass_centerGenerator, add_zero]
        exact q.prop⟩
      left_inv q := by
        apply Subtype.ext
        change q.val * q1ImageCenterGenerator * q1ImageCenterGenerator = q.val
        rw [mul_assoc, ← pow_two, q1ImageCenterGenerator_sq, mul_one]
      right_inv q := by
        apply Subtype.ext
        change q.val * q1ImageCenterGenerator * q1ImageCenterGenerator = q.val
        rw [mul_assoc, ← pow_two, q1ImageCenterGenerator_sq, mul_one] }
  involutive q := by
    apply Subtype.ext
    change q.val * q1ImageCenterGenerator * q1ImageCenterGenerator = q.val
    rw [mul_assoc, ← pow_two, q1ImageCenterGenerator_sq, mul_one]
  fixedPointFree q h := q1ImageCenterGenerator_ne_one
    (mul_eq_left.mp (congrArg Subtype.val h))

theorem shortLiftClass_eq_iff (q r : ShortLift e) :
    shortLiftClass e q = shortLiftClass e r ↔ q = r ∨ q = (shortLiftSigns e).flip r := by
  rw [Subtype.ext_iff]
  change latticeClass e q.val = latticeClass e r.val ↔ _
  rw [latticeClass_eq_iff]
  exact or_congr Subtype.ext_iff.symm
    (show q.val = ((shortLiftSigns e).flip r).val ↔ q = (shortLiftSigns e).flip r from
      Subtype.ext_iff.symm)

/-- The unsigned orbits of the actual extraspecial lifts are the short
Leech classes; this proves the source dimension without selecting fake lifts. -/
def shortLiftOrbitEquiv : (shortLiftSigns e).toPairing.Orbit ≃ ShortClass :=
  Equiv.ofBijective
    (Quotient.lift (shortLiftClass e) (fun q r h => (shortLiftClass_eq_iff e q r).mpr h))
    ⟨by
      intro a b
      induction a using Quotient.inductionOn with
      | h q =>
        induction b using Quotient.inductionOn with
        | h r =>
          intro h
          exact Quotient.sound ((shortLiftClass_eq_iff e q r).mp h),
      by
        intro a
        obtain ⟨q, hq⟩ := shortLiftClass_surjective e a
        exact ⟨(shortLiftSigns e).toPairing.orbit q, hq⟩⟩

abbrev ShortSpace := (shortLiftSigns e).Space

def shortVector (r : ShortLift e) : ShortSpace e := (shortLiftSigns e).delta r

@[simp] theorem shortVector_sign (r : ShortLift e) :
    shortVector e ((shortLiftSigns e).flip r) = -shortVector e r :=
  (shortLiftSigns e).delta_flip r

def shortForm : LinearMap.BilinForm ℝ (ShortSpace e) := (shortLiftSigns e).form

theorem shortForm_pos (v : ShortSpace e) (hv : v ≠ 0) : 0 < shortForm e v v :=
  (shortLiftSigns e).form_pos v hv

theorem shortForm_symmetric (v w : ShortSpace e) : shortForm e v w = shortForm e w v :=
  (shortLiftSigns e).form_symmetric v w

theorem shortForm_vector_self (r : ShortLift e) :
    shortForm e (shortVector e r) (shortVector e r) = 1 := by
  exact ((shortLiftSigns e).form_delta r ((shortLiftSigns e).delta r)).trans
    ((shortLiftSigns e).delta_self r)

theorem shortSpace_finrank : Module.finrank ℝ (ShortSpace e) = 98280 := by
  rw [ShortSpace, SignedSet.finrank_eq, Nat.card_congr (shortLiftOrbitEquiv e), shortClass_card]

/-- A basis consisting of the prescribed signed vectors, one for each class. -/
def shortBasis : Module.Basis ShortClass ℝ (ShortSpace e) :=
  (shortLiftSigns e).basis.reindex (shortLiftOrbitEquiv e)

theorem shortBasis_eq_vector (a : ShortClass) :
    shortBasis e a = shortVector e ((shortLiftOrbitEquiv e).symm a).out := by
  simp only [shortBasis, Module.Basis.reindex_apply, SignedSet.basis_eq_delta, shortVector]

theorem shortBasis_orthonormal (a b : ShortClass) :
    shortForm e (shortBasis e a) (shortBasis e b) = if a = b then 1 else 0 := by
  simp only [shortBasis, Module.Basis.reindex_apply]
  change (shortLiftSigns e).form
    ((shortLiftSigns e).basis ((shortLiftOrbitEquiv e).symm a))
    ((shortLiftSigns e).basis ((shortLiftOrbitEquiv e).symm b)) = _
  simp only [SignedSet.basis_orthonormal, (shortLiftOrbitEquiv e).symm.injective.eq_iff]

theorem shortLift_card : Nat.card (ShortLift e) = 196560 := by
  have h := (shortLiftSigns e).twice_finrank
  change Module.finrank ℝ (ShortSpace e) * 2 = _ at h
  rw [shortSpace_finrank] at h
  exact h.symm

/-- Short extraspecial elements are involutions, as required in (28.4). -/
theorem shortLift_square (r : ShortLift e) : r.val ^ 2 = 1 := by
  have ht : leechClassType (latticeClass e r.val) = 2 :=
    (leechClassType_fibers _).2.1.mpr r.prop
  have hq : coordinateQuadratic (q1ImageCoordinates r.val).toAdd = 0 := by
    have he := e.map_app (q1ImageCoordinates r.val).toAdd
    change leechQuadratic (latticeClass e r.val) = _ at he
    rw [leechQuadratic_classType, ht] at he
    simpa using he.symm
  rw [Q1Image_square_coordinates, hq]
  rfl

/-- Every automorphism fixes the unique nonidentity central element. -/
theorem automorphism_fixes_centerGenerator (f : MulAut Q1Image) :
    f q1ImageCenterGenerator = q1ImageCenterGenerator := by
  have hc := (Subgroup.centerCongr f ⟨q1ImageCenterGenerator, centerGenerator_mem⟩).prop
  rcases (image_center_iff _).mp hc with h | h
  · exact False.elim (q1ImageCenterGenerator_ne_one (f.injective (h.trans (map_one f).symm)))
  · exact h

/-- Compatible automorphisms of the actual extraspecial group and lattice.
This auxiliary group acts on the short summand; the spin tensor image defining
`C` is a separate construction, and is not identified with this group. -/
def compatibleAutomorphisms : Subgroup (MulAut Q1Image × LeechIsometryGroup) where
  carrier p := ∀ q, latticeClass e (p.1 q) =
    leechModTwoRepresentation p.2 (latticeClass e q)
  one_mem' q := (leechModTwoMap_one _).symm
  mul_mem' := by
    intro p r hp hr q
    change latticeClass e (p.1 (r.1 q)) =
      leechModTwoMap (p.2 * r.2) (latticeClass e q)
    rw [hp, hr, leechModTwoMap_mul]
    rfl
  inv_mem' := by
    intro p hp q
    have h := hp (p.1.symm q)
    rw [p.1.apply_symm_apply] at h
    apply (leechModTwoRepresentation p.2).injective
    change leechModTwoMap p.2 (latticeClass e (p.1.symm q)) =
      leechModTwoMap p.2 (leechModTwoMap p.2⁻¹ (latticeClass e q))
    rw [← leechModTwoMap_mul, mul_inv_cancel, leechModTwoMap_one]
    exact h.symm

def shortLiftPermutation (p : compatibleAutomorphisms e) : Equiv.Perm (ShortLift e) where
  toFun q := ⟨p.val.1 q.val, by
    rw [p.prop]
    exact shellClasses_transport p.val.2 4 _ q.prop⟩
  invFun q := ⟨p.val.1.symm q.val, by
    have h := (p⁻¹).prop q.val
    change latticeClass e (p.val.1.symm q.val) = _ at h
    rw [h]
    exact shellClasses_transport p.val.2⁻¹ 4 _ q.prop⟩
  left_inv q := Subtype.ext (p.val.1.symm_apply_apply q.val)
  right_inv q := Subtype.ext (p.val.1.apply_symm_apply q.val)

def shortLiftRepresentation : compatibleAutomorphisms e →* Equiv.Perm (ShortLift e) where
  toFun := shortLiftPermutation e
  map_one' := by ext q; rfl
  map_mul' p r := by ext q; rfl

theorem shortLiftRepresentation_sign (p : compatibleAutomorphisms e) (q : ShortLift e) :
    shortLiftRepresentation e p ((shortLiftSigns e).flip q) =
      (shortLiftSigns e).flip (shortLiftRepresentation e p q) := by
  apply Subtype.ext
  change p.val.1 (q.val * q1ImageCenterGenerator) = p.val.1 q.val * q1ImageCenterGenerator
  rw [map_mul, automorphism_fixes_centerGenerator]

/-- The source conjugation action on the signed vectors, whenever the
extraspecial and lattice actions induce the same binary action. -/
def shortAction : Representation ℝ (compatibleAutomorphisms e) (ShortSpace e) :=
  (shortLiftSigns e).representation (shortLiftRepresentation e) (shortLiftRepresentation_sign e)

@[simp] theorem shortAction_vector (p : compatibleAutomorphisms e) (q : ShortLift e) :
    shortAction e p (shortVector e q) = shortVector e (shortLiftRepresentation e p q) :=
  (shortLiftSigns e).representation_delta _ _ p q

theorem shortAction_form (p : compatibleAutomorphisms e) (v w : ShortSpace e) :
    shortForm e (shortAction e p v) (shortAction e p w) = shortForm e v w :=
  (shortLiftSigns e).transport_isometry (shortLiftSigns e)
    (shortLiftRepresentation e p) (shortLiftRepresentation_sign e p) v w

theorem shortAction_kernel_iff (p : compatibleAutomorphisms e) :
    shortAction e p = 1 ↔ ∀ q : ShortLift e, p.val.1 q.val = q.val := by
  rw [shortAction, SignedSet.representation_kernel_iff]
  constructor
  · intro h q
    exact congrArg Subtype.val (Equiv.congr_fun h q)
  · intro h
    ext q
    exact Subtype.ext (h q)

theorem shortLiftClass_action (p : compatibleAutomorphisms e) (q : ShortLift e) :
    shortLiftClass e (shortLiftRepresentation e p q) =
      shortClassRepresentation p.val.2 (shortLiftClass e q) :=
  Subtype.ext (p.prop q.val)

/-- The tensor associated to an actual short extraspecial lift. -/
def shortLiftTensor (q : ShortLift e) : SymmetricPart := shortTensor (shortLiftClass e q)

@[simp] theorem shortLiftTensor_sign (q : ShortLift e) :
    shortLiftTensor e ((shortLiftSigns e).flip q) = shortLiftTensor e q := by
  apply congrArg shortTensor
  apply Subtype.ext
  exact (latticeClass_mul e _ _).trans (by rw [latticeClass_centerGenerator, add_zero]; rfl)

/-- The sign-independent natural factor of the mixed product (28.6). -/
def shortLiftCorrection (q : ShortLift e) (a : NaturalSpace) : NaturalSpace :=
  shortCorrection (shortLiftClass e q) a

@[simp] theorem shortLiftCorrection_sign (q : ShortLift e) (a : NaturalSpace) :
    shortLiftCorrection e ((shortLiftSigns e).flip q) a = shortLiftCorrection e q a := by
  have h : shortLiftClass e ((shortLiftSigns e).flip q) = shortLiftClass e q := by
    apply Subtype.ext
    exact (latticeClass_mul e _ _).trans (by rw [latticeClass_centerGenerator, add_zero]; rfl)
  exact congrArg (fun r => shortCorrection r a) h

end Sporadic.Monster.Construction.LocalC
