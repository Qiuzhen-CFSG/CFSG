module

public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinary
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The isotropic projective action of U₆(2)

The identity Hermitian form over GF(4) has norm `∑ i, (v i)² * v i`.
Its zero locus is invariant under nonzero scaling and under the specified
special unitary matrix group. Restricting the existing PGL action therefore
constructs the action of the actual projective image on isotropic lines.
We also adjoin a point fixed by the whole group for comparison with the
fixed-point action of the ATLAS Fi22 involution centralizer.

The matrix equation `Aᴴ A = 1` proves norm preservation; projectivization
handles the scalar quotient. Faithfulness and comparison with the ATLAS
permutations are separate results, not assumptions in these definitions.

Application: the Fi22 centralizer entry, GLS3 Table 5.3t
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`). The table specifies the unitary
quotient; identifying its action with this isotropic-line construction
requires an additional comparison proof.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Theory.SpecificGroups.U6Two

/-- Every nonzero scalar of GF(4) has Hermitian norm one. -/
theorem conjugation_mul_self_of_ne_zero (c : Field) (hc : c ≠ 0) : conjugation c * c = 1 := by
  let := Fintype.ofFinite Field
  have hcard : Fintype.card Field = 4 := by
    simpa only [Nat.card_eq_fintype_card] using field_card
  simpa [conjugation_apply, ← pow_succ, hcard] using
    FiniteField.pow_card_sub_one_eq_one c hc


/-- The six-dimensional vector space of the fixed matrix model. -/
abbrev Vector := Fin 6 → Field
/-- One-dimensional subspaces, represented by nonzero vectors modulo scaling. -/
abbrev ProjectivePoint := ℙ Field Vector

/-- The norm of the identity Hermitian form with conjugation `x ↦ x²`. -/
noncomputable def hermitianNorm (v : Vector) : Field :=
  (fun i => conjugation (v i)) ⬝ᵥ v

theorem hermitianNorm_smul (c : Field) (v : Vector) :
    hermitianNorm (c • v) = (conjugation c * c) * hermitianNorm v := by
  simp only [hermitianNorm, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hermitianNorm_smul_eq_zero_iff (c : Field) (hc : c ≠ 0) (v : Vector) :
    hermitianNorm (c • v) = 0 ↔ hermitianNorm v = 0 := by
  rw [hermitianNorm_smul]
  exact mul_eq_zero_iff_left (mul_ne_zero ((map_ne_zero conjugation).mpr hc) hc)

/-- Isotropy of a projective point; `isotropic_mk_iff` removes the chosen representative. -/
def Isotropic (p : ProjectivePoint) : Prop := hermitianNorm p.rep = 0

theorem isotropic_mk_iff (v : Vector) (hv : v ≠ 0) :
    Isotropic (Projectivization.mk Field v hv) ↔ hermitianNorm v = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep Field v hv
  unfold Isotropic
  rw [← hc]
  exact hermitianNorm_smul_eq_zero_iff c.val c.ne_zero v

/-- The actual isotropic one-dimensional subspaces of GF(4)⁶. -/
abbrev IsotropicPoint := {p : ProjectivePoint // Isotropic p}

/-- The isotropic line of a specified nonzero isotropic vector. -/
noncomputable def mkIsotropicPoint (v : Vector) (hv : v ≠ 0)
    (hi : hermitianNorm v = 0) : IsotropicPoint :=
  ⟨Projectivization.mk Field v hv, (isotropic_mk_iff v hv).mpr hi⟩

private theorem conjugation_mulVec (A : Matrix (Fin 6) (Fin 6) Field) (v : Vector) :
    (fun i => conjugation ((A *ᵥ v) i)) =
      (fun i => conjugation (v i)) ᵥ* form.conjTranspose A := by
  funext i
  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul,
    BenderSuzuki.MatrixGroups.HermitianForm.conjTranspose]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem hermitianNorm_mulVec (A : form.specialSubgroup) (v : Vector) :
    hermitianNorm ((A.val : Matrix (Fin 6) (Fin 6) Field) *ᵥ v) =
      hermitianNorm v := by
  have hA := (form.mem_specialSubgroup_iff A.val).mp A.property
  have hAA : form.conjTranspose (A.val : Matrix (Fin 6) (Fin 6) Field) *
      (A.val : Matrix (Fin 6) (Fin 6) Field) = 1 := by
    simpa only [show form.form = 1 from rfl, mul_one] using hA.1
  unfold hermitianNorm
  rw [conjugation_mulVec, dotProduct_mulVec, vecMul_vecMul, hAA, vecMul_one]

theorem isotropic_smul_iff (g : Carrier) (p : ProjectivePoint) :
    Isotropic (g.val • p) ↔ Isotropic p := by
  obtain ⟨A, rfl⟩ := project_surjective g
  induction p using Projectivization.ind with
  | h v hv =>
    change Isotropic (Matrix.ProjGenLinGroup.mk A.val •
      Projectivization.mk Field v hv) ↔ _
    rw [Projectivization.PGL.mk_smul_mk, isotropic_mk_iff, isotropic_mk_iff]
    change hermitianNorm ((A.val : Matrix (Fin 6) (Fin 6) Field) *ᵥ v) = 0 ↔ _
    rw [hermitianNorm_mulVec]

/-- Restriction of the PGL action to the isotropic lines. -/
noncomputable def isotropicAction : Carrier →* Equiv.Perm IsotropicPoint where
  toFun g := (MulAction.toPerm g.val).subtypePerm (isotropic_smul_iff g)
  map_one' := by
    ext p
    exact one_smul (Matrix.ProjGenLinGroup (Fin 6) Field) p.val
  map_mul' g h := by
    ext p
    exact mul_smul g.val h.val p.val

theorem isotropicAction_apply (g : Carrier) (p : IsotropicPoint) :
    (isotropicAction g p).val = g.val • p.val := rfl

theorem isotropicAction_project_mk (A : form.specialSubgroup)
    (v : Vector) (hv : v ≠ 0) (hi : hermitianNorm v = 0) :
    isotropicAction (project A) (mkIsotropicPoint v hv hi) =
      mkIsotropicPoint (A.val • v) ((smul_ne_zero_iff_ne A.val).mpr hv)
        ((hermitianNorm_mulVec A v).trans hi) := by
  apply Subtype.ext
  exact Projectivization.PGL.mk_smul_mk A.val hv

/-- Isotropic lines together with a distinguished fixed point `none`. -/
abbrev PointWithSingleton := Option IsotropicPoint

/-- The projective unitary action with an additional fixed point. -/
noncomputable def isotropicActionWithSingleton : Carrier →* Equiv.Perm PointWithSingleton where
  toFun g := Equiv.optionCongr (isotropicAction g)
  map_one' := by
    ext p
    cases p <;> simp [Equiv.optionCongr, map_one]
  map_mul' g h := by
    ext p
    cases p <;> simp [Equiv.optionCongr, map_mul, Equiv.Perm.mul_apply]

theorem isotropicActionWithSingleton_none (g : Carrier) :
    isotropicActionWithSingleton g none = none := rfl

theorem isotropicActionWithSingleton_some (g : Carrier) (p : IsotropicPoint) :
    isotropicActionWithSingleton g (some p) = some (isotropicAction g p) := rfl

theorem isotropicActionWithSingleton_injective_iff :
    Function.Injective isotropicActionWithSingleton ↔ Function.Injective isotropicAction := by
  constructor
  · intro h g k hgk
    apply h
    change Equiv.optionCongr (isotropicAction g) = Equiv.optionCongr (isotropicAction k)
    rw [hgk]
  · intro h g k hgk
    apply h
    apply Equiv.ext
    intro p
    exact Option.some.inj (congrArg (fun e : Equiv.Perm PointWithSingleton => e (some p)) hgk)

end Theory.SpecificGroups.U6Two
