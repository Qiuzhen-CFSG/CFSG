/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianProjectiveModel.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveKernel
public import Theory.AtlasPort.Janko2.Conway.IcosianCentralizerFinite
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card

/-!
# IcosianProjectiveModel

The root-point action has exactly the two central signs as kernel. Its quotient is
the finite concrete projective model, with a faithful root-point action.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianProjectiveModel.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- The two central signs in the actual full Hermitian lattice group. -/
def icosianCentralSigns : Subgroup icosianHermitianGroup where
  carrier := {g | g=1 ∨ g=icosianCentralSign}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl|rfl) (rfl|rfl) <;> simp [icosianCentralSign_square]
  inv_mem' := by
    rintro a (rfl|rfl)
    · simp
    · right
      exact inv_eq_of_mul_eq_one_right icosianCentralSign_square

theorem icosianCentralSigns_mem (g : icosianHermitianGroup) :
    g∈icosianCentralSigns ↔ g=1 ∨ g=icosianCentralSign := Iff.rfl

theorem icosianCentralSign_ne_one : icosianCentralSign≠1 := by
  intro h
  have he := congrArg
    (fun g : icosianHermitianGroup => g.val (Pi.single 0 1 : IcosianRationalCoordinates) 0) h
  rw [icosianCentralSign_apply] at he
  change -(1 : IcosianQuaternion)=1 at he
  have h0 : (1 : GoldenRational)=0 :=
    CharZero.neg_eq_self_iff.mp (congrArg QuaternionAlgebra.re he)
  exact one_ne_zero h0

theorem icosianCentralSigns_card : Nat.card icosianCentralSigns=2 := by
  have he : (icosianCentralSigns : Set icosianHermitianGroup)={1,icosianCentralSign} := rfl
  rw [show Nat.card icosianCentralSigns=Nat.card ({1,icosianCentralSign} : Set icosianHermitianGroup)
    from Nat.card_congr (Equiv.setCongr he)]
  simp [Nat.card_eq_fintype_card,Ne.symm icosianCentralSign_ne_one]

theorem icosianCentralSign_fixes_rootPoints (p : IcosianRootPoint) :
    icosianCentralSign • p=p := by
  obtain ⟨r,hr⟩ := icosianRootToPoint_surjective p
  subst p
  apply Subtype.ext
  change icosianCentralSign • icosianRootPoint r=icosianRootPoint r
  rw [icosianRootPoint,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op (-1 : IcosianQuaternion),?_⟩
  change MulOpposite.op (-1 : IcosianQuaternion) • icosianCoordinateEmbedding r.val =
    icosianCentralSign.val (icosianCoordinateEmbedding r.val)
  rw [icosianCentralSign_apply]
  funext i
  simp

/-- Exact projective kernel, proved without order or simplicity of J2. -/
theorem icosian_rootPoint_kernel :
    (MulAction.toPermHom icosianHermitianGroup IcosianRootPoint).ker=icosianCentralSigns := by
  ext g
  constructor
  · intro hg
    apply icosian_fix_rootPoints_eq_sign g
    intro p
    exact DFunLike.congr_fun hg p
  · intro hg
    apply Equiv.ext
    intro p
    change g • p=p
    rcases hg with rfl|rfl
    · exact one_smul _ _
    · exact icosianCentralSign_fixes_rootPoints p

instance icosianCentralSigns_normal : icosianCentralSigns.Normal := by
  rw [← icosian_rootPoint_kernel]
  infer_instance

/-- The intended projective quotient of the actual full linear stabilizer. -/
abbrev IcosianProjectiveModel := icosianHermitianGroup ⧸ icosianCentralSigns

def icosianProjectiveProjection : icosianHermitianGroup →* IcosianProjectiveModel :=
  QuotientGroup.mk' icosianCentralSigns

def icosianProjectivePointHom : IcosianProjectiveModel →* Equiv.Perm IcosianRootPoint :=
  QuotientGroup.lift _ (MulAction.toPermHom icosianHermitianGroup IcosianRootPoint)
    icosian_rootPoint_kernel.ge

theorem icosianProjectivePointHom_injective : Function.Injective icosianProjectivePointHom :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr icosian_rootPoint_kernel.symm

instance icosianProjectivePointAction : MulAction IcosianProjectiveModel IcosianRootPoint :=
  MulAction.compHom _ icosianProjectivePointHom

theorem icosianProjectivePointAction_mk (g : icosianHermitianGroup) (p : IcosianRootPoint) :
    icosianProjectiveProjection g • p=g • p := rfl

instance icosianProjectivePoint_faithful : FaithfulSMul IcosianProjectiveModel IcosianRootPoint where
  eq_of_smul_eq_smul h := icosianProjectivePointHom_injective (Equiv.ext h)

instance icosianProjective_finite : Finite IcosianProjectiveModel := inferInstance

theorem icosianProjective_card_mul_two :
    Nat.card IcosianProjectiveModel*2=Nat.card icosianHermitianGroup := by
  simpa only [icosianCentralSigns_card] using
    (Subgroup.card_eq_card_quotient_mul_card_subgroup icosianCentralSigns).symm

end Atlas.Conway
