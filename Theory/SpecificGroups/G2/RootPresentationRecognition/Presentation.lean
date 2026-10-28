module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.ModelRelations
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The explicit G₂ Borel–Weyl presentation

This is the ordinary presented group on six positive-root families, two torus
parameters and the long and short reflections. Its relators are exactly the
additive, positive collection, torus, Weyl and rank-one equations recorded in
`BorelWeylData.Relations`. Evaluation is constructed from those equations;
faithfulness is a separate theorem, not an input to this construction.

Source: the finite split comparison in DGS, Groups and Graphs, Theorem D,
p.224. The A–F root convention follows the licensed ATLAS octonion model.
-/

@[expose] public noncomputable section
namespace Atlas.G2.RootPresentationRecognition.Presentation
variable {F : Type*} [Field F]

inductive Generator (F : Type*) [Field F]
  | root : Fin 6 → F → Generator F
  | torus : Fˣ × Fˣ → Generator F
  | r : Generator F
  | s : Generator F

def x (i : Fin 6) (a : F) : FreeGroup (Generator F) := FreeGroup.of (.root i a)
def h (p : Fˣ × Fˣ) : FreeGroup (Generator F) := FreeGroup.of (.torus p)
def r : FreeGroup (Generator F) := FreeGroup.of .r
def s : FreeGroup (Generator F) := FreeGroup.of .s

inductive Relator : FreeGroup (Generator F) → Prop
  | zero (i : Fin 6) : Relator ((x i (0:F)) * (1)⁻¹)
  | add (i : Fin 6) (a b : F) : Relator ((x i (a+b)) * (x i a * x i b)⁻¹)
  | ba (a b : F) : Relator ((x 1 a * x 0 b) * (x 0 b * x 1 a)⁻¹)
  | ca (a b : F) : Relator ((x 2 a * x 0 b) * (x 0 b * x 2 a)⁻¹)
  | cb (a b : F) : Relator ((x 2 a * x 1 b) * (x 1 b * x 2 a)⁻¹)
  | da (a b : F) : Relator ((x 3 a * x 0 b) * (x 0 b * x 3 a)⁻¹)
  | db (a b : F) : Relator ((x 3 a * x 1 b) * (x 1 b * x 3 a)⁻¹)
  | ea (a b : F) : Relator ((x 4 a * x 0 b) * (x 0 b * x 4 a)⁻¹)
  | ec (a b : F) : Relator ((x 4 a * x 2 b) * (x 2 b * x 4 a)⁻¹)
  | ed (a b : F) : Relator ((x 4 a * x 3 b) * (x 3 b * x 4 a)⁻¹)
  | fa (a b : F) : Relator ((x 5 a * x 0 b) * (x 0 b * x 5 a)⁻¹)
  | fb (a b : F) : Relator ((x 5 a * x 1 b) * (x 1 b * x 5 a)⁻¹)
  | dc (a b : F) : Relator ((x 3 a * x 2 b) * (x 0 (b*a) * x 2 b * x 3 a)⁻¹)
  | eb (a b : F) : Relator ((x 4 a * x 1 b) * (x 0 (b*a) * x 1 b * x 4 a)⁻¹)
  | fc (a b : F) : Relator ((x 5 a * x 2 b) * (x 1 (b*a) * x 2 b * x 5 a)⁻¹)
  | fd (a b : F) : Relator ((x 5 a * x 3 b) * (x 0 (b^2*a) * x 1 (b*a^2) * x 3 b * x 5 a)⁻¹)
  | fe (a b : F) : Relator ((x 5 a * x 4 b) * (x 0 (b^2*a^3) * x 1 (b*a^3) * x 2 (b*a^2) * x 3 (b*a) * x 4 b * x 5 a)⁻¹)
  | torus_one  : Relator ((h (1 : Fˣ × Fˣ)) * (1)⁻¹)
  | torus_mul (p q : Fˣ × Fˣ) : Relator ((h (p*q)) * (h p * h q)⁻¹)
  | torus_root (l m : Fˣ) (i : Fin 6) (a : F) : Relator ((h (l,m) * x i a * (h (l,m))⁻¹) * (x i (BorelWeylData.weight l m i * a))⁻¹)
  | r_sq  : Relator ((r^2) * (1)⁻¹)
  | s_sq  : Relator ((s^2) * (1)⁻¹)
  | braid  : Relator (((r*s)^6) * (1)⁻¹)
  | r_torus (l m : Fˣ) : Relator ((r * h (l,m) * r⁻¹) * (h (l,l/m))⁻¹)
  | s_torus (l m : Fˣ) : Relator ((s * h (l,m) * s⁻¹) * (h (m,l))⁻¹)
  | rA (a : F) : Relator ((r * x 0 a * r⁻¹) * (x 1 a)⁻¹)
  | rB (a : F) : Relator ((r * x 1 a * r⁻¹) * (x 0 a)⁻¹)
  | rC (a : F) : Relator ((r * x 2 a * r⁻¹) * (x 2 a)⁻¹)
  | rD (a : F) : Relator ((r * x 3 a * r⁻¹) * (x 5 a)⁻¹)
  | rF (a : F) : Relator ((r * x 5 a * r⁻¹) * (x 3 a)⁻¹)
  | sA (a : F) : Relator ((s * x 0 a * s⁻¹) * (x 0 a)⁻¹)
  | sB (a : F) : Relator ((s * x 1 a * s⁻¹) * (x 4 a)⁻¹)
  | sC (a : F) : Relator ((s * x 2 a * s⁻¹) * (x 3 a)⁻¹)
  | sD (a : F) : Relator ((s * x 3 a * s⁻¹) * (x 2 a)⁻¹)
  | sE (a : F) : Relator ((s * x 4 a * s⁻¹) * (x 1 a)⁻¹)
  | long_word (a : Fˣ) : Relator ((x 4 (a:F) * (r * x 4 (↑a⁻¹:F) * r⁻¹) * x 4 (a:F)) * (h (1,a) * r)⁻¹)
  | short_word (a : Fˣ) : Relator ((x 5 (a:F) * (s * x 5 (↑a⁻¹:F) * s⁻¹) * x 5 (a:F)) * (h (a,a⁻¹) * s)⁻¹)

def relators : Set (FreeGroup (Generator F)) := {w | Relator w}
abbrev Group (F : Type*) [Field F] := PresentedGroup (relators (F := F))

def data : BorelWeylData F (Group F) where
  root i := {
    toFun := fun a => PresentedGroup.of (.root i a.toAdd)
    map_one' := by
      exact PresentedGroup.one_of_mem (show x i (0:F) ∈ relators from by
        change Relator (x i (0:F))
        simpa only [inv_one, mul_one] using Relator.zero (F := F) i)
    map_mul' := fun a b => PresentedGroup.mk_eq_mk_of_mul_inv_mem (.add i a.toAdd b.toAdd) }
  torus := {
    toFun := fun p => PresentedGroup.of (.torus p)
    map_one' := by
      exact PresentedGroup.one_of_mem (show h (1 : Fˣ × Fˣ) ∈ relators from by
        change Relator (h (1 : Fˣ × Fˣ))
        simpa only [inv_one, mul_one] using Relator.torus_one (F := F))
    map_mul' := fun p q => PresentedGroup.mk_eq_mk_of_mul_inv_mem (.torus_mul p q) }
  r := PresentedGroup.of .r
  s := PresentedGroup.of .s

/-- The equations are consequences of the defining relators. -/
theorem relations : (data (F := F)).Relations := by
  refine { toCharTwoRelations := { toCommutingRelations := ?_, dc := ?_, eb := ?_, fc := ?_, fd := ?_, fe := ?_ }, torus_root := ?_, r_sq := ?_, s_sq := ?_, braid := ?_, r_torus := ?_, s_torus := ?_, rA := ?_, rB := ?_, rC := ?_, rD := ?_, rF := ?_, sA := ?_, sB := ?_, sC := ?_, sD := ?_, sE := ?_, long_word := ?_, short_word := ?_ }
  · constructor
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ba a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ca a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.cb a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.da a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.db a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ea a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ec a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ed a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fa a b)
    · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fb a b)
  · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.dc a b)
  · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.eb a b)
  · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fc a b)
  · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fd a b)
  · intro a b; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fe a b)
  · intro l m i a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.torus_root l m i a)
  · exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.r_sq)
  · exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.s_sq)
  · exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.braid)
  · intro l m; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.r_torus l m)
  · intro l m; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.s_torus l m)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.rA a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.rB a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.rC a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.rD a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.rF a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.sA a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.sB a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.sC a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.sD a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.sE a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.long_word a)
  · intro a; exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.short_word a)

variable {G : Type*} [_root_.Group G]

def assignment (d : BorelWeylData F G) : Generator F → G
  | .root i a => d.x i a
  | .torus p => d.torus p
  | .r => d.r
  | .s => d.s

private theorem lift_relator (d : BorelWeylData F G) (R : d.Relations)
    (w : FreeGroup (Generator F)) (hw : Relator w) :
    FreeGroup.lift (assignment d) w = 1 := by
  cases hw with
  | zero i =>
      simp only [x, map_mul, map_inv, map_one, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (by simp)
  | add i a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (by simp [PositiveRoots.x_add])
  | ba a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.ba a b)
  | ca a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.ca a b)
  | cb a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.cb a b)
  | da a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.da a b)
  | db a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.db a b)
  | ea a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.ea a b)
  | ec a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.ec a b)
  | ed a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.ed a b)
  | fa a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.fa a b)
  | fb a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.fb a b)
  | dc a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.dc a b)
  | eb a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.eb a b)
  | fc a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.fc a b)
  | fd a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.fd a b)
  | fe a b =>
      simp only [x, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.fe a b)
  | torus_one  =>
      simp only [h, map_mul, map_inv, map_one, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (rfl)
  | torus_mul p q =>
      simp only [h, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (rfl)
  | torus_root l m i a =>
      simp only [x, h, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.torus_root l m i a)
  | r_sq  =>
      simp only [r, map_mul, map_inv, map_pow, map_one, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.r_sq)
  | s_sq  =>
      simp only [s, map_mul, map_inv, map_pow, map_one, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.s_sq)
  | braid  =>
      simp only [r, s, map_mul, map_inv, map_pow, map_one, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.braid)
  | r_torus l m =>
      simp only [h, r, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.r_torus l m)
  | s_torus l m =>
      simp only [h, s, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.s_torus l m)
  | rA a =>
      simp only [x, r, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.rA a)
  | rB a =>
      simp only [x, r, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.rB a)
  | rC a =>
      simp only [x, r, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.rC a)
  | rD a =>
      simp only [x, r, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.rD a)
  | rF a =>
      simp only [x, r, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.rF a)
  | sA a =>
      simp only [x, s, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.sA a)
  | sB a =>
      simp only [x, s, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.sB a)
  | sC a =>
      simp only [x, s, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.sC a)
  | sD a =>
      simp only [x, s, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.sD a)
  | sE a =>
      simp only [x, s, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.sE a)
  | long_word a =>
      simp only [x, h, r, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.long_word a)
  | short_word a =>
      simp only [x, h, s, map_mul, map_inv, FreeGroup.lift_apply_of, assignment]
      exact mul_inv_eq_one.mpr (R.short_word a)

/-- Evaluation into any group satisfying exactly the displayed equations. -/
def lift (d : BorelWeylData F G) (R : d.Relations) : Group F →* G :=
  PresentedGroup.toGroup (f := assignment d) (by intro w hw; exact lift_relator d R w hw)

@[simp] theorem lift_root (d : BorelWeylData F G) (R : d.Relations)
    (i : Fin 6) (a : F) : lift d R ((data (F := F)).x i a) = d.x i a :=
  PresentedGroup.toGroup.of _

@[simp] theorem lift_torus (d : BorelWeylData F G) (R : d.Relations)
    (p : Fˣ × Fˣ) : lift d R ((data (F := F)).torus p) = d.torus p :=
  PresentedGroup.toGroup.of _

@[simp] theorem lift_r (d : BorelWeylData F G) (R : d.Relations) :
    lift d R (data (F := F)).r = d.r := PresentedGroup.toGroup.of _

@[simp] theorem lift_s (d : BorelWeylData F G) (R : d.Relations) :
    lift d R (data (F := F)).s = d.s := PresentedGroup.toGroup.of _

theorem lift_product (d : BorelWeylData F G) (R : d.Relations)
    (a : Fin 6 → F) : lift d R ((data (F := F)).product a) = d.product a := by
  simp only [PositiveRoots.product, map_mul, lift_root]

/-- Evaluation in the actual octonion automorphism group. -/
def evaluation [CharP F 2] : Group F →* Model F := lift modelData model_relations

end Atlas.G2.RootPresentationRecognition.Presentation
