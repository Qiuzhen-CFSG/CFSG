module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.ModelRelations
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Faithfulness of the six-positive-root presentation

The presented group has six additive root families, the ten commuting pairs
and the five A–F polynomial interchanges. The projection-free collector puts
every presented word into six-coordinate form. The actual octonion coordinates
are injective, so evaluation is faithful and identifies this presented group
with the entire concrete unipotent subgroup. This includes the binary field.

This is the positive part of the finite Borel–Weyl presentation for DGS,
Groups and Graphs, Theorem D, p.224. No assertion about mixed Weyl words or
the full G₂ presentation is made here. The polynomial convention is that
of the licensed ATLAS octonion model.
-/

@[expose] public noncomputable section
namespace Atlas.G2.RootPresentationRecognition.PositivePresentation
variable {F : Type*} [Field F]

/-- A free generator labelled by its positive root and field parameter. -/
def v (i : Fin 6) (a : F) : FreeGroup (Fin 6 × F) := FreeGroup.of (i,a)

/-- Only the stated additive and positive interchange equations are imposed. -/
inductive Relator : FreeGroup (Fin 6 × F) → Prop
  | zero (i : Fin 6) : Relator (v i (0 : F))
  | add (i : Fin 6) (a b : F) : Relator (v i (a+b) * (v i a * v i b)⁻¹)
  | ba (a b : F) : Relator ((v 1 a * v 0 b) * (v 0 b * v 1 a)⁻¹)
  | ca (a b : F) : Relator ((v 2 a * v 0 b) * (v 0 b * v 2 a)⁻¹)
  | cb (a b : F) : Relator ((v 2 a * v 1 b) * (v 1 b * v 2 a)⁻¹)
  | da (a b : F) : Relator ((v 3 a * v 0 b) * (v 0 b * v 3 a)⁻¹)
  | db (a b : F) : Relator ((v 3 a * v 1 b) * (v 1 b * v 3 a)⁻¹)
  | ea (a b : F) : Relator ((v 4 a * v 0 b) * (v 0 b * v 4 a)⁻¹)
  | ec (a b : F) : Relator ((v 4 a * v 2 b) * (v 2 b * v 4 a)⁻¹)
  | ed (a b : F) : Relator ((v 4 a * v 3 b) * (v 3 b * v 4 a)⁻¹)
  | fa (a b : F) : Relator ((v 5 a * v 0 b) * (v 0 b * v 5 a)⁻¹)
  | fb (a b : F) : Relator ((v 5 a * v 1 b) * (v 1 b * v 5 a)⁻¹)
  | dc (a b : F) : Relator ((v 3 a * v 2 b) * (v 0 (3*b*a) * v 2 b * v 3 a)⁻¹)
  | eb (a b : F) : Relator ((v 4 a * v 1 b) * (v 0 (-b*a) * v 1 b * v 4 a)⁻¹)
  | fc (a b : F) : Relator ((v 5 a * v 2 b) * (v 1 (-3*b*a) * v 2 b * v 5 a)⁻¹)
  | fd (a b : F) : Relator ((v 5 a * v 3 b) * (v 0 (-3*b^2*a) * v 1 (3*b*a^2) * v 2 (-2*b*a) * v 3 b * v 5 a)⁻¹)
  | fe (a b : F) : Relator ((v 5 a * v 4 b) * (v 0 (-b^2*a^3) * v 1 (-b*a^3) * v 2 (b*a^2) * v 3 (-b*a) * v 4 b * v 5 a)⁻¹)

/-- The displayed inductive family, regarded as a set of free words. -/
def relators : Set (FreeGroup (Fin 6 × F)) := {w | Relator w}

/-- The ordinary quotient of the free group by these relators. -/
abbrev Presentation (F : Type*) [Field F] := PresentedGroup (relators (F := F))

/-- The six additive root maps in the presented group. -/
def roots : PositiveRoots F (Presentation F) where
  root i := {
    toFun := fun a => PresentedGroup.of (i,a.toAdd)
    map_one' := PresentedGroup.one_of_mem (.zero i)
    map_mul' := fun a b => PresentedGroup.mk_eq_mk_of_mul_inv_mem (.add i a.toAdd b.toAdd) }

/-- The defining equations hold without appealing to the model evaluation. -/
theorem collection : (roots (F := F)).CollectionRelations := by
  constructor
  · constructor
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ba a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ca a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.cb a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.da a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.db a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ea a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ec a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.ed a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fa a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fb a b)
  · constructor
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.dc a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.eb a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fc a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fd a b)
    · intro a b
      exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (.fe a b)

variable {G : Type*} [Group G]

private theorem lift_relator (L : PositiveRoots F G) (R : L.CollectionRelations)
    (w : FreeGroup (Fin 6 × F)) (hw : Relator w) :
    FreeGroup.lift (fun p : Fin 6 × F => L.x p.1 p.2) w = 1 := by
  cases hw with
  | zero i => simp [v]
  | add i a b => simp [v, L.x_add]
  | ba a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.ba, mul_inv_cancel]
  | ca a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.ca, mul_inv_cancel]
  | cb a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.cb, mul_inv_cancel]
  | da a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.da, mul_inv_cancel]
  | db a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.db, mul_inv_cancel]
  | ea a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.ea, mul_inv_cancel]
  | ec a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.ec, mul_inv_cancel]
  | ed a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.ed, mul_inv_cancel]
  | fa a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.fa, mul_inv_cancel]
  | fb a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.fb, mul_inv_cancel]
  | dc a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.dc, mul_inv_cancel]
  | eb a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.eb, mul_inv_cancel]
  | fc a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.fc, mul_inv_cancel]
  | fd a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.fd, mul_inv_cancel]
  | fe a b => simp only [v, map_mul, map_inv, FreeGroup.lift_apply_of, R.fe, mul_inv_cancel]

/-- Evaluation into any group satisfying the explicit positive equations. -/
def lift (L : PositiveRoots F G) (R : L.CollectionRelations) : Presentation F →* G :=
  PresentedGroup.toGroup (f := fun p : Fin 6 × F => L.x p.1 p.2)
    (by intro w hw; exact lift_relator L R w hw)

@[simp] theorem lift_root (L : PositiveRoots F G) (R : L.CollectionRelations)
    (i : Fin 6) (a : F) : lift L R ((roots (F := F)).x i a) = L.x i a :=
  PresentedGroup.toGroup.of _

theorem lift_product (L : PositiveRoots F G) (R : L.CollectionRelations)
    (t : Fin 6 → F) : lift L R ((roots (F := F)).product t) = L.product t := by
  simp only [PositiveRoots.product, map_mul, lift_root]

/-- Internal positive-word collection in the presented group. -/
theorem normalForm (g : Presentation F) : ∃ t, (roots (F := F)).product t = g := by
  apply ((roots (F := F)).mem_generated_iff collection g).mp
  have hgen : (roots (F := F)).generated = ⊤ := PresentedGroup.closure_range_of _
  rw [hgen]
  trivial

/-- Evaluation in the actual octonion group. -/
def evaluation : Presentation F →* Model F := lift modelRoots model_collectionRelations

@[simp] theorem evaluation_product (t : Fin 6 → F) :
    evaluation ((roots (F := F)).product t) = unipotentProduct t := by
  rw [evaluation, lift_product]
  rfl

/-- Faithfulness follows from collection and actual coordinate injectivity. -/
theorem evaluation_injective : Function.Injective (evaluation (F := F)) := by
  apply (injective_iff_map_eq_one evaluation).mpr
  intro g hg
  obtain ⟨t,rfl⟩ := normalForm g
  rw [evaluation_product] at hg
  have ht : t = 0 := unipotentProduct_injective (hg.trans unipotentProduct_zero.symm)
  rw [ht, PositiveRoots.product_zero]

theorem evaluation_range : (evaluation (F := F)).range = unipotent := by
  apply le_antisymm
  · rintro g ⟨p,rfl⟩
    obtain ⟨t,rfl⟩ := normalForm p
    rw [evaluation_product]
    exact unipotentProduct_mem t
  · intro g hg
    rw [unipotent_eq_range] at hg
    obtain ⟨t,rfl⟩ := hg
    exact ⟨roots.product t, evaluation_product t⟩

/-- The actual positive presented group, with no assumed faithfulness. -/
def equivalence : Presentation F ≃* unipotent (K := F) :=
  (MonoidHom.ofInjective evaluation_injective).trans (MulEquiv.subgroupCongr evaluation_range)

@[simp] theorem equivalence_product (t : Fin 6 → F) :
    equivalence ((roots (F := F)).product t) = unipotentEquiv t :=
  Subtype.ext (evaluation_product t)

@[simp] theorem equivalence_root (i : Fin 6) (a : F) :
    equivalence ((roots (F := F)).x i a) = unipotentEquiv (Pi.single i a) := by
  rw [← PositiveRoots.product_single roots i a, equivalence_product]

/-- The positive presentation has the exact expected finite order. -/
theorem card_presentation [Finite F] : Nat.card (Presentation F) = Nat.card F ^ 6 := by
  rw [Nat.card_congr equivalence.toEquiv, card_unipotent]

end Atlas.G2.RootPresentationRecognition.PositivePresentation
