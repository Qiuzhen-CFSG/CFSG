module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Geometry

/-!
# Faithful centralizer action on a homogeneous multiplicity space

For an H-subrepresentation R of V, the centralizer of H acts on
Hom_H(R,V) by postcomposition. If V is the full homogeneous part of R
and the ambient representation is faithful, this multiplicity action is
faithful. Indeed, intertwiners cover every copy of R, and those copies span V.
For irreducible R, evaluation at any nonzero vector is injective by Schur's
lemma, so a single evaluation detects every nontrivial centralizer actor.

The source consumer is the nonfaithful marked-constituent branch in
Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.
Source: Aschbacher--Smith, paragraphs before G.11.8, printed p.368.
This constructs the binary action; it does not assert projective or
semilinear recognition over the Schur field.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.CentralizerMultiplicity
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (H : Subgroup D)
  (R : Subrepresentation (ρ.comp H.subtype))

/-- The actual H-intertwiners from the chosen constituent into V. -/
abbrev Multiplicity := IntertwiningMap R.toRepresentation (ρ.comp H.subtype)

/-- The original centralizer acts by postcomposition. -/
def action : Representation (ZMod 2) (centralizer (H : Set D)) (Multiplicity ρ H R) where
  toFun c := {
    toFun := fun f => {
      toLinearMap := (ρ c).comp f.toLinearMap
      isIntertwining' h := by
        ext w
        change ρ c (f (R.toRepresentation h w)) = ρ h (ρ c (f w))
        rw [f.isIntertwining]
        change ρ c (ρ h (f w)) = ρ h (ρ c (f w))
        simpa only [map_mul, Module.End.mul_apply] using
          congrArg (fun d : D => ρ d (f w))
            ((mem_centralizer_iff.mp c.property) h h.property).symm }
    map_add' := by intro f g; ext w; exact map_add (ρ c) (f w) (g w)
    map_smul' := by intro a f; ext w; exact map_smul (ρ c) a (f w) }
  map_one' := by ext f w; exact congrArg (fun t : Module.End (ZMod 2) V => t (f w)) ρ.map_one
  map_mul' c d := by
    ext f w
    exact congrArg (fun t : Module.End (ZMod 2) V => t (f w)) (ρ.map_mul c d)

@[simp] theorem action_apply (c : centralizer (H : Set D))
    (f : Multiplicity ρ H R) (w : R.toSubmodule) : action ρ H R c f w = ρ c (f w) := rfl

/-- Evaluation at a vector of the chosen constituent. -/
def evaluationAt (w : R.toSubmodule) : Multiplicity ρ H R →ₗ[ZMod 2] V where
  toFun f := f w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A nonzero vector detects maps from an irreducible representation. -/
theorem evaluationAt_injective (hi : IsIrreducible R.toRepresentation)
    {w : R.toSubmodule} (hw : w ≠ 0) : Function.Injective (evaluationAt ρ H R w) := by
  let : IsIrreducible R.toRepresentation := hi
  have hz (f : Multiplicity ρ H R) (hf : f w = 0) : f = 0 := by
    rcases IsIrreducible.injective_or_eq_zero f with hinj | he
    · exact (hw (hinj (hf.trans (map_zero f).symm))).elim
    · exact he
  intro f g hfg
  apply sub_eq_zero.mp
  apply hz
  exact sub_eq_zero.mpr hfg

/-- Evaluation at one nonzero vector detects whether a centralizer actor is trivial. -/
theorem action_eq_one_iff (hi : IsIrreducible R.toRepresentation)
    {w : R.toSubmodule} (hw : w ≠ 0) (c : centralizer (H : Set D)) :
    action ρ H R c = 1 ↔ ∀ f : Multiplicity ρ H R, ρ c (f w) = f w := by
  constructor
  · intro he f
    exact congrArg (fun t : Module.End (ZMod 2) (Multiplicity ρ H R) => t f w) he
  · intro he
    apply LinearMap.ext
    intro f
    apply evaluationAt_injective ρ H R hi hw
    exact he f

/-- Homogeneity and faithfulness make the centralizer action faithful. -/
theorem action_faithful (hf : Function.Injective ρ)
    (hhom : Homogeneous.homogeneousPart R ⊤ = ⊤) :
    Function.Injective (action ρ H R) := by
  intro a b hab
  have hle : Homogeneous.homogeneousPart R ⊤ ≤ (ρ a - ρ b).ker := by
    apply iSup_le
    intro J
    apply iSup_le
    intro hJ
    obtain ⟨e⟩ := (Homogeneous.sameModule_iff_repEquiv R J).mp hJ.2
    let f : Multiplicity ρ H R := {
      toLinearMap := J.toSubmodule.subtype.comp e.toLinearEquiv.toLinearMap
      isIntertwining' h := by
        ext w
        exact congrArg Subtype.val (LinearMap.congr_fun (e.isIntertwining' h) w) }
    intro w hw
    obtain ⟨u,hu⟩ := e.surjective (⟨w,hw⟩ : J)
    have he := congrArg (fun t : Module.End (ZMod 2) (Multiplicity ρ H R) => t f u) hab
    change ρ a (f u) = ρ b (f u) at he
    have hfu : f u = w := congrArg Subtype.val hu
    rw [hfu] at he
    exact sub_eq_zero.mpr he
  apply Subtype.ext
  apply hf
  ext w
  exact sub_eq_zero.mp (hle (hhom.symm ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule (ZMod 2) V))))

end Representation.CentralizerMultiplicity
