module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.DiagramNatural.SLThree
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.DiagramNatural.SpFour

/-!+# Natural-module rigidity for the actual induced diagram action

The binary natural SL₃ module, two identical copies of it, and the binary
natural Sp₄ module admit no equivalence with their twist by a genuine
diagram action. The imported proofs distinguish fixed-space dimensions of
the actual root planes or parabolic two-cores.

Here the automorphism is the one in `InducedDiagramAction`: conjugation by
its specified normalizing element of T, transported through the same model
identification φ. Its Borel and two parabolics are the literal standard
matrix subgroups. The source field hypotheses f > 1 and Odd f are more than
needed: the SL₃ argument works in every binary degree, and Sp₄ needs only
f > 1. No automorphism family tag or FF exclusion is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.4.2(2),(3),
B.5.1(1)(ii), E.2.2(2)(b), and the diagram case of 15.3.65,
printed pp.86, 99--100, 215--216, 1152.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.DiagramNatural
open Representation
open Matrix.PSL3.LinearThree
open Theory.SpecificGroups.SymplecticFour

variable {D F : Type*} [Group D] [Field F] [Finite F] [Algebra (ZMod 2) F]
    {K T : Subgroup D}

/-- Rigidity for the actual SL₃ automorphism induced using the given model map. -/
theorem slThree_induced_not_intertwines {f : ℕ} (hF : Nat.card F = 2 ^ f)
    {φ : K ≃* Matrix.SpecialLinearGroup (Fin 3) F}
    (d : InducedDiagramAction K T φ (borelSL F) (pointParabolicSL F) (lineParabolicSL F)) :
    let σ := restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
    ¬ ∃ e : (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F),
      ∀ g v, e (σ g v) = (σ.comp d.automorphism.toMonoidHom) g (e v) :=
  slThree_not_intertwines hF d.automorphism d.borel d.moves

/-- The same actual diagram action excludes the doubled natural alternative
of B.5.1(1)(ii). The two summands use the identical model identification. -/
theorem slThree_prod_self_induced_not_intertwines {f : ℕ} (hF : Nat.card F = 2 ^ f)
    {φ : K ≃* Matrix.SpecialLinearGroup (Fin 3) F}
    (d : InducedDiagramAction K T φ (borelSL F) (pointParabolicSL F) (lineParabolicSL F)) :
    let σ := restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
    ¬ ∃ e : ((Fin 3 → F) × (Fin 3 → F)) ≃ₗ[ZMod 2] ((Fin 3 → F) × (Fin 3 → F)),
      ∀ g v, e (σ.prod σ g v) = ((σ.prod σ).comp d.automorphism.toMonoidHom) g (e v) :=
  slThree_prod_self_not_intertwines hF d.automorphism d.borel d.moves

/-- Rigidity for the actual Sp₄ automorphism induced using the given model map. -/
theorem spFour_induced_not_intertwines {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) {φ : K ≃* Sp F}
    (d : InducedDiagramAction K T φ borel pointParabolic planeParabolic) :
    let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
    ¬ ∃ e : Vector F ≃ₗ[ZMod 2] Vector F,
      ∀ g v, e (σ g v) = (σ.comp d.automorphism.toMonoidHom) g (e v) := by
  let : CharP F 2 := (Algebra.charP_iff (ZMod 2) F 2).mp inferInstance
  exact spFour_not_intertwines hF hf d.automorphism d.moves

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.DiagramNatural
