/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianGlueStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianGlueClassification
public import Mathlib.FieldTheory.Finite.Basic

/-!
# IcosianGlueStabilizer

The block stabilizer is parametrized by one nonzero scalar and two field
elements. The resulting equivalence counts it as q squared times q minus one.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianGlueStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


noncomputable section
namespace Atlas.Codes
open Matrix

theorem icosianGlue_preserves_iff_mem {F : Type*} [Field F] [Finite F]
    (g : IcosianGlueBlocks F) (hg : IcosianGluePreserves g) (x : IcosianGlueWord F) :
    g • x ∈ icosianGlue F ↔ x ∈ icosianGlue F := by
  constructor
  · intro hx
    let f : icosianGlue F → icosianGlue F := fun y => ⟨g • y.val,hg y.val y.property⟩
    have hf : Function.Injective f := by
      intro y z h
      apply Subtype.ext
      exact (MulAction.injective g) (congrArg Subtype.val h)
    obtain ⟨y,hy⟩ := Finite.surjective_of_injective hf ⟨g • x,hx⟩
    have he : y.val=x := (MulAction.injective g) (congrArg Subtype.val hy)
    exact he ▸ y.property
  · exact hg x

/-- The actual block-fixing subgroup preserving the concrete glue submodule. -/
def icosianGlueBlockStabilizer (F : Type*) [Field F] [Finite F] :
    Subgroup (IcosianGlueBlocks F) where
  carrier := {g | IcosianGluePreserves g}
  one_mem' := by intro x hx; simpa using hx
  mul_mem' := by
    intro g h hg hh x hx
    simpa only [mul_smul] using hg (h • x) (hh x hx)
  inv_mem' := by
    intro g hg x hx
    apply (icosianGlue_preserves_iff_mem g hg (g⁻¹ • x)).mp
    simpa using hx

def icosianGlueMatrix {F : Type*} [Field F] (s : Fˣ) (c : F) :
    SpecialLinearGroup (Fin 2) F :=
  ⟨!![(s : F)⁻¹,c;0,(s : F)],by simp [Matrix.det_fin_two,Units.ne_zero s]⟩

def icosianGlueBlockParameter {F : Type*} [Field F] (s : Fˣ) (u v : F) :
    IcosianGlueBlocks F := fun i => icosianGlueMatrix s (![u,v,-u-v] i)

theorem icosianGlueBlockParameter_form {F : Type*} [Field F] (s : Fˣ) (u v : F) :
    IcosianGlueBlockForm (icosianGlueBlockParameter s u v) s ![u,v,-u-v] := by
  constructor
  · simp [Matrix.cons_val_two]
  · intro i
    exact ⟨rfl,rfl,rfl,rfl⟩

def icosianGlueBlockParameterElement {F : Type*} [Field F] [Finite F]
    (p : Fˣ × F × F) : icosianGlueBlockStabilizer F :=
  ⟨icosianGlueBlockParameter p.1 p.2.1 p.2.2,
    icosianGlue_form_preserves _ _ _ (icosianGlueBlockParameter_form _ _ _)⟩

theorem icosianGlueBlockParameterElement_injective {F : Type*} [Field F] [Finite F] :
    Function.Injective (icosianGlueBlockParameterElement (F := F)) := by
  intro p q h
  have hmat : icosianGlueBlockParameter p.1 p.2.1 p.2.2=
      icosianGlueBlockParameter q.1 q.2.1 q.2.2 := congrArg Subtype.val h
  have hs : p.1=q.1 := Units.ext (congrArg (fun g : IcosianGlueBlocks F => g 0 1 1) hmat)
  have hu : p.2.1=q.2.1 := congrArg (fun g : IcosianGlueBlocks F => g 0 0 1) hmat
  have hv : p.2.2=q.2.2 := congrArg (fun g : IcosianGlueBlocks F => g 1 0 1) hmat
  exact Prod.ext hs (Prod.ext hu hv)

theorem icosianGlueBlockParameterElement_surjective {F : Type*} [Field F] [Finite F] :
    Function.Surjective (icosianGlueBlockParameterElement (F := F)) := by
  intro g
  obtain ⟨s,c,hc,hg⟩ := icosianGlue_preserves_form g.val g.property
  have he : ![c 0,c 1,-c 0-c 1]=c := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change -c 0-c 1=c 2
      linear_combination -hc
  refine ⟨(s,c 0,c 1),?_⟩
  apply Subtype.ext
  funext i
  apply Subtype.ext
  ext r t
  rcases hg i with ⟨h00,h01,h10,h11⟩
  change (icosianGlueMatrix s (![c 0,c 1,-c 0-c 1] i)).val r t=(g.val i).val r t
  rw [he]
  fin_cases r <;> fin_cases t <;> simp [icosianGlueMatrix,h00,h01,h10,h11]

def icosianGlueBlockParameterEquiv {F : Type*} [Field F] [Finite F] :
    (Fˣ × F × F) ≃ icosianGlueBlockStabilizer F :=
  Equiv.ofBijective icosianGlueBlockParameterElement
    ⟨icosianGlueBlockParameterElement_injective,icosianGlueBlockParameterElement_surjective⟩

theorem icosianGlueBlockStabilizer_card {F : Type*} [Field F] [Finite F] :
    Nat.card (icosianGlueBlockStabilizer F)=(Nat.card F-1)*Nat.card F^2 := by
  rw [← Nat.card_congr (icosianGlueBlockParameterEquiv (F := F)),Nat.card_prod,Nat.card_prod]
  rw [Nat.card_units]
  ring

theorem icosianGlueBlockStabilizer_card_four {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F=4) : Nat.card (icosianGlueBlockStabilizer F)=48 := by
  rw [icosianGlueBlockStabilizer_card,hF]
  norm_num

end Atlas.Codes
