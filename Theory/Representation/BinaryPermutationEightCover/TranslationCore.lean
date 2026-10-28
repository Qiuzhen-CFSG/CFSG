module
public import Theory.Representation.BinaryPermutationEightCover.Translations
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic
public import Theory.PGroupCore
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Transvections in the two-core of the eight-coordinate code stabilizer

Distinct coordinate evaluations make the action of the actual A₈ code
stabilizer faithful. Its action fixes the constant word. The kernel on
the quotient by that line is elementary abelian, and contains every affine
translation constructed from a functional vanishing on the constant word.
A difference of two coordinate evaluations supplies a translation moving
the code, so the stabilizer's two-core acts nontrivially.

Source: Aschbacher–Smith, Lemma 12.3.3, printed p.808. The ambient
normalizer transport is developed in the companion Normalizer module.
-/

@[expose] public noncomputable section
open Module Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.EightCore
variable (U : Submodule (ZMod 2) (core (Fin 8)))
  (hd : finrank (ZMod 2) U = 4) (hone : oneWord ∈ U)
  (hw : ∀ v ∈ U, v ≠ 0 → v ≠ oneWord → wordWeight v.val = 4)

include hd hw in
theorem code_stabilizer_faithful :
    Function.Injective (stabilizerRepresentation (alternatingCoreRepresentation (Fin 8)) U) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro i
  apply code_evaluation_injective U hd hw
  funext v
  exact congrArg (fun t : Module.End (ZMod 2) U => (t v).val.val i) he

def codePointAction : subspaceStabilizer (alternatingCoreRepresentation (Fin 8)) U →*
    Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer (⟨oneWord,hone⟩ : U) :=
  let α := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom.comp
    (stabilizerRepresentation (alternatingCoreRepresentation (Fin 8)) U).asGroupHom
  α.codRestrict _ (by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rfl)

include hd hw in
theorem codePointAction_injective : Function.Injective (codePointAction U hone) := by
  intro g h he
  apply code_stabilizer_faithful U hd hw
  apply LinearMap.ext
  intro v
  exact LinearEquiv.congr_fun (congrArg Subtype.val he) v

theorem codeTranslation_mem_twoCore
    (φ : Module.Dual (ZMod 2) U) (hφ : φ ⟨oneWord,hone⟩ = 0) :
    (⟨⟨codeTranslation U hd hone hw φ hφ,codeTranslation_even U hd hone hw φ hφ⟩,
      codeTranslation_mem_stabilizer U hd hone hw φ hφ⟩ :
      subspaceStabilizer (alternatingCoreRepresentation (Fin 8)) U) ∈
        pCore 2 (subspaceStabilizer (alternatingCoreRepresentation (Fin 8)) U) := by
  let z : U := ⟨oneWord,hone⟩
  let α := codePointAction U hone
  let q := Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction z
  have hp : IsPGroup 2 ((q.comp α).ker) := by
    change IsPGroup 2 (q.ker.comap α)
    exact (IsElementaryAbelian.isPGroup 2 _).comap_of_injective α
      (codePointAction_injective U hd hone hw)
  have hle : (q.comp α).ker ≤ pCore 2 _ := le_sSup ⟨inferInstance,hp⟩
  apply hle
  apply (Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff z _).mpr
  intro v
  have ha : (α ⟨⟨codeTranslation U hd hone hw φ hφ,codeTranslation_even U hd hone hw φ hφ⟩,
      codeTranslation_mem_stabilizer U hd hone hw φ hφ⟩).val v = v + φ v • z := by
    apply Subtype.ext
    exact codeTranslation_action U hd hone hw φ hφ v
  rw [ha,add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)

include hd hone hw in
/-- The actual two-core of the code stabilizer acts nontrivially on the code. -/
theorem code_twoCore_moves :
    ∃ g : subspaceStabilizer (alternatingCoreRepresentation (Fin 8)) U,
      g ∈ pCore 2 (subspaceStabilizer (alternatingCoreRepresentation (Fin 8)) U) ∧
      ∃ v : U, alternatingCoreRepresentation (Fin 8) g.val v.val ≠ v.val := by
  classical
  have hn : ∃ v : U, v.val.val 0 ≠ v.val.val 1 := by
    by_contra! he
    have hh := code_evaluation_injective U hd hw (funext he)
    exact (by decide : (0 : Fin 8) ≠ 1) hh
  obtain ⟨v,hv⟩ := hn
  let φ := codeEvaluation U 0 + codeEvaluation U 1
  have hφ : φ ⟨oneWord,hone⟩ = 0 := by change (1 : ZMod 2) + 1 = 0; decide
  let g : subspaceStabilizer (alternatingCoreRepresentation (Fin 8)) U :=
    ⟨⟨codeTranslation U hd hone hw φ hφ,codeTranslation_even U hd hone hw φ hφ⟩,
      codeTranslation_mem_stabilizer U hd hone hw φ hφ⟩
  refine ⟨g,codeTranslation_mem_twoCore U hd hone hw φ hφ,v,?_⟩
  intro he
  have ha := codeTranslation_action U hd hone hw φ hφ v
  change alternatingCoreRepresentation (Fin 8) g.val v.val = _ at ha
  rw [he] at ha
  have hc := congrArg (fun w : core (Fin 8) => w.val 0) ha
  change v.val.val 0 = v.val.val 0 + (v.val.val 0 + v.val.val 1) * 1 at hc
  rw [mul_one] at hc
  have hz := add_eq_left.mp hc.symm
  exact hv (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg, CharTwo.neg_eq] using hz))

end BinaryPermutation.EightCore
