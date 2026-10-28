module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FullAutomizer
public import Theory.Representation.G2NaturalOffenders.Long
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.Basic

/-!
# Attaining involutions on the original natural module

The original central cover and its marked quotient have identical fixed
codimensions for every inner actor. The marked model therefore transfers an
involution directly to the actual induced automizer with its order unchanged;
no lift of order two in L is required. The witnesses are standard transvections
for SL₃ and Sp₄, and a long-root element for G₂. Their fixed quotient dimensions
are n, n, and 2n respectively.

The Source endpoint combines these witnesses with the full-automizer lower
bounds to compute the genuine E.3 parameter, retaining nonsplit central covers.
Source: Aschbacher--Smith, I.2.3(1), B.4.6, and 11.2.2(1),
printed pp.413,88--90,767.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (c : Coordinates D S.field) [IsElementaryAbelian 2 V]

/-- On inner actors the original central cover preserves fixed codimension exactly. -/
theorem inner_fixedCodim (a : inducedAutomizer V L) :
    fixedCodim (automizerRepresentation V) (zpowers (a : Automizer V)) =
      fixedCodim (restrictScalars (k := ZMod 2) c.modelAction)
        (zpowers (layerEquiv D S c a)) := by
  let Q := fixedSpace (restrictScalars (k := ZMod 2) c.modelAction)
    (zpowers (layerEquiv D S c a))
  have hfix : fixedSpace (automizerRepresentation V) (zpowers (a : Automizer V)) =
      Q.comap (projectionLinear D S c) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change automizerRepresentation V a v = v ↔
      projectionLinear D S c v ∈ fixedSpace
        (restrictScalars (k := ZMod 2) c.modelAction) (zpowers (layerEquiv D S c a))
    rw [mem_fixedSpace_zpowers_iff]
    obtain ⟨l,rfl⟩ := layerAction_surjective D a
    rw [layerEquiv_apply]
    change automizerRepresentation V (layerAction D l) v = v ↔
      c.modelAction (c.quotientMap l) (c.projection v.toMul).toAdd = (c.projection v.toMul).toAdd
    rw [← NaturalFixedSpaces.centralizes_vector_iff D S c l v.toMul]
    constructor
    · intro h
      exact mul_inv_eq_iff_eq_mul.mp
        (congrArg (fun w : Additive V => (w.toMul : G)) h)
    · intro h
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr h
  let q := Q.mkQ.comp (projectionLinear D S c)
  have hq : Function.Surjective q := Q.mkQ_surjective.comp (projectionLinear_surjective D S c)
  have hk : q.ker = fixedSpace (automizerRepresentation V) (zpowers (a : Automizer V)) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    exact hfix.symm
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans
    (q.quotKerEquivOfSurjective hq)).finrank_eq

/-- An attaining involution in the marked model gives one in the literal automizer. -/
theorem attainment_of_model
    (hmodel : ∃ g : c.ModelGroup, orderOf g = 2 ∧
      fixedCodim (restrictScalars (k := ZMod 2) c.modelAction) (zpowers g) =
        naturalParameter D S c) :
    ∃ a : Automizer V, orderOf a = 2 ∧
      fixedCodim (automizerRepresentation V) (zpowers a) = naturalParameter D S c := by
  obtain ⟨g,hg,hcod⟩ := hmodel
  let a := (layerEquiv D S c).symm g
  refine ⟨a, ?_, ?_⟩
  · exact (Subgroup.orderOf_coe a).trans (((layerEquiv D S c).symm.orderOf_eq g).trans hg)
  · rw [inner_fixedCodim D S c, show layerEquiv D S c a = g from
      (layerEquiv D S c).apply_symm_apply g]
    exact hcod

section Model
variable {H F I : Type*} [Group H] [Field F] [CharP F 2] [Finite F]
  [Algebra (ZMod 2) F] [Fintype I] [DecidableEq I]

omit [CharP F 2] [Finite F] [Fintype I] in
private theorem single_add_codim (ρ : Representation F H (I → F)) (a : H)
    (i j : I) (ha : ∀ v, ρ a v = v + Pi.single i (v j)) :
    fixedCodim (restrictScalars (k := ZMod 2) ρ) (zpowers a) = Module.finrank (ZMod 2) F := by
  let q : (I → F) →ₗ[ZMod 2] F := ((LinearMap.proj j : (I → F) →ₗ[F] F)).restrictScalars (ZMod 2)
  have hq : Function.Surjective q := fun x => ⟨Pi.single j x, Pi.single_eq_same _ _⟩
  have hk : q.ker = fixedSpace (restrictScalars (k := ZMod 2) ρ) (zpowers a) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change v j = 0 ↔ ρ a v = v
    rw [ha, add_eq_left]
    constructor
    · intro h; simp only [h, Pi.single_zero]
    · intro h
      have hh := congrFun h i
      simpa only [Pi.single_eq_same, Pi.zero_apply] using hh
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans
    (q.quotKerEquivOfSurjective hq)).finrank_eq

omit [Finite F] in
private theorem sl3_model_attains : ∃ a : Matrix.SpecialLinearGroup (Fin 3) F,
    orderOf a = 2 ∧
      fixedCodim (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))
        (zpowers a) = Module.finrank (ZMod 2) F := by
  let a := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) (1 : F)
  have ha (v : Fin 3 → F) : specialLinearNatural 3 a v = v + Pi.single 0 (v 1) := by
    change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single 0 1 1).mulVec v = _
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul]
    congr 1
    ext k
    by_cases hk : k = 0 <;> simp [hk]
  refine ⟨a, ?_, single_add_codim (specialLinearNatural 3) a 0 1 ha⟩
  apply orderOf_eq_prime
  · rw [pow_two]
    change a * a = 1
    simpa only [CharTwo.neg_eq] using
      Matrix.SpecialLinearGroup.transvection_mul_neg (by decide : (0 : Fin 3) ≠ 1) (1 : F)
  · intro h
    have hh := ha (Pi.single 1 1)
    rw [h, map_one, Module.End.one_apply] at hh
    have hz := congrFun hh 0
    simp at hz

omit [Finite F] in
private theorem sp4_model_attains : ∃ a : Matrix.symplecticGroup (Fin 2) F,
    orderOf a = 2 ∧
      fixedCodim (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))
        (zpowers a) = Module.finrank (ZMod 2) F := by
  let a := Representation.OneCohomology.SymplecticFour.rootElement 0 (1 : F)
  have ha (v : (Fin 2 ⊕ Fin 2) → F) : symplecticNatural 2 a v =
      v + Pi.single (.inl 0) (v (.inr 0)) := by
    ext i
    fin_cases i <;>
      simp [a, Representation.OneCohomology.SymplecticFour.rootElement,
        Representation.OneCohomology.SymplecticFour.rootMatrix, symplecticNatural,
        Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fin.sum_univ_two,
        Fintype.sum_sum_type]
  exact ⟨a, Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.rootElement_orderOf
    0 one_ne_zero, single_add_codim (symplecticNatural 2) a (.inl 0) (.inr 0) ha⟩

private theorem g2_model_attains {n : ℕ} (hc : Nat.card F = 2 ^ n) :
    ∃ a : Atlas.G2.Model F, orderOf a = 2 ∧
      fixedCodim (restrictScalars (k := ZMod 2) (g2Natural F)) (zpowers a) = 2 * n := by
  refine ⟨Atlas.G2.rootA 1, ?_, ?_⟩
  · apply orderOf_eq_prime
    · simp [pow_two, Atlas.G2.rootA_add, CharTwo.add_self_eq_zero]
    · intro h
      exact one_ne_zero (Atlas.G2.rootA_injective (h.trans Atlas.G2.rootA_zero.symm))
  · change fixedCodim (Atlas.G2.NaturalOffenders.binaryNatural (F := F))
      (zpowers (Atlas.G2.rootA 1)) = 2 * n
    rw [Atlas.G2.NaturalOffenders.natural_fixedCodim_eq]
    exact Atlas.G2.NaturalOffenders.fixedCodim_rootA hc 1 one_ne_zero
end Model

omit [IsElementaryAbelian 2 V] in
/-- All three actual markings contain an involution attaining the source parameter. -/
theorem involution_attains (c : Coordinates D S.field) :
    letI := D.elementary; ∃ a : Automizer V, orderOf a = 2 ∧
      fixedCodim (automizerRepresentation V) (zpowers a) = naturalParameter D S c := by
  let := D.elementary
  apply attainment_of_model D S c
  cases c with
  | sl3 m =>
    change ∃ a : Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier, orderOf a = 2 ∧
      fixedCodim (restrictScalars (k := ZMod 2) (specialLinearNatural (k := S.field.Carrier) 3))
        (zpowers a) = S.field.degree
    simpa only [Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] using
      (sl3_model_attains (F := S.field.Carrier))
  | sp4 m =>
    change ∃ a : Matrix.symplecticGroup (Fin 2) S.field.Carrier, orderOf a = 2 ∧
      fixedCodim (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))
        (zpowers a) = S.field.degree
    simpa only [Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] using
      (sp4_model_attains (F := S.field.Carrier))
  | g2 m => exact g2_model_attains S.field.card_eq
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
