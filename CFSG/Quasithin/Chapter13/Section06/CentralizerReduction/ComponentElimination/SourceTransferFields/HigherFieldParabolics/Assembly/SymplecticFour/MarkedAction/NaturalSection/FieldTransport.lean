module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection.Models
public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible

/-!
# Transporting the natural symplectic coordinates to the specified field

Equal field cardinalities give a field isomorphism. Applying it entrywise
to symplectic matrices and vectors gives an actual binary-linear action
isomorphism. The group-order comparison supplies the required cardinality
from the classifier's arbitrary group marking.

Source: the natural-module conclusion of B.5.1 used in 13.6.19, printed
pp.99 and 931 of Aschbacher–Smith, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection

private def fieldGroupEquiv {E F : Type*} [Field E] [Field F] (σ : E ≃+* F) :
    Sp E ≃* Sp F where
  toFun g := ⟨g.val.map σ, SymplecticGroup.map_mem g.property σ⟩
  invFun g := ⟨g.val.map σ.symm, SymplecticGroup.map_mem g.property σ.symm⟩
  left_inv g := by apply Subtype.ext; ext i j; exact σ.symm_apply_apply _
  right_inv g := by apply Subtype.ext; ext i j; exact σ.apply_symm_apply _
  map_mul' _ _ := Subtype.ext Matrix.map_mul

private def fieldVectorEquiv {E F : Type*} [Field E] [Field F]
    [Algebra (ZMod 2) E] [Algebra (ZMod 2) F] (σ : E ≃+* F) :
    Vector E ≃ₗ[ZMod 2] Vector F where
  toFun v i := σ (v i)
  invFun v i := σ.symm (v i)
  left_inv v := by ext i; exact σ.symm_apply_apply _
  right_inv v := by ext i; exact σ.apply_symm_apply _
  map_add' v w := by ext i; exact σ.map_add _ _
  map_smul' c v := by ext i; exact ZMod.map_smul σ c (v i)

/-- Transport both matrices and vectors through the same field isomorphism. -/
def fieldActionEquiv {E F : Type*} [Field E] [Field F]
    [Algebra (ZMod 2) E] [Algebra (ZMod 2) F] (σ : E ≃+* F) :
    ActionEquiv (restrictScalars (k := ZMod 2) (symplecticNatural (k := E) 2))
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) where
  groupEquiv := fieldGroupEquiv σ
  linearEquiv := fieldVectorEquiv σ
  intertwines g v := by
    ext i
    change σ (∑ j, g.val i j * v j) = ∑ j, σ (g.val i j) * σ (v j)
    simp only [map_sum, map_mul]

/-- Recover the prescribed field from the actual group isomorphism, and
transport the classifier's coordinates without constraining its orientation. -/
theorem natural_over_field {C V F : Type*} [Group C] [AddCommGroup V]
    [Module (ZMod 2) V] [Field F] [Finite F] [Algebra (ZMod 2) F]
    {ρ : Representation (ZMod 2) C V} {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 0 < m) (mark : C ≃* Sp F)
    (E : BinaryField) (e : ActionEquiv ρ (binarySymplectic E)) :
    Nonempty (ActionEquiv ρ
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))) := by
  let := Fintype.ofFinite F
  let := Fintype.ofFinite E.Carrier
  have hc := field_card hF hm E (mark.symm.trans e.groupEquiv)
  let σ := FiniteField.ringEquivOfCardEq (K := E.Carrier) (K' := F)
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let a := fieldActionEquiv σ
  exact ⟨{ groupEquiv := e.groupEquiv.trans a.groupEquiv
           linearEquiv := e.linearEquiv.trans a.linearEquiv
           intertwines := fun g v =>
             (congrArg a.linearEquiv (e.intertwines g v)).trans
               (a.intertwines (e.groupEquiv g) (e.linearEquiv v)) }⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection
