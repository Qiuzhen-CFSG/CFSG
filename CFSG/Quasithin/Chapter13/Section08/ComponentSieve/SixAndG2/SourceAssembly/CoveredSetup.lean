module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Final
public import Theory.Representation.HexacodeAction.Cover

/-!
# The literal covered-A₆ / L₄(2) terminal setup

The covered quotient is marked over the original six-letter projection,
so its local module and flag are the original ones. The four-dimensional
whole quotient model and the original kernel line of order two give
|U_H|=32. Conjugation gives the same order at every original critical
endpoint. This is the input to the separate 13.8.29–32 tensor and chief
factor argument, owned by qt-d-138-linear-four-source.
Source: Aschbacher–Smith, 13.8.27–28, printed p.963.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open CriticalGeometry CriticalGeometry.AsymmetricPair SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Construction of the covered local flag and the original L₄ action,
including the order of U_H and every conjugate Uγ. -/
theorem covered_terminal_setup
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hm : HasActionModel ρ projectiveFourRepresentation) :
    Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) ∧
      HasActionModel ρ linearFourRepresentation ∧
      Nat.card (Source.UH H V₃) = 32 ∧ rank (Source.UH H V₃) = 5 ∧
      ∀ c : CriticalPair L (T : Subgroup G) H V,
        Nat.card (c.Ugamma V₃) = 32 := by
  have hflag : Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
    rcases local_quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
    · obtain ⟨eC⟩ := hcover
      have hz := Nat.card_congr (centerCongr (e.symm.trans eC)).toEquiv
      rw [alternatingGroup.center_eq_bot (by simp), card_bot,
        Representation.Hexacode.even_center_card] at hz
      contradiction
    · exact local_covered_flag_model d e he
  obtain ⟨eH, eU, he⟩ := hm
  have hd : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 4 := by
    simpa only [Module.finrank_fin_fun] using eU.finrank_eq
  have hi : V₁.relIndex (Source.UH H V₃) = 16 := by
    rw [relIndex_eq_two_pow_quotient_finrank]
    change 2 ^ Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 16
    rw [hd]
    decide
  have hc : Nat.card (Source.UH H V₃) = 32 := by
    have hh := (V₁.subgroupOf (Source.UH H V₃)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (d.line_le_uh H)).toEquiv, d.line_card] at hh
    change 2 * V₁.relIndex (Source.UH H V₃) = Nat.card (Source.UH H V₃) at hh
    rw [hi] at hh
    exact hh.symm
  refine ⟨hflag, ⟨eH.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)),
    eU, he⟩, hc, ?_, ?_⟩
  · change Nat.log 2 (Nat.card (Source.UH H V₃)) = 5
    rw [hc]
    decide
  · intro c
    change Nat.card ((Source.UH H V₃).map (MulAut.conj (c.gb : G)).toMonoidHom) = 32
    rw [card_map_of_injective (MulAut.conj (c.gb : G)).injective, hc]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
