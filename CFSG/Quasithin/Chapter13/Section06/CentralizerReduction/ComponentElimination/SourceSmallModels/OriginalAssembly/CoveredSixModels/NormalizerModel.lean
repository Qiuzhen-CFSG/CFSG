module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels.Full
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer.Action

/-!
# The literal U_K model used by the covered-six normalizer contradiction

The B.5 moved space is identified with the original ambient commutator U_K.
Transport the full hexacode coordinates along this actual multiplication
map. The resulting model retains ambient conjugation on each element of U_K
and the entire even-cover range, exactly as required by the normalizer proof.

Source: Aschbacher--Smith 13.6.22, printed p.932.
-/

public section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
open ComponentSelection SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]
  (K L T : Subgroup G) (z v : G)
  (hL : Tv T v ≤ normalizer (Lv L v : Set G))
  (hz : Tv T v ≤ centralizer ({z} : Set G))
  [IsElementaryAbelian 2 (WK K L T z v)]
  [IsElementaryAbelian 2 (UK K L T z v)]
  [(plusImage K L T z v hL hz K).Normal]

/-- Construct the exact model consumed by `CoveredSixNormalizer.contradiction`.
The original U_K is retained, with no block or full-core identification. -/
theorem exists_normalizer_model
    (m : ActionData (wkRepresentation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (eC : plusImage K L T z v hL hz K ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hquot : IsPGroup 2 (Gplus K L T z v hL hz ⧸ plusImage K L T z v hL hz K))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    ∃ d : CoveredSixNormalizer.Model K L T (UK K L T z v) z v hL hz,
      Atlas.Codes.hexSign.ker ≤ d.embedding.range := by
  let s := m.ambientSection
  let E : Additive (UK K L T z v) ≃ₗ[ZMod 2] s.space.toSubmodule :=
    { (movedEquivUK K L T z v hL hz s).symm.toAdditive with
      map_smul' := ZMod.map_smul (movedEquivUK K L T z v hL hz s).symm.toMonoidHom.toAdditive }
  obtain ⟨f, c, e, hf, hrange, _, he⟩ := m.exists_full_model eC hquot hcore
  refine ⟨{ embedding := f, injective := hf, coordinates := E.trans e,
    conjugation := ?_ }, hrange⟩
  intro g u
  change ((E.symm (e.symm (Hexacode.action (f (plusMk K L T z v hL hz g))
    (e (E u))))).toMul : G) = _
  rw [← he, e.symm_apply_apply]
  change (((s.space.toRepresentation (plusMk K L T z v hL hz g) (E u)).val).toMul : G) = _
  exact wkRepresentation_apply K L T z v hL hz g (E u).val

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
