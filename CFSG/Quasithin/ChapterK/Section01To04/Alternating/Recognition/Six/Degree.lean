module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.Reduction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.FlagModule
public import Theory.Representation.Quotient

/-!
# Assembly of the A₆ cubic degree calculation

A faithful binary A₆ action has degree at least four by the order-five
obstruction. The elementary-actor generation input bounds the original
ambient module by twelve. A composition series of the actual 45-point flag
module with simple factor degrees 1, 4 and 16 then forces degree four: every
irreducible binary A₆ module is a quotient of that flag module.

Both the group-generation witness and the concrete flag filtration remain
explicit proof obligations. This conditional assembly does not assert the
unconditional `sixDegree`. The numerical assertion of G.5.1 is owned by the
existing G.5 development; no four-space recognition or normalizer premise is
used here.

Source: Aschbacher–Smith G.5.1, printed pp.342–343, and K.1–K.1.1,
printed p.452 (PDF p.463), citing Guralnick–Malle (2002), Theorem 6.2 and
Table 6.3.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter
open SixDegreeReduction
universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}

omit [Finite G] in
/-- An actual faithful A₆ component already forces binary degree at least four. -/
theorem four_le_finrank_of_six_component (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 6)) : 4 ≤ Module.finrank (ZMod 2) V := by
  exact degree_ge_four ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)

/-- Apply a concrete binary flag filtration to the actual restricted action.
The pure group-generation premise still supplies the ambient degree estimate. -/
theorem finrank_eq_four_of_actorGeneration_and_filtration
    (hgen : ActorGeneration.{u})
    (hfiltration : FactorDegreeFiltration {d : ℕ | d = 1 ∨ d = 4 ∨ d = 16}
      flagRepresentation) (h : Input ρ K L) (e : L ≃* alternatingGroup (Fin 6)) :
    Module.finrank (ZMod 2) V = 4 := by
  let τ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hlo := four_le_finrank_of_six_component ρ h e
  have hdeg := BinaryPermutation.finrank_mem_of_factorDegreeFiltration
    flagAction ((1 : Theory.SpecificGroups.SymmetricSix.A6) : Flag)
    Theory.SpecificGroups.SymmetricSix.a6Borel
    Theory.SpecificGroups.SymmetricSix.a6BorelSylow.isPGroup'
    flag_stabilizer flag_transitive hfiltration τ
  have hhi := finrank_le_twelve_of_actorGeneration ρ hgen h e
  change Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 4 ∨
    Module.finrank (ZMod 2) V = 16 at hdeg
  omega

/-- Conditional assembly of the exact `Six.Degree` contract. The remaining
group and composition-series premises must both be discharged. -/
theorem sixDegree_of_actorGeneration_and_filtration
    (hgen : ActorGeneration.{u})
    (hfiltration : FactorDegreeFiltration {d : ℕ | d = 1 ∨ d = 4 ∨ d = 16}
      flagRepresentation) : RecognitionInputs.Six.Degree.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h e
  exact finrank_eq_four_of_actorGeneration_and_filtration ρ hgen hfiltration h e

end CFSG.Quasithin.ChapterK.Alternating
