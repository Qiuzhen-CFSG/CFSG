module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.Preparation
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# The literal radical quotient and A₆ Sylow action

The quotient equivalence from the component lift is composed with the supplied
A₆ image marking. Its kernel is precisely the radical, and conjugation by the
original Sylow is transported through this same map. The natural-action
condition means membership in the natural S₆ subgroup of Aut(A₆), retaining
outer transpositions. It asserts neither that the action is inner nor that the
radical is the two-core.

These are interfaces for the source recovery, not proofs of G.11.2(2),(10).
Source: Aschbacher--Smith G.11.2 and 14.3.15, printed pp.364--367,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}

@[expose] def ComponentLift.alternatingSixRadicalEquiv (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) :
    (K ⧸ solvableRadical K) ≃* alternatingGroup (Fin 6) :=
  (hK.radicalQuotientEquiv (Or.inr ⟨e6⟩)).trans e6

@[expose] def ComponentLift.alternatingSixMap (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) : K →* alternatingGroup (Fin 6) :=
  (hK.alternatingSixRadicalEquiv e6).toMonoidHom.comp (QuotientGroup.mk' (solvableRadical K))

theorem ComponentLift.alternatingSixMap_surjective (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) :
    Function.Surjective (hK.alternatingSixMap e6) :=
  (hK.alternatingSixRadicalEquiv e6).surjective.comp (QuotientGroup.mk'_surjective _)

theorem ComponentLift.alternatingSixMap_ker (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) :
    (hK.alternatingSixMap e6).ker = solvableRadical K := by
  ext k
  change hK.alternatingSixRadicalEquiv e6 (QuotientGroup.mk k) = 1 ↔ k ∈ solvableRadical K
  rw [MulEquiv.map_eq_one_iff,QuotientGroup.eq_one_iff]

/-- Conjugation on the literal radical quotient, in the supplied A₆ coordinates. -/
@[expose] def ComponentLift.alternatingSixAction (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) : T →* MulAut (alternatingGroup (Fin 6)) :=
  (MulAut.congr (hK.alternatingSixRadicalEquiv e6)).toMonoidHom.comp
    (((solvableRadical K).quotientAut.comp K.normalizerMonoidHom).comp (inclusion hn))

theorem ComponentLift.alternatingSixAction_equivariant (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) (t : T) (k : K) :
    hK.alternatingSixAction e6 hn t (hK.alternatingSixMap e6 k) =
      hK.alternatingSixMap e6 (K.normalizerMonoidHom ⟨t,hn t.property⟩ k) := by
  dsimp only [ComponentLift.alternatingSixAction,ComponentLift.alternatingSixMap,
    MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
  simp only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,quotientAut_apply_mk]
  rfl

/-- The action condition in 14.3.15. Natural S₆ automorphisms are permitted,
including outer transpositions. This record supplies no kernel equality. -/
structure ComponentLift.AlternatingSixNaturalAction (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) : Prop where
  normalizes : (T : Subgroup G) ≤ normalizer (K : Set G)
  natural_action : ∀ t : T, hK.alternatingSixAction e6 normalizes t ∈ AlternatingSix.ShadowLocal.natural

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
