module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Contracts
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.NaturalOffenders.Transport
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.NaturalOffenders.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.SevenNatural
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo.PolarComparison

/-!
# The natural alternating branches of K.1

The supplied natural-action recognition identifies either the whole component
or its full symmetric extension. For A₆ the B.3 offender calculation gives
generation, ratio one, and the rank-two conjugacy description under that same
identification. For S₆ the polar-coordinate equivalence identifies the actual
four-space action with Sp₄(2), marking A₆ as its commutator subgroup. For S₇
we transport the full disjoint-transposition offender family and ratio one.
The inner A₇ case uses the already proved quadratic and cubic ratios 3/2.

The endpoints use only `NaturalAction`, so apply in particular to every finite,
finite-dimensional source `Input`. The independent recognition owner supplies
this input to the final K.1 assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.1–K.1.2,
printed p.452, citing B.3.2, B.3.4 and the alternatives of B.4.2.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource ChapterB.Offenders NaturalOffenders
open Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The same S₆ polar isomorphism intertwines the natural module and sends the
marked component to the actual derived subgroup of Sp₄(2). -/
noncomputable def sixSymplecticMarking
    (e : MarkedActionEquiv ρ ⊤ L (naturalRepresentation (Fin 6))
      (alternatingGroup (Fin 6))) :
    MarkedActionEquiv ρ ⊤ L (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) where
  action := {
    groupEquiv := e.action.groupEquiv.trans symmetricSymplecticEquiv
    linearEquiv := e.action.linearEquiv.trans naturalLinearEquiv
    intertwines := by
      intro g v
      exact (congrArg naturalLinearEquiv (e.action.intertwines g v)).trans
        (naturalLinearEquiv_equivariant _ _) }
  contained := le_top
  subgroupEquiv := e.subgroupEquiv.trans alternatingDerivedEquiv
  compatible := by
    intro l
    change symmetricSymplecticEquiv (e.action.groupEquiv ⟨l.val, _⟩) =
      (alternatingDerivedEquiv (e.subgroupEquiv l)).val
    rw [e.compatible]
    rfl

/-- Inner A₆: generation, ratio one, and conjugacy by an actual even permutation
under the supplied natural identification. -/
theorem sixNatural_inner_conclusion (hL : L = ⊤) (a : NaturalAction ρ L 6) :
    Conclusion ρ L := by
  have hgen := generated_eq_top (wholeAction hL a.restricted) sixNatural_generated
  refine .ff (.six a) (.alternatingSix (hgen.trans hL.symm) a.restricted ?_ ?_)
  · intro A hA
    have hAL : A ≤ L := hL.symm ▸ le_top
    have hb := best_map a.restricted (hA.subgroupOf ρ hAL)
    refine ⟨?_, ?_⟩
    · have hd := (six_best_dimensions hb).1
      rwa [rank_map_injective _ a.restricted.groupEquiv.injective,
        rank_subgroupOf hAL] at hd
    · simpa only [Subgroup.map_map] using even_conjugator (six_best_conjugate hb)
  · exact (quadraticRatio_eq (wholeAction hL a.restricted)).trans sixNatural_ratio

/-- Outer S₆: the marked symplectic alternative, with its generated subgroup
and ratio 2/3 discharged on the original action. -/
theorem sixNatural_outer_conclusion (a : NaturalAction ρ L 6)
    (e : MarkedActionEquiv ρ ⊤ L (naturalRepresentation (Fin 6))
      (alternatingGroup (Fin 6))) : Conclusion ρ L := by
  have hgen := generated_eq_top (wholeAction rfl e.action) sixSymmetric_generated
  refine .ff (.six a) ?_
  rw [hgen]
  exact .symplecticTwo (sixSymplecticMarking e)
    ((quadraticRatio_eq (wholeAction rfl e.action)).trans Six.quadraticRatio_natural)

/-- Outer S₇: the complete symmetric alternative, including its actual
best-offender family, generated subgroup and ratio one. -/
theorem sevenNatural_outer_conclusion (a : NaturalAction ρ L 7)
    (e : MarkedActionEquiv ρ ⊤ L (naturalRepresentation (Fin 7))
      (alternatingGroup (Fin 7))) : Conclusion ρ L := by
  have hgen := generated_eq_top (wholeAction rfl e.action) sevenSymmetric_generated
  refine .ff (.sevenNatural a) ?_
  rw [hgen]
  refine .symmetric 7 (Or.inr rfl) e ?_ ?_
  · intro A hA
    exact (Odd.isBestOffender_natural_iff_caseAFamily (Or.inr rfl) _).mp
      (best_map e.action (hA.subgroupOf ρ le_top))
  · exact (quadraticRatio_eq (wholeAction rfl e.action)).trans
      (Odd.quadraticRatios (Or.inr rfl : 7 = 5 ∨ 7 = 7)).2.2.2

/-- The complete K.1 natural-A₆ conclusion from natural-action recognition. -/
theorem sixNatural_conclusion (a : NaturalAction ρ L 6) : Conclusion ρ L :=
  a.extension.elim (fun hL => sixNatural_inner_conclusion hL a)
    (fun he => he.elim (fun e => sixNatural_outer_conclusion a e))

/-- The complete K.1 natural-A₇ conclusion, including both permitted actors. -/
theorem sevenNaturalAction_conclusion (a : NaturalAction ρ L 7) : Conclusion ρ L :=
  a.extension.elim (fun hL => sevenNatural_conclusion hL a.restricted)
    (fun he => he.elim (fun e => sevenNatural_outer_conclusion a e))

end CFSG.Quasithin.ChapterK.Alternating
