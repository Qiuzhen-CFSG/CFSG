module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Contracts
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DisplacementZero
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.LocalReduction.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Source
public import Theory.GroupTheory.PCoreRestriction

/-!
# Assembly of the natural small-corank contradiction

The terminal TI pair is contained in the centralizer of its actual diagonal
involution: one factor lies in V and the other in Vᵍ. The 10.2.11 input puts
V in the two-core of that centralizer. Restricting this normal two-subgroup
to the TI pair contradicts the first factor's escape from its own two-core.
All containments use the original subgroups and embedded two-cores.

The local reduction is proved from the earlier half-Sylow uniqueness input.
The diagonal-core theorem and terminal construction remain explicit source
inputs. This conditional assembly does not prove NaturalSmallCorankExclusionAt
until the remaining inputs are discharged.
Source: Aschbacher--Smith 10.2.12, last paragraph on printed p.755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

/-- The constructed diagonal and TI pair contradict the literal 10.2.11
two-core containment. No ambient normality of the TI pair is assumed. -/
theorem TerminalWitness.false_of_diagonal_core
    (w : TerminalWitness T D g) (c : Configuration T D g)
    (m : SourceLinearThreeGeometry T D) (hcore : DiagonalCoreAt T)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆) : False := by
  let V := D.fullModule
  let W := ⁅D.fullModule,L⁆
  let C := centralizer ({w.first * w.second} : Set G)
  let I := W ⊔ W.map (MulAut.conj w.conjugator).toMonoidHom
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hpartner : W.map (MulAut.conj w.exchange).toMonoidHom ≤ V := by
    exact (map_mono hWV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T w.exchange_mem)))
  have hzV : w.first * w.second ∈ V := V.mul_mem (hWV w.first_mem)
    (hpartner w.second_mem)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  have hVC : V ≤ C := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (V.le_centralizer hzV v hv)
  have hconj : W.map (MulAut.conj w.conjugator).toMonoidHom ≤
      V.map (MulAut.conj (w.align * g)).toMonoidHom := by
    rcases w.conjugator_eq with he | he
    · rw [he]
      exact map_mono hWV
    · rw [he]
      have hc : (MulAut.conj ((w.align * g) * w.exchange)).toMonoidHom =
          (MulAut.conj (w.align * g)).toMonoidHom.comp
            (MulAut.conj w.exchange).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply,mul_assoc]
      rw [hc,←map_map]
      exact map_mono hpartner
  have hIC : I ≤ C := sup_le (hWV.trans hVC)
    (hconj.trans w.conjugate_centralizes)
  have hVcore : V ≤ C.pCoreIn 2 := hcore c.many L D m c.nonnormal
    c.pointCentralizers hz hti w.exchange w.exchange_mem w.exchange_moves
    w.first w.second w.first_mem w.second_mem w.first_ne w.second_ne
    w.first_fixed w.second_fixed w.central w.order
  exact w.core_escape ((le_inf (le_sup_left : W ≤ I) (hWV.trans hVcore)).trans
    (inf_pCoreIn_le_of_le 2 hIC))

/-- The exact published exclusion follows once the three independent
source arguments are proved. Final discharge remains with this task. -/
theorem naturalSmallCorankExclusion_of_source_steps
    (hlocal : LocalReductionAt T) (hcore : DiagonalCoreAt T)
    (hterminal : TerminalConstructionAt T) : NaturalSmallCorankExclusionAt T := by
  intro L D g c m hsmall
  obtain ⟨hone,hz,hti⟩ := hlocal L D g c m hsmall
  obtain ⟨w⟩ := hterminal L D g c m hone hz hti
  exact w.false_of_diagonal_core c m hcore hz hti

/-- Application to the published small-offender consumer. Recognition is
independent; all three remaining natural source steps stay explicit. -/
theorem nonnormalSmallOffender_of_recognition_and_natural_steps
    (hrecognition : RecognitionAt T) (hlocal : LocalReductionAt T)
    (hcore : DiagonalCoreAt T) (hterminal : TerminalConstructionAt T) :
    SourceNonnormalSmallOffenderAt T :=
  source_nonnormalSmallOffender_of_source_steps hrecognition
    (naturalSmallCorankExclusion_of_source_steps hlocal hcore hterminal)

/-- The proved local reduction removes its former callback. The earlier
half-Sylow uniqueness theorem remains with the point-control owner; diagonal
core control and the terminal TI construction remain with this task. -/
theorem naturalSmallCorankExclusion_of_halfSylow_core_terminal
    (hhalf : PointControl.HalfSylowUniqueAt T) (hcore : DiagonalCoreAt T)
    (hterminal : TerminalConstructionAt T) : NaturalSmallCorankExclusionAt T :=
  naturalSmallCorankExclusion_of_source_steps
    (localReduction_of_halfSylowUnique hhalf) hcore hterminal

/-- Actual application of the completed local reduction to the published
small-offender contract, retaining precisely its earlier and terminal inputs. -/
theorem nonnormalSmallOffender_of_recognition_halfSylow_core_terminal
    (hrecognition : RecognitionAt T) (hhalf : PointControl.HalfSylowUniqueAt T)
    (hcore : DiagonalCoreAt T) (hterminal : TerminalConstructionAt T) :
    SourceNonnormalSmallOffenderAt T :=
  source_nonnormalSmallOffender_of_source_steps hrecognition
    (naturalSmallCorankExclusion_of_halfSylow_core_terminal hhalf hcore hterminal)

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
