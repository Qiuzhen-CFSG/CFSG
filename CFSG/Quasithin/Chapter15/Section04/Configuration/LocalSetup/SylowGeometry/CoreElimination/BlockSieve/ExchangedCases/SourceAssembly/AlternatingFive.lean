module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.AlternatingFiveSeed
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.RankOneGeometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Local
/-!
# The symmetric-five B.5 row contradicts the actual local seed

Restricting the prescribed Sylow to D=LR gives the exact centralizer of the
original seed in D. The local module comparison places that seed in Ω₁Z(O₂D).
The literal B.5 moved quotient with its natural A₅ action then supplies the
cubic fixed-space enlargement excluded by this seed centralizer. No block
recognition, C.2.7 classification, or ambient-core quotient inclusion is used.
Source: Aschbacher–Smith C.2.7(3) and 15.4.20, printed pp.145–147 and1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

theorem source_alternatingFive_row_contradiction
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H))
    (c : StarSourceConclusion (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))
    (e : ActionEquiv (c.sectionData.action.comp
      ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H)
          ((sourceRadical d U).subgroupOf H)))).subtype) (alternatingNatural 5)) : False := by
  let L := K₁.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let Z := d.Z.subgroupOf H
  have hr := source_local_radical h s hn
  have hcomp := h.local_module_comparison L hn hr
  have hZV : Z.subgroupOf D ≤ omegaCoreModule D := by
    have hNC : normalClosure (Z.subgroupOf D : Set D) ≤ omegaCoreModule D := by
      apply (map_le_map_iff_of_injective D.subtype_injective).mp
      rw [hcomp.1]
      exact hcomp.2.2.1
    exact (show Z.subgroupOf D ≤ normalClosure (Z.subgroupOf D : Set D) from
      fun _ hz => le_normalClosure hz).trans hNC
  obtain ⟨P,hP⟩ := SL3Geometry.source_local_sylow h s hn
  have hZD : Z ≤ D := (show Z ≤ R from fun _ hz => h.seed_le_radical hz).trans le_sup_right
  have hCZ : centralizer (Z.subgroupOf D : Set D) = (P : Subgroup D) := by
    apply map_injective D.subtype_injective
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hZD,h.seed_inputs.2.2.1,hP,inf_comm]
  exact not_alternatingFive_movedSection_of_seed
    (omegaCoreModule D) (Z.subgroupOf D) (starProjection L R)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hZV P hCZ (offenderSubgroup (starRepresentation L R)) (starComponent L R)
    c.sectionData e

/-- Literal application to the marked symmetric-five row of the original B.5 conclusion. -/
theorem source_symmetricFive_row_contradiction
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H))
    (c : StarSourceConclusion (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))
    (e : MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H)
          ((sourceRadical d U).subgroupOf H))))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) : False := by
  exact source_alternatingFive_row_contradiction h s hn c
    (ExtensionConsequences.markedRestriction e)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
