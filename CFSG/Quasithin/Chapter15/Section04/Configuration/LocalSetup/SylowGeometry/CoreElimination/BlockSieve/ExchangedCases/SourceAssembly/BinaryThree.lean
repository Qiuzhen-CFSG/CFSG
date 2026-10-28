module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.BinaryThreeSeed
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.RankOneGeometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Local
/-!
# Direct exclusion of both binary SL₃ B.5 source rows

The original selected component and radical construct a local Sylow whose
centralizer is exactly the original seed. The seed lies in the actual
omega-core module. The point-radical cubic witness on the binary natural
module therefore excludes both the natural moved quotient and the doubled
natural moved space, using their same field and actor markings.
No universal C.1.34 theorem is an input to these local source contradictions.
Source: Aschbacher–Smith B.5.1 and15.4.20, pp.99 and1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

theorem source_local_seed_geometry
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H)) :
    let D := K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H
    let Z := (d.Z.subgroupOf H).subgroupOf D
    Z ≤ omegaCoreModule D ∧ ∃ P : Sylow 2 D,
      centralizer (Z : Set D) = (P : Subgroup D) := by
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
  exact ⟨hZV,P,hCZ⟩

theorem source_binaryThree_row_contradiction
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H))
    (c : StarSourceConclusion (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))
    (F : BinaryField) (hF : F.degree = 1)
    (e : ActionEquiv (c.sectionData.action.comp
      ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H)
          ((sourceRadical d U).subgroupOf H)))).subtype) (linearNatural F 3)) : False := by
  let L := K₁.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  obtain ⟨hZV,P,hCZ⟩ := source_local_seed_geometry h s hn
  exact not_binaryThree_movedSection_of_seed
    (omegaCoreModule D) ((d.Z.subgroupOf H).subgroupOf D) (starProjection L R)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hZV P hCZ (offenderSubgroup (starRepresentation L R)) (starComponent L R)
    c.sectionData F hF e

theorem source_doubleThree_row_contradiction
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H))
    (c : StarSourceConclusion (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))
    (F : BinaryField) (hF : F.degree = 1)
    (e : ActionEquiv (c.sectionData.space.toRepresentation.comp
      ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H)
          ((sourceRadical d U).subgroupOf H)))).subtype) (repeated (linearNatural F 3) 2)) : False := by
  let L := K₁.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  obtain ⟨hZV,P,hCZ⟩ := source_local_seed_geometry h s hn
  exact not_binaryThree_movedSpace_of_seed
    (omegaCoreModule D) ((d.Z.subgroupOf H).subgroupOf D) (starProjection L R)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hZV P hCZ (offenderSubgroup (starRepresentation L R)) (starComponent L R)
    c.sectionData F hF 2 e

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
