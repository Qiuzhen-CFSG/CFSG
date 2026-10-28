module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LocalGeneration
public import Theory.GroupTheory.SylowCenterFixedSpan
public import Theory.Representation.RankOne.QuadraticRecognition.Generation

/-!
# Fixed generation on the literal noncommuting center section

The odd-index local actor contains every Sylow two-subgroup of its vertex
stabilizer. A common Sylow and Sylow conjugacy identify their actual center
spans. Thus every specified conjugation section of the original Z is generated
by fixed vectors for the image of any local Sylow, through the same quotient
map. This supplies the corrected generation premise in the recognition proof.

Source: DGS, *Groups and Graphs* (1985), notation p.81, (6.0)--(6.1),
pp.118--119, and (7.1), pp.126--127; Stroth's correction to (5.12).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

/-- Passing to the actual local actor preserves the original center span. -/
theorem local_center_span (P E : Subgroup G) (c : LocalRankOneData P E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex P) :
    sylowCenterSpan P = sylowCenterSpan c.Pstar := by
  let := c.finite_P
  have hLP : c.Pstar ≤ P := le_sup_left.trans c.supplement.le
  let : Finite c.Pstar := Finite.of_injective (inclusion hLP) (inclusion_injective _)
  have hT (T : Sylow 2 P) : (T : Subgroup P).map P.subtype ≤ c.Pstar :=
    local_twoGroup_le_star c hodd _ (T.isPGroup'.map _) (map_subtype_le _)
  obtain ⟨T,hTmap⟩ := sylow_in_overgroup_of_odd_relIndex P c.Pstar
    ((c.sylow : Subgroup c.Pstar).map c.Pstar.subtype) hLP ⟨c.sylow,rfl⟩ hodd
  rw [sylowCenterSpan_eq_conjugateSpan P c.Pstar hLP hT T,hTmap]
  exact (sylowCenterSpan_eq_conjugateSpan c.Pstar c.Pstar le_rfl
    (fun _ => map_subtype_le _) c.sylow).symm

/-- Fixed-space generation for the same marked center quotient used in (7.1). -/
theorem local_section_generated (P E : Subgroup G) (c : LocalRankOneData P E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex P)
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (π : c.Pstar →* D)
    (d : BinaryConjugationSection c.Pstar (sylowCenterSpan P)
      (Stellmacher.omegaOneCenterAmbient c.Pstar) (σ.comp π)) (T : Sylow 2 c.Pstar) :
    GeneratedByFixedSpace σ ((T : Subgroup c.Pstar).map π) := by
  let := c.finite_P
  let : Finite c.Pstar := Finite.of_injective
    (inclusion (le_sup_left.trans c.supplement.le)) (inclusion_injective _)
  apply sylow_span_fixedSpace_generated c.Pstar _ _ σ π d T
  exact local_center_span P E c hodd

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
