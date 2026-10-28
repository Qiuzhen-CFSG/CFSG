module

public import CFSG.Quasithin.ChapterJ.Section04To05.SourceAmalgam.FirstOvergroup
public import CFSG.Quasithin.ChapterJ.Section03.Quasithin

/-!
# Quasithinness for the actual J.4 source amalgam

The original TypeRu hypotheses give the full J.3 order and extraspecial
Sylow subgroups at three and five, hence quasithinness of every subgroup.
Applying this to the literal generated source group discharges the remaining
ambient rank hypothesis of F.1.12 alongside the constructed F.1.1 local data.
The specialized endpoint recognition is still a separate source theorem.

Source: Aschbacher–Smith J.3.1, J.3.6 and J.4.5, printed pp.438–442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G]

/-- Every literal generated source group satisfies the quasithin hypothesis. -/
theorem Plane.F_quasithin (h : IsTypeRu G) {d : LocalSetup G} (p : Plane d)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic) :
    IsQuasithin (p.F B5 X) := Section03.quasithin_subgroup_of_typeRu h _

/-- All genuine local and rank inputs for the binary Ree F.1.12 branch are
constructed from the original TypeRu hypothesis on the unchanged ambient group. -/
theorem source_quasithin_amalgam_of_typeRu (h : IsTypeRu G) :
    ∃ (d : LocalSetup G) (p : Plane d) (s : SourceChoice p)
      (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic),
      (∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹) ∧
      p.F₂ B5 X ⊔ d.toTypeRuSetup.S = p.parabolic ∧
      ChapterF.Source.BinaryRee.LocalData (p.F₁ B5) (p.T_F B5) (p.F₂ B5 X) ∧
      IsQuasithin (p.F B5 X) ∧
      centralizer (p.F B5 X : Set G) ≤ p.F B5 X ∧
      (p.F₁ B5).relIndex (p.F₁ B5 ⊔ d.toTypeRuSetup.Q) = 2 := by
  obtain ⟨d,p,s,B5,X,hi,hgen,hl⟩ := source_local_of_typeRu h
  exact ⟨d,p,s,B5,X,hi,hgen,hl,p.F_quasithin h B5 X,p.centralizer_F_le B5 X,
    s.F₁_relIndex_sup_Q p B5 hi⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
