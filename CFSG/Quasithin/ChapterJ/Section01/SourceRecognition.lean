module

public import CFSG.Quasithin.ChapterJ.Section04To05.SourceAmalgam.Recognition.Rudvalis
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Placement.Complete

/-!
# Recognition of the original Type-Ru group

The original source hypotheses construct the marked local amalgam inside its
literal generated subgroup. The six-parabolic graph and actual commutator
actor place the fixed five-subgroup in the fourth point stabilizer. This gives
Small and the marked full binary Ree subgroup, then the original rank-three
action identifies the ambient group with the concrete Rudvalis carrier.

No local marking, placement, graph, or recognition hypothesis remains.
Source: Aschbacher–Smith Theorem J.1.1 and J.4.7–J.5.14, printed pp.431–455.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open RuSubgroup
open RuSubgroup.FiveHexagon.ParabolicFamily

/-- Theorem J.1.1 on the original Type-Ru hypotheses and the concrete Ru carrier. -/
theorem theorem_J_1_1 {G:Type*} [Group G] [Finite G] (h:IsTypeRu G) :
    Nonempty (G≃*Rudvalis.Model) := by
  obtain ⟨d,p,s,c,B5,X,q,e,e₂,hi,hm,hl,hr,hz,hfive,_,_⟩:=marked_completion_of_typeRu h
  have hplace:=Placement.source_fixedFive_placement q p s c B5 hi e
    (p.F B5 X).subtype (p.F B5 X).subtype_injective hl hz hfive
  exact s.rudvalis_of_fixedFive_placement c B5 hi X hm q e e₂ hl hr hz hfive hplace

end CFSG.Quasithin.ChapterJ
