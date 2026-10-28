module

public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicGeneration.SecondPoint
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicCentralizers

/-!
# The original source actors force the core centralizer to vanish

If a subgroup N of Q is normalized by B₅ and a supplement J to S in G₂,
then it meets the centralizer of any subgroup containing Q₅ trivially.
A nontrivial intersection first puts Z into N; the two native generation
steps then put the selected escaping element into N, contradicting N≤Q.
Applied to the normal two-core of F, the p-group fixed-point theorem supplies
exactly the nontrivial intersection excluded here.

Source: Aschbacher–Smith, J.4.5(1), printed p.442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- Literal source core-centralizer obstruction, with the unchanged B₅ and choice. -/
theorem SourceChoice.core_centralizer_eq_bot (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (J N T : Subgroup G)
    (hJS : J ⊔ d.toTypeRuSetup.S = p.parabolic)
    (hNQ : N ≤ d.toTypeRuSetup.Q) (hJ : J ≤ normalizer (N : Set G))
    (hB : Centralizers.Choices.B5Image B5 ≤ normalizer (N : Set G))
    (hfive : Q₅ d B5 ≤ T) :
    N ⊓ centralizer (T : Set G) = ⊥ := by
  by_contra h
  exact s.not_point_le_of_supplement_normalized B5 J N hJS hNQ hJ hB
    (Z_le_of_nontrivial_centralizer d B5 hfive h)

end CFSG.Quasithin.ChapterJ.RuSubgroup
