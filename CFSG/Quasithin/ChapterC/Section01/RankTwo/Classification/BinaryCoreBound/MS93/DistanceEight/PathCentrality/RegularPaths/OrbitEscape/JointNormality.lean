module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Reduction

/-!
# Conditional assembly of joint normality in MS93 (4.4.2)

The subgroup and counting arguments are complete. The source selection of two
separating edge conjugates and the applications of (4.4.1) remain explicit
inputs to the theorem below. This is not yet joint normality from LocalSource,
CommonFacts, b > 4, local commutator control and failed orbit escape alone.
The assembly owner must discharge each extra premise before exporting that
source theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.2), first paragraph on
printed p.893. Normality is relative to the start stabilizer.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality
open NormalizerTransfer
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Conditional assembly of the first subgroup argument in (4.4.2).
The selection and three applications of (4.4.1) remain explicit. -/
theorem jointSpan_normalized_of_source_steps [Finite M]
    {source : LocalSource L R} (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hreverse : ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
      Q R (p.walk.getVert (p.walk.length - 4)))
    (hselect : SeparatingConjugates p) (hcontained : ContainedDisplacementBound p)
    (hedge : EdgeDisplacementBound p)
    (hexclude : ¬ ⁅Z R a, Z R a'⁆ ≤ U R (p.walk.getVert (p.walk.length - 2))) :
    stabilizer R a ≤ normalizer (jointSpan p) := by
  by_contra hn
  obtain ⟨g, hg, h, hh, hgen, hgen', hsep⟩ := hselect
  have hHg := displacement_ne_bot_of_not_normalized common p hb hreverse hg hgen
    (hcontained g hg hgen) hn
  have hHh := displacement_ne_bot_of_not_normalized common p hb hreverse hh hgen'
    (hcontained h hh hgen') hn
  have hfill := displacements_sup_eq_natural_centralizer common p hb hreverse hg hh hHg hHh
    (hedge g hg hgen hHg) (hedge h hh hgen' hHh) hsep
  apply hexclude
  exact ((critical_le_natural_centralizer common p).trans_eq hfill.symm).trans
    (sup_le (displacement_le_terminal_natural source p hb hreverse hg)
      (displacement_le_terminal_natural source p hb hreverse hh))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality
