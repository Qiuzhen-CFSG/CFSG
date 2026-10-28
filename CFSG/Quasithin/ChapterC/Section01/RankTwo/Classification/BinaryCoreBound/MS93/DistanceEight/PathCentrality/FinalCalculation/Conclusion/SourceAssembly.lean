module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.OriginalSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.RadiusImage

/-!
# The concluding MS93 (4.4) calculation from the earlier source controls

The selected-pair construction and its two nontrivial commutators supply the
terminal product. The symmetric calculation, the genuine (4.2)(i) transfer
and the b>8 contradiction give distance eight, centrality in the whole local
stabilizer and both edge indices. `ProductSource.OriginalSource.conclusions`
already exposes precisely this implication with the full (4.4.5) natural
sections as input; it is publicly reexported here without any product premise.

The numerical application below uses the same product bounds and the actual
alpha-2 moving neighbor of the extended path. The remaining applications
construct the full natural sections by `RadiusImage.natural_section`, including
its b=8 boundary case, and feed them to the concluding calculation.

Only the earlier-source controls remain explicit: (4.4.1) local commutator
control, (4.4.4) prescribed replacement on regular paths, the critical-prefix
nonnatural exclusion, and the correctly marked extended path. LocalCommutator
and RegularPaths retain their construction; the PathCentrality assembly owner
discharges these inputs. In particular, full local commutator control is still
used for the oppositely ordered span in the selected Ri fixed-core estimate
and for RadiusImage's boundary calculation. This is a conditional concluding
family, not an unconditional proof of (4.4) from the original MS input.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), printed pp.894--895, (4.4.5) and the conclusion of (4.4).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SourceAssembly
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The numerical consumer at any M-vertex, using only the preceding full
natural sections and the source product construction. No first-edge identity,
distance-eight conclusion or centrality premise is required. -/
theorem H_card_le_four_of_sections (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) : Nat.card (H R c) ≤ 4 :=
  ProductEstimates.H_card_le_four common hb sections e
    (ProductSource.OriginalSource.terminalProduct_card common hb hlocal replacement sections e)
    (ProductSource.OriginalSource.terminalProduct_le_fixed hb hlocal e) hc

/-- The literal alpha application, even when the given extended path is
centered elsewhere; the moving neighbor and natural action are transported. -/
theorem H_alpha_card_le_four_of_sections (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Nat.card (H R (alpha R)) ≤ 4 :=
  H_card_le_four_of_sections common hb hlocal replacement sections e rfl

/-- All concluding (4.4) outputs after supplying (4.4.5) from the actual
radius-image calculation and critical-prefix exclusion. The selected pair,
its product, moving-edge fixation and natural sections are all constructed. -/
theorem conclusions (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    geometry.b R = 8 ∧
      (∀ c, color R c = false → ⁅V R c, Q R c⁆ ≤
        (center (stabilizer R c)).map (stabilizer R c).subtype) ∧
      (∀ c t, color R c = false → Adjacent R c t →
        (Z R t).relIndex (Z R c) = 2 ∧ (Q R c).relIndex (Q R t) = 4) :=
  ProductSource.OriginalSource.conclusions common hb hlocal replacement
    (fun _ hc => RadiusImage.natural_section common hb hlocal exclude e hc) e

/-- The distinguished edge application with the source Z-index and Q-index,
and centrality in the actual alpha stabilizer. -/
theorem alpha_beta (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    geometry.b R = 8 ∧
      ⁅V R (alpha R), Q R (alpha R)⁆ ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype ∧
      (Z R (beta R)).relIndex (Z R (alpha R)) = 2 ∧
      (Q R (alpha R)).relIndex (Q R (beta R)) = 4 := by
  obtain ⟨hd, hc, hi⟩ := conclusions common hb hlocal replacement exclude e
  exact ⟨hd, hc _ rfl, hi _ _ rfl (base_adjacent R)⟩

/-- Discharge the natural-section premise in the numerical application using
the same (4.4.5) calculation. The genuine earlier controls remain explicit. -/
theorem H_alpha_card_le_four (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Nat.card (H R (alpha R)) ≤ 4 :=
  H_alpha_card_le_four_of_sections common hb hlocal replacement
    (fun _ hc => RadiusImage.natural_section common hb hlocal exclude e hc) e

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SourceAssembly
