module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Assembly

/-!
# The complete local calculations for MS93 (4.5.5)

The source critical window at positions two through ten is transported by
an actual conjugator. Extending that window preserves its midpoint and its
forward vertices, so the full second quotient supplies the neighboring
marked section on precisely the subgroups used by the two Z-cases.

The first and second marked sections and all preceding path calculations
are now constructed from CommonFacts and genuine Earlier. They give both
the conjugate-pair bound and the noncentral seed calculation, and hence
the Q-commutator and derived-group equalities modulo Z on the original
path. No moving quotient or final core-center assertion is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii),(v) and (4.5.5),
printed pp.898--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Source
open NormalizerTransfer PathCentrality RegularPaths TwoCases
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The neighboring second quotient, pulled back along the given conjugator. -/
theorem neighbor_pair (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (k : FreeAmalgam R) (hk : act R k (alpha R) = p.walk.getVert 6) :
    Nonempty (MarkedPairSection source common
      (rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) k⁻¹)
      (rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) k⁻¹) true) := by
  let v := Early.PathExtension.sourceWindow earlier.distance p 2 (by decide) (by decide)
  have hv := Early.PathExtension.sourceWindow_regular earlier.distance p 2 (by decide) (by decide)
  have hback : act R k⁻¹ (p.walk.getVert 6) = alpha R := by
    rw [← hk, ← act_mul, mul_inv_cancel, act_one]
  have hm : (v.act k⁻¹).walk.getVert 4 = alpha R := by
    change (actWalk R k⁻¹ v.walk).getVert 4 = _
    rw [actWalk_getVert]
    rw [Early.PathExtension.sourceWindow_getVert earlier.distance p 2 (by decide) (by decide) 4 (by decide)]
    exact hback
  obtain ⟨⟨q,hq⟩⟩ := Replacement.Regularity.sourcePath_preserving_start_window
    common earlier (v.act k⁻¹) (hasTurnConjugators_act v hv k⁻¹)
  have hmodel : ∀ w : Early.SourcePath R ((v.act k⁻¹).walk.getVert 4),
      Nonempty (MarkedPairSection source common
        (hatW R ((v.act k⁻¹).walk.getVert 4) (w.walk.getVert 6) (w.walk.getVert 8))
        (hatV R ((v.act k⁻¹).walk.getVert 4) (w.walk.getVert 6)) true) := by
    rw [hm]
    exact Quotients.SecondLayer.OrbitSource.marked_pair common earlier
  have h6 : q.walk.getVert 6 = act R k⁻¹ (p.walk.getVert 8) := by
    rw [hq 6 (by decide)]
    change (actWalk R k⁻¹ v.walk).getVert 6 = _
    rw [actWalk_getVert, Early.PathExtension.sourceWindow_getVert]
    decide
  have h8 : q.walk.getVert 8 = act R k⁻¹ (p.walk.getVert 10) := by
    rw [hq 8 (by decide)]
    change (actWalk R k⁻¹ v.walk).getVert 8 = _
    rw [actWalk_getVert, Early.PathExtension.sourceWindow_getVert]
    decide
  simpa only [rightConjugate_hatW, rightConjugate_hatV, hback, h6, h8, hm]
    using hmodel q


/-- Both source local calculations on the original path, with all inputs discharged. -/
theorem local_calculations (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (∀ g : stabilizer R (alpha R),
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
          hatV R (alpha R) (p.walk.getVert 6)) ∧
    ¬ ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ≤
        Z R (alpha R) := by
  obtain ⟨k,hk⟩ := exists_mVertex_of_color R (p.even_color (i := 6) (by decide) (by decide))
  have hk' : act R k (alpha R) = p.walk.getVert 6 := by
    rw [hk]
    change mVertex R (1 * k) = mVertex R k
    rw [one_mul]
  obtain ⟨first⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  obtain ⟨second⟩ := Quotients.SecondLayer.OrbitSource.marked_pair common earlier p
  obtain ⟨neighbor⟩ := neighbor_pair common earlier p k hk'
  let h := Early.Orbit.Source.HatIdentity.SmallSeed.identitiesOnPath common earlier p
  have f := Early.firstFactsOnPath source common earlier p
  apply TwoCases.local_calculations source common earlier
    (Early.Orbit.SourceApplications.higherPath geometry p) first second k hk' neighbor
    h.center (h.forward 6 (by decide) (by decide) (by decide))
    (h.forward 8 (by decide) (by decide) (by decide))
  · simpa only [p.center_eq] using
      (f.forward 4 (by decide) (by decide) (by decide)).H_card
  · exact (Early.Orbit.Source.HatCommutators.first_bounds_of_identity common earlier p h
      (i := 6) (by decide) (by decide) (by decide)).1
  · convert (f.forward 2 (by decide) (by decide) (by decide)).hatW_product using 1 <;>
      simp only [Early.Orbit.SourceApplications.higherPath, Nat.reduceAdd, p.center_eq]
  · convert (f.forward 4 (by decide) (by decide) (by decide)).hatW_product using 1 <;>
      simp only [Early.Orbit.SourceApplications.higherPath, Nat.reduceAdd, p.center_eq]
  · exact Early.Orbit.Source.HatCommutators.forward_second_bound_of_identity
      common earlier p h (i := 6) (by decide) (by decide) (by decide)

/-- The literal third-layer commutator with the original Q lies in the first hat. -/
theorem Q_commutator_le (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (alpha R)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6) := by
  let h := Early.Orbit.Source.HatIdentity.SmallSeed.identitiesOnPath common earlier p
  have f := Early.firstFactsOnPath source common earlier p
  apply SourcePath.Q_commutator_le_of_conjugate_bounds
    (Early.Orbit.SourceApplications.higherPath geometry p) earlier h.center
    (h.forward 8 (by decide) (by decide) (by decide))
  · convert (f.forward 2 (by decide) (by decide) (by decide)).hatW_product using 1 <;>
      simp only [Early.Orbit.SourceApplications.higherPath, Nat.reduceAdd, p.center_eq]
  · convert (f.forward 4 (by decide) (by decide) (by decide)).hatW_product using 1 <;>
      simp only [Early.Orbit.SourceApplications.higherPath, Nat.reduceAdd, p.center_eq]
  · exact Early.Orbit.Source.HatCommutators.forward_second_bound_of_identity
      common earlier p h (i := 6) (by decide) (by decide) (by decide)
  · exact (local_calculations common earlier p).1

/-- Both equalities of MS93 (4.5.5), conditional only on genuine Earlier. -/
theorem commutator_layers (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (alpha R)⁆ ⊔ Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) ∧
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ⊔
        Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) := by
  obtain ⟨first⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  obtain ⟨hpairs,hnon⟩ := local_calculations common earlier p
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  exact Higher.commutator_layers_of_local_bounds source common earlier
    q.two_step_distances.1.le q.two_step_distances.2.1.le q.two_step_distances.2.2.le first hpairs
    (Q_commutator_le common earlier p) hnon

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Source
