module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitPair
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalImage
public import Theory.GroupTheory.TransverseCommutatorIndex

/-!
# The strict index gain for paired critical orbits

The fixed subgroup modulo Zalpha contains both A intersect Qc and Zalpha.
Since Zalpha has image of order two modulo Qc, this improves the naive
centralizer index bound by a factor two. The opposite orbit is constructed
from the original Source, so the estimate has no extra second-local-group
hypothesis. This is the numerical comparison in MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem criticalOrbit_fixed_index_mul_two_le (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hcommB : ⁅Q R c,B⁆ ≤ Z R b) :
    2 * (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
      (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b) := by
  let A := criticalOrbit R c b
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  have hAQ : A ≤ Q R (alpha R) := (s.criticalOrbit_le_Q_iff hb hc b).mpr
    (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  have hAG : A ≤ stabilizer R (alpha R) := hAQ.trans (fun _ hx => hx.1)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite A := Finite.of_injective (inclusion hAG) (inclusion_injective _)
  have hZG : Z R b ≤ Z R (alpha R) := by
    simpa only [Z,show color R (alpha R) = false from rfl,
      DistanceTwo.NaturalCore.edge_color hab,Bool.true_eq_false,if_true,if_false]
      using (le_iSup_of_le b (le_iSup_of_le hab (le_refl (edgeOmega R b))) :
        edgeOmega R b ≤ ⨆ u,⨆ (_ : Adjacent R (alpha R) u),edgeOmega R u)
  have hAZ := s.Z_le_criticalOrbit hb hc hab hcb
  have hAC : A ≤ normalizer (Q R c : Set (FreeAmalgam R)) :=
    (hAQ.trans (DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer hab hcb)).trans (Q_normalized R c)
  have hCZ : ⁅A ⊓ Q R c,B⁆ ≤ Z R (alpha R) :=
    ((commutator_mono inf_le_right le_rfl).trans hcommB).trans hZG
  have hZB : ⁅Z R (alpha R),B⁆ ≤ Z R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((hBQ.trans ((Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color hab) hcb).trans
        (fun _ hx => hx.2 _ (adjacent_symm R hab)))).trans
        (Z_normalized R (alpha R)))
  have hh := commutatorPreimage_relIndex_mul_le A B (Q R c) (Z R (alpha R)) hAZ hAC hCZ hZB
  rwa [s.critical_image_order_two_of_core_large h t hfull hb hlarge hc] at hh

/-- The fixed-space bound applies to an actual opposite source orbit. -/
theorem exists_oppositeOrbit_fixed_index_bound (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ∃ B : Subgroup (FreeAmalgam R), Z R c ≤ B ∧ core R c ≤ B ∧ B ≤ Q R c ∧
      stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)) ∧
      ⁅Q R c,B⁆ ≤ Z R b ∧
      2 * (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
        (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b) := by
  obtain ⟨B,hZ,hplane,hcore,hBQ,hn,hcomm,hcentral,hmove⟩ :=
    s.exists_opposite_criticalOrbit h t hfull hb hlarge hc hab hcb
  exact ⟨B,hZ,hcore,hBQ,hn,hcomm,
    s.criticalOrbit_fixed_index_mul_two_le h t hfull hb hlarge hc hab hcb B hBQ hcomm⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
