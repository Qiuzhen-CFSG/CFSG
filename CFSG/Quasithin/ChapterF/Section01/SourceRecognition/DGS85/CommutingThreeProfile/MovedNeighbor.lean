module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionGeometry

/-!
# A moved neighbor in the three-core configuration

Let `A` be the intersection of the first radius-one span with the opposite
two-core.  If `A` acts nontrivially on the neighboring span, the span
definition supplies a neighboring vertex whose center is moved by `A`.  The
middle vertex is excluded when `A` lies in its two-core, and the moved center
also shows that `A` is not contained in the two-core at the selected neighbor.
This is the choice made at the start of DGS85 (12.3)(a), printed p.179.
The statement keeps the literal graph, centers and intrinsic cores; no tree
identification or equality between a local kernel and its two-core is used.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- A nontrivial span action moves a neighboring center away from the middle vertex. -/
theorem exists_moved_neighbor_of_nontrivial_commutator
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    {y m : Vertex F} (A : Subgroup G) (hAy : A ≤ Q F y) (hAm : A ≤ Q F m)
    (hmove : ⁅A, V F y 1⁆ ≠ ⊥) :
    ∃ z, (graph F).Adj y z ∧ z ≠ m ∧ ⁅A, Z F z⁆ ≠ ⊥ ∧ ¬ A ≤ Q F z := by
  have hcentral (v : Vertex F) (hAv : A ≤ Q F v) : ⁅A, Z F v⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    intro z hz
    exact centralizer_le hAv ((mem_omegaCenterIn_iff _ _).mp (hZ v hz)).2.1
  have hex : ∃ z, (graph F).Adj y z ∧ ⁅A, Z F z⁆ ≠ ⊥ := by
    by_contra! hn
    apply hmove
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rcases (mem_ball_one F y z).mp hz with hz | rfl
    · exact hn z hz
    · exact hcentral y hAy
  obtain ⟨z, hz, hzm⟩ := hex
  exact ⟨z, hz, fun he => hzm (he ▸ hcentral m hAm), hzm,
    fun hAz => hzm (hcentral z hAz)⟩

/-- The middle core fixes both endpoints and therefore normalizes the actual intersection. -/
theorem core_intersection_normalized_by_middle
    [∀ i, Finite (F i)] (hQ : ∀ v, Q F v ≤ U F v)
    {x y m : Vertex F} (hxm : (graph F).Adj x m) (hym : (graph F).Adj y m) :
    Q F m ≤ normalizer (V F x 1 ⊓ Q F y : Set G) := by
  have hmx : Q F m ≤ stabilizer F x :=
    (hQ m).trans ((ballKernel_one_le_edge F hxm.symm).trans inf_le_right)
  have hmy : Q F m ≤ stabilizer F y :=
    (hQ m).trans ((ballKernel_one_le_edge F hym.symm).trans inf_le_right)
  have hnQ : stabilizer F y ≤ normalizer (Q F y : Set G) :=
    (stabilizer F y).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F y)))
  exact (le_inf (hmx.trans (stabilizer_normalizes_V F x 1)) (hmy.trans hnQ)).trans
    inf_normalizer_le_normalizer_inf

/-- Critical distance greater than two supplies the middle-core placement needed for the choice. -/
theorem intersection_moved_neighbor
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hSyl : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (hb : 2 < b F) {x y m : Vertex F} (hxm : (graph F).Adj x m)
    (hmove : ⁅V F x 1 ⊓ Q F y, V F y 1⁆ ≠ ⊥) :
    ∃ z, (graph F).Adj y z ∧ z ≠ m ∧
      ⁅V F x 1 ⊓ Q F y, Z F z⁆ ≠ ⊥ ∧ ¬ V F x 1 ⊓ Q F y ≤ Q F z := by
  exact exists_moved_neighbor_of_nontrivial_commutator F hZ _ inf_le_right
    (inf_le_left.trans (V_le_neighbor_Q F hgen hZ hSyl hb hxm)) hmove

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
