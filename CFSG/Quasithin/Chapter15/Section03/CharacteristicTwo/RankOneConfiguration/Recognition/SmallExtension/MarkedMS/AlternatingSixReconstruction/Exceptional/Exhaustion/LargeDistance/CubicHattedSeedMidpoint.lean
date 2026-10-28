module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicGeneratingShiftCentralization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRestrictedCover

/-!
# Hatted seeds on the original cubic plane

At distance four a large original critical image admits a restricted full
seed containing the entire first-edge seed and of index at most two on its
moving cover. Its commutator with the whole midpoint two-core is exactly
the original critical commutator. Plane quadraticity centralizes that
commutator under the midpoint core; the full-cover restriction then controls
the whole core, retaining the actual cubic kernel and both moving covers.

This does not assert that a chosen backward shift has large image or that
the original whole-radius commutator is residual-fixed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The actual restricted seed retains its full edge attachment and its
critical commutator, now against the entire midpoint core. -/
theorem plane_critical_hatted_seed_midpoint_control
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    ∃ E : Subgroup (FreeAmalgam Rg),
      Z Rg (p.walk.getVert 1) ≤ E ∧ E ≤ Z Rg a ∧
      (E ⊓ U Rg a).relIndex (U Rg a) ≤ 2 ∧
      ⁅E,Q Rg (p.walk.getVert 2)⁆ = ⁅Z Rg a,Z Rg z⁆ := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let K := ⁅Z Rg a,Z Rg z⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent Rg a t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hQcT : Q Rg c ≤ Q Rg t := Q_le_adjacent_h Rg ht hct
  have hTG : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hAz : Z Rg z ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical z p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,
      SimpleGraph.dist_comm,p.dist_end,hl]
    change 2 < sourceDistance h
    omega
  have htC : Z Rg t ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := by
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hQcT (hAz hy))
  have hAG : Z Rg a ≤ stabilizer Rg z :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hsplit : Z Rg a = U Rg a ⊔ Z Rg t := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg a t).mp hat
    · rw [hg.1,hg.2]
      have hh := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
      rw [graph_U_map h e hz] at hh
      have he := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
        A.map (MulAut.conj g⁻¹).toMonoidHom) hh
      rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
      simpa [alpha,beta] using he
    · have ha := p.start_color
      rw [hg.1] at ha
      cases ha
  have hfull : ⁅U Rg a,Z Rg z⁆ = K := by
    have hh := commutator_eq_of_centralizing_sup
      ((sup_comm (Z Rg t) (U Rg a)).trans
        hsplit.symm)
      htC (((DistanceEight.U_le_Z Rg a).trans hAG).trans (Z_normalized Rg z))
    rw [commutator_comm (Z Rg z) (U Rg a),commutator_comm (Z Rg z) (Z Rg a)] at hh
    exact hh
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a p.start_color
  have hA : Z Rg z ≤ i.range := (hAz.trans (hQcT.trans hTG)).trans_eq hir.symm
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hKZ : K ≤ Z Rg z :=
    le_normalizer_iff_commutator_le_right.mp (hAG.trans (Z_normalized Rg z))
  have hAA : ⁅U Rg a,Z Rg z⁆ ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    (hfull.le.trans hKZ).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hcard := reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hlarge
  obtain ⟨W,hW,hiW,hpres,hcontrol⟩ := embedded_cover_restriction_preserving h e hz hk i hi
    (Z Rg z) hA (hiQ.symm ▸ hcard) (hiU.symm ▸ hAA)
  rw [hiU] at hW hiW hpres hcontrol
  have hKQ : K ≤ centralizer (Q Rg c : Set (FreeAmalgam Rg)) := by
    intro x hx y hy
    have hh := plane_critical_commutator_le_first_seed h e hz hk u hR p hx
    change x ∈ Z Rg t at hh
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2 y (hQcT hy)
  have hWK : ⁅W,Q Rg c⁆ = K := by
    apply le_antisymm
    · exact (hcontrol _ ((hQcT.trans hTG).trans_eq hir.symm) (hfull.le.trans hKQ)).trans_eq hfull
    · rw [←hfull,←hpres]
      exact commutator_mono le_rfl hAz
  let E := W ⊔ Z Rg t
  have hFZ : Z Rg t ≤ Z Rg a := adjacent_Z_le Rg p.start_color hat
  have hEZ : E ≤ Z Rg a := sup_le (hW.trans (DistanceEight.U_le_Z Rg _)) hFZ
  have hFQ : Z Rg t ≤ centralizer (Q Rg c : Set (FreeAmalgam Rg)) := by
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hQcT hy)
  have hZG : Z Rg z ≤ stabilizer Rg a := hAz.trans (hQcT.trans hTG)
  have hKZa : K ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_left.mp (hZG.trans (Z_normalized Rg a))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  have hKN : Z Rg a ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hKZa)).trans (Subgroup.centralizer_le_normalizer _)
  let := finite_Z Rg a
  let : Finite (U Rg a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
  refine ⟨E,le_sup_right,hEZ,
    (relIndex_le_of_le_left (le_inf (show W ≤ E from le_sup_left) hW)
      index_ne_zero_of_finite).trans hiW,?_⟩
  apply le_antisymm
  · exact commutator_sup_le_of_relative_normal (Z Rg a) W (Z Rg t)
      (Q Rg c) K hKN (hW.trans (DistanceEight.U_le_Z Rg _)) hFZ hWK.le
      ((commutator_eq_bot_iff_le_centralizer.mpr hFQ).le.trans bot_le)
  · change K ≤ ⁅E,Q Rg c⁆
    rw [←hWK]
    exact commutator_mono le_sup_left le_rfl

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
