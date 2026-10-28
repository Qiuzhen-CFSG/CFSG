module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelNormalMovement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourSmallExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity

/-!
# Midpoint core control for large original Borel critical images

For a four-edge critical path c--d--a--b--w with large endpoint image,
the midpoint core Q_a is normalized by the first edge and fixes
[U_c,Z_w]. Radius centrality gives this fixedness on the entire cover.
The finite normal-Borel calculation then puts Q_a in the proper mover
J_c(Q_d), using the literal cubic projection and the actual edge chart.

The proper mover is quadratic on U_c and has fixed index four. Hence the
whole movement [Z_c,Q_a] lies in U_c and X_a, has order dividing eight,
and is normalized by Q_d. It contains the entire critical commutator.
Both full covers of orders sixteen and thirty-two and their central
attachments remain; the cubic kernel E is never identified with Q.

OriginalSylowExceptional applies these statements to a large critical
path constructed on the literal source c.L,d.S graph. They provide the
midpoint-core comparisons used in MS93 (5.12)(2). Full radius/core
fixedness and the selected-span terminal contradiction are still needed
before CoreExhaustion and whole-block reconstruction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.2)(ii), and (5.12)(2), printed pp.867,913--914,925--926;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem borel_cover_normal_large_movement
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A P : Subgroup M) (hAR : A ≤ Rg) (hPR : P ≤ Rg)
    (hn : Rg ≤ normalizer (P : Set M))
    (hc : 2 < (pCore 2 M).relIndex A)
    (hf : P ≤ centralizer ((⁅(W : Subgroup M),A⁆ : Subgroup M) : Set M)) :
    P ≤ borelPlane h e hz hk u := by
  let := h.relative_normal
  have hker := CubicAction.moved_projection_kernel h e hz hk
  have him : P.map π ≤ D.map (MulAut.conj u).toMonoidHom := by
    apply BorelLargeModel.conjugate_normal_large_le_plane (A.map π) (P.map π) u
      ((map_mono hAR).trans_eq hR) ((map_mono hPR).trans_eq hR)
    · rw [←hR]
      exact (map_mono hn).trans (le_normalizer_map π)
    · rwa [CubicAction.permutation_image_card_of_two h e hz hk A
        (h.relative_radical.isPGroup.to_le hAR)]
    · rintro _ ⟨g,hg,rfl⟩ _ ⟨a,ha,rfl⟩ v
      obtain ⟨w,rfl⟩ := coverMap_surjective h e hz hk v
      have hw : coverAction h e hz hk (π a) w-w ∈ commutatorSpace W A := by
        rw [commutatorSpace_eq W π (CubicEven.projection_surjective h e hz hk) hker]
        exact Submodule.subset_span ⟨π a,mem_map_of_mem π ha,w,Submodule.mem_top,rfl⟩
      have hfix : coverAction h e hz hk (π g) (coverAction h e hz hk (π a) w-w) =
          coverAction h e hz hk (π a) w-w := by
        let d : Additive W := coverAction h e hz hk (π a) w-w
        have hd : (d.toMul : M) ∈ ⁅W,A⁆ := hw
        have hcent : (d.toMul : M) ∈ centralizer (P : Set M) :=
          (le_centralizer_iff.mp hf) hd
        have hh := (mem_fixedSpace_image W π (CubicEven.projection_surjective h e hz hk)
          hker P d).mpr hcent
        exact hh ⟨π g,mem_map_of_mem π hg⟩
      have hh := congrArg (coverMap h e hz hk) hfix
      simpa only [coverMap_equivariant,map_sub] using hh
  exact le_inf hPR (fun g hg => him (mem_map_of_mem π hg))

include h e hz hk in
/-- A normal edge actor fixing the movement of a large image lies in the
proper Borel mover on the original graph. The full moving cover is used. -/
theorem borel_edge_normal_large_movement
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (A P : Subgroup (FreeAmalgam Rg)) (hAT : A ≤ Q Rg t) (hPT : P ≤ Q Rg t)
    (hn : Q Rg t ≤ normalizer (P : Set (FreeAmalgam Rg)))
    (hiA : 2 < (Q Rg c).relIndex A)
    (hf : P ≤ centralizer ((⁅U Rg c,A⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    P ≤ edgeOffenderJoin c t := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz hc hct
  have hTG : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hPm : (P.comap i).map i = P := map_comap_eq_self ((hPT.trans hTG).trans_eq hir.symm)
  have hAm : (A.comap i).map i = A := map_comap_eq_self ((hAT.trans hTG).trans_eq hir.symm)
  have hAR : A.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hAm,hiR]
  have hPR : P.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hPm,hiR]
  have hn' : Rg ≤ normalizer (P.comap i : Set M) := by
    apply le_normalizer_iff.mpr
    intro g hg p hp
    change i (g*p*g⁻¹) ∈ P
    simp only [map_mul,map_inv]
    exact le_normalizer_iff.mp hn (i g) (hiR ▸ mem_map_of_mem i hg) (i p) hp
  have hi' : 2 < (pCore 2 M).relIndex (A.comap i) := by
    rw [←relIndex_map_map_of_injective _ _ hi,hiQ,hAm]
    exact hiA
  have hcomm : (⁅W,A.comap i⁆).map i = ⁅U Rg c,A⁆ := by
    rw [map_commutator,hiU,hAm]
  have hf' : P.comap i ≤ centralizer ((⁅W,A.comap i⁆ : Subgroup M) : Set M) := by
    intro p hp v hv
    apply hi
    simp only [map_mul]
    exact hf hp (i v) (hcomm ▸ mem_map_of_mem i hv)
  have hh := map_mono (f := i)
    (borel_cover_normal_large_movement h e hz hk u hR (A.comap i) (P.comap i)
      hAR hPR hn' hi' hf')
  rw [hPm] at hh
  rwa [remaining_join_in_chart h e hz hk u (Or.inr hR) hc hct i hi hiR hiQ hiU]

include h e hz hk in
/-- On a distance-four large critical path, its midpoint two-core lies in
the proper mover at the starting vertex. Radius centrality supplies the
pointwise fixedness needed for the normal Borel calculation. -/
theorem borel_four_large_midpoint_core_le_mover
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c w : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : 4 ≤ (Q Rg w).relIndex (Z Rg c)) :
    Q Rg (p.walk.getVert 2) ≤ edgeOffenderJoin c (p.walk.getVert 1) := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color Rg a = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hQaT : Q Rg a ≤ Q Rg t := Q_le_adjacent_h Rg ht hat
  have hTG : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hZa : Z Rg w ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    change 4-2 < sourceDistance h
    omega
  apply borel_edge_normal_large_movement h e hz hk u hR p.start_color hct (Z Rg w)
    (Q Rg a) (hZa.trans hQaT) hQaT (hTG.trans (Q_normalized Rg a))
  · have hh := reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hp
    omega
  · apply le_centralizer_iff.mp
    have hcV : Z Rg c ≤ V Rg a := terminal_neighbor_seed_radius hat hct
    have haw : (cosetGraph Rg).dist a w = 2 := by exact (p.dist_end 2).trans (by omega)
    have hwV : Z Rg w ≤ V Rg a := by
      exact le_iSup_of_le w (le_iSup_of_le (by rw [SimpleGraph.dist_comm,haw]) le_rfl)
    have hDX : ⁅U Rg c,Z Rg w⁆ ≤ X Rg a :=
      (commutator_mono ((DistanceEight.U_le_Z Rg c).trans hcV) hwV).trans
        (radius_bounds_at h e hz hk a ha c w).2.1
    exact hDX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)

include h e hz hk in
/-- The whole endpoint-seed movement by a large critical path's midpoint
core lies in midpoint omega, has order dividing eight on either cover,
and is normalized by the first edge. -/
theorem borel_four_large_midpoint_movement
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c w : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : 4 ≤ (Q Rg w).relIndex (Z Rg c)) :
    let H := ⁅Z Rg c,Q Rg (p.walk.getVert 2)⁆
    H ≤ U Rg c ∧ H ≤ X Rg (p.walk.getVert 2) ∧ Nat.card H ∣ 8 ∧
      Q Rg (p.walk.getVert 1) ≤ normalizer (H : Set (FreeAmalgam Rg)) ∧
      ⁅Z Rg c,Z Rg w⁆ ≤ H := by
  let a := p.walk.getVert 2
  let d := p.walk.getVert 1
  let H := ⁅Z Rg c,Q Rg a⁆
  change H ≤ U Rg c ∧ H ≤ X Rg a ∧ Nat.card H ∣ 8 ∧
    Q Rg d ≤ normalizer (H : Set (FreeAmalgam Rg)) ∧ ⁅Z Rg c,Z Rg w⁆ ≤ H
  have hb := borel_distance_eq_four h e hz hk u hR
  have hb2 := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color Rg a = false := (p.vertex_color (by omega)).mpr (by decide)
  have hcd : Adjacent Rg c d := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have had : Adjacent Rg a d := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hcore := borel_four_large_midpoint_core_le_mover h e hz hk u hR p hp
  obtain ⟨J,_,hJ,_,hJT,_,_,hfix,hquad⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR p.start_color hcd
  have hQJ : Q Rg a ≤ J := hcore.trans hJ.le
  have hdGc : Q Rg d ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hcd)
  have hdGa : Q Rg d ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg had)
  have hcomm : H = ⁅U Rg c,Q Rg a⁆ := by
    have hh := full_fixed_seed_edge_commutator h e hz p.start_color hcd
      (⊥ : Subgroup (FreeAmalgam Rg)) bot_le (Q Rg a) (hQJ.trans hJT)
    have hbot : centralizer ((⊥ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊤ := by
      apply top_unique
      intro x _ y hy
      rw [mem_bot.mp hy,mul_one,one_mul]
    simpa only [hbot,inf_top_eq] using hh
  have hHU : H ≤ U Rg c := by
    rw [hcomm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((hQJ.trans hJT).trans (hdGc.trans (U_normalized c)))
  have hHQ : H ≤ Q Rg a := (hHU.trans (DistanceEight.U_le_Z Rg c)).trans
    ((terminal_neighbor_seed_radius had hcd).trans ((sourceGeometry h).V_le_Q hb2 a ha))
  have hHJ : H ≤ centralizer (J : Set (FreeAmalgam Rg)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [hcomm]
    exact (commutator_mono (commutator_mono le_rfl hQJ) le_rfl).trans_eq hquad
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.start_color
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le (hHU.trans (DistanceEight.U_le_Z Rg c))
  have hHX : H ≤ X Rg a := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQ hx,elemPow_eq_one_of_isElementaryAbelian x hx,
      (hHJ.trans (centralizer_le hQJ)) hx⟩
  have hTN : Q Rg d ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅Z Rg c,Q Rg a⁆ : Subgroup (FreeAmalgam Rg)).map _ = _
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg c (hdGc hx)),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg a (hdGa hx))]
  let := finite_Z Rg c
  have hsmall : Nat.card H ∣ 8 := by
    let C := U Rg c ⊓ centralizer (J : Set (FreeAmalgam Rg))
    have hi : C.relIndex (U Rg c) = 4 := by
      rw [show C = U Rg c ⊓ centralizer (J : Set (FreeAmalgam Rg)) from rfl,inf_relIndex_left]
      exact hfix
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) C (U Rg c) bot_le inf_le_left
    simp only [relIndex_bot_left,hi] at hm
    have hc : Nat.card C ∣ 8 := by
      rcases graph_U_card h e hz hk c p.start_color with hh | hh
      · have he : Nat.card C = 4 := by omega
        rw [he]; decide
      · have he : Nat.card C = 8 := by omega
        rw [he]
    let : Finite C := Finite.of_injective
      (inclusion (inf_le_left.trans (DistanceEight.U_le_Z Rg c))) (inclusion_injective _)
    exact (card_dvd_of_le (le_inf hHU hHJ)).trans hc
  have hZwQa : Z Rg w ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,hl,(sourceGeometry h).distance_constant _ p.end_color]
    exact hb2
  exact ⟨hHU,hHX,hsmall,hTN,commutator_mono le_rfl hZwQa⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
