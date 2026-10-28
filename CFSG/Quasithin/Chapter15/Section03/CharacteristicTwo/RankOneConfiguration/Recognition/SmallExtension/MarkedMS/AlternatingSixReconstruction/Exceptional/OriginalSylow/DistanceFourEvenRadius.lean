module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourDerivedRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.ChiefCubicCores

/-!
# The exact even midpoint-radius image on the original Borel graph

The midpoint two-core lies in the proper Borel mover. The whole midpoint
radius has even image, so its image lies in the even three-pair subgroup
of order four. Its critical endpoint already has image of order at least
four; hence both images equal that same conjugate four-group. Transport
also gives order four for both images of every critical pair.

The two-group image formula compares these orders with indices modulo the
original two-core Q. Equal indices give the whole midpoint radius as its
intersection with Q joined to the endpoint seed. Since Q centralizes the
starting seed, the entire radius has exactly the critical commutator on
that seed. In particular the argument never identifies the cubic kernel
E with Q, and retains both full covers and their central attachments.

OriginalSylowExceptional applies these results to the literal c.L,d.S
source graph. They supply the whole-radius action comparison for the
remaining MS93 (5.12)(2) terminal argument. Whole-radius/core fixedness,
CoreExhaustion and the whole intrinsic exceptional block remain to be proved.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(2), printed pp.925--926; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
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
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem borel_join_image_plane
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (t : Vertex Rg) (hat : Adjacent Rg (alpha Rg) t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ edgeOffenderJoin (alpha Rg) t) :
    ∃ v : S, CubicAction.graphImage h e hz hk A ≤ D.map (MulAut.conj v).toMonoidHom := by
  have hbase : edgeOffenderJoin (alpha Rg) (beta Rg) =
      (borelPlane h e hz hk u).map (embedM Rg) :=
    remaining_join_in_chart h e hz hk u (Or.inr hR) rfl (base_adjacent Rg) (embedM Rg)
      (embedM_injective Rg) (Q_beta Rg).symm
      (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
      (graph_U_map h e hz)
  obtain ⟨g,hg|hg⟩ := edge_transitive Rg hat (base_adjacent Rg)
  · have hgM : g ∈ (embedM Rg).range := by
      change g ∈ Mbar Rg
      rw [←stabilizer_m_base Rg]
      exact hg.1
    obtain ⟨m,rfl⟩ := hgM
    have hJ : (edgeOffenderJoin (alpha Rg) t).map
        (MulAut.conj ((embedM Rg m)⁻¹)).toMonoidHom =
          (borelPlane h e hz hk u).map (embedM Rg) := by
      rw [←remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hat,hg.1,hg.2]
      exact hbase
    have hAm (x : (L ⊔ R : Subgroup G)) (hx : x ∈ A.comap (embedM Rg)) :
        m⁻¹*x*m ∈ borelPlane h e hz hk u := by
      have hh := ((map_mono hA).trans_eq hJ) (mem_map_of_mem
        (MulAut.conj ((embedM Rg m)⁻¹)).toMonoidHom hx)
      obtain ⟨r,hr,he⟩ := hh
      have heq : r = m⁻¹*x*m := by
        apply embedM_injective Rg
        change embedM Rg r = (embedM Rg m)⁻¹ *
          embedM Rg x * ((embedM Rg m)⁻¹)⁻¹ at he
        simpa only [map_mul,map_inv,inv_inv] using he
      exact heq ▸ hr
    refine ⟨π m*u,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    have hxD := (hAm x hx).2
    obtain ⟨r,hr,he⟩ := hxD
    refine ⟨r,hr,?_⟩
    change (π m*u)*r*(π m*u)⁻¹=π x
    have he' : u*r*u⁻¹ = (π m)⁻¹*π x*π m := by
      change u*r*u⁻¹ = π (m⁻¹*x*m) at he
      simpa only [map_mul,map_inv] using he
    calc
      (π m*u)*r*(π m*u)⁻¹ = π m*(u*r*u⁻¹)*(π m)⁻¹ := by group
      _ = π x := by rw [he']; group
  · have hh : color Rg (beta Rg) = false := by
      change color Rg (hVertex Rg 1) = false
      rw [←hg.1,action_preserves_color]
      rfl
    cases hh

include h e hz hk in
private theorem graph_two_image_card
    (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg (alpha Rg))
    (hA : IsPGroup 2 A) :
    Nat.card (CubicAction.graphImage h e hz hk A) = (Q Rg (alpha Rg)).relIndex A := by
  have hm : (A.comap (embedM Rg)).map (embedM Rg) = A :=
    map_comap_eq_self (hAG.trans_eq (stabilizer_m_base Rg))
  change Nat.card ((A.comap (embedM Rg)).map π) = _
  rw [CubicAction.permutation_image_card_of_two h e hz hk _
    (hA.comap_of_injective _ (embedM_injective Rg)),
    Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,←hm,
    relIndex_map_map_of_injective _ _ (embedM_injective Rg),
    comap_map_eq_self_of_injective (embedM_injective Rg)]

include h e hz hk in
/-- The full midpoint radius and its critical endpoint have the same even three-pair image, with both original two-core indices equal to four. -/
theorem borel_four_midpoint_radius_image
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ∃ v : S,
      CubicAction.graphImage h e hz hk (V Rg (p.walk.getVert 2)) =
        D0.map (MulAut.conj v).toMonoidHom ∧
      CubicAction.graphImage h e hz hk (Z Rg z) =
        D0.map (MulAut.conj v).toMonoidHom ∧
      (Q Rg (alpha Rg)).relIndex (V Rg (p.walk.getVert 2)) = 4 ∧
      (Q Rg (alpha Rg)).relIndex (Z Rg z) = 4 := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hJ := borel_four_large_midpoint_core_le_mover h e hz hk u hR p
    (borel_four_critical_images_large h e hz hk u hR p)
  have hVcJ := ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) c hc).trans hJ
  obtain ⟨v,hv⟩ := borel_join_image_plane h e hz hk u hR t hat (V Rg c) hVcJ
  have heven := borel_four_midpoint_radius_even h e hz hk u hR p
  have hD : CubicAction.graphImage h e hz hk (V Rg c) ≤ D0.map (MulAut.conj v).toMonoidHom := by
    have hAlt : (alternatingGroup (Fin 6)).map (MulAut.conj v).toMonoidHom =
        alternatingGroup (Fin 6) :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
    rw [show D0 = D ⊓ alternatingGroup (Fin 6) from rfl,
      Subgroup.map_inf _ _ _ (MulAut.conj v).injective,hAlt]
    exact le_inf hv heven
  have hzV : Z Rg z ≤ V Rg c := by
    exact le_iSup_of_le z (le_iSup_of_le (by
      rw [SimpleGraph.dist_comm,p.dist_end,hl]) le_rfl)
  have hzG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) p.critical
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hzi := graph_two_image_card h e hz hk (Z Rg z) hzG (IsElementaryAbelian.isPGroup 2 _)
  have hlarge := reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p
    (borel_four_critical_images_large h e hz hk u hR p)
  have hmap : CubicAction.graphImage h e hz hk (Z Rg z) ≤
      CubicAction.graphImage h e hz hk (V Rg c) := map_mono (comap_mono hzV)
  have hcard : Nat.card (D0.map (MulAut.conj v).toMonoidHom) = 4 := by
    rw [card_map_of_injective (MulAut.conj v).injective,D0_card]
  have hZeq := eq_of_le_of_card_ge (hmap.trans hD) (by rw [hcard,hzi]; exact hlarge)
  have hVeq := le_antisymm hD (hZeq ▸ hmap)
  have hVG : V Rg c ≤ stabilizer Rg (alpha Rg) :=
    hVcJ.trans ((remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1.trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hat)))
  have hVP : IsPGroup 2 (V Rg c) :=
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc).to_le ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) c hc)
  refine ⟨v,hVeq,hZeq,?_,?_⟩
  · rw [←graph_two_image_card h e hz hk (V Rg c) hVG hVP,hVeq,hcard]
  · rw [←hzi,hZeq,hcard]

private theorem le_sup_normal_of_equal_index {F : Type*} [Group F]
    (Q A B : Subgroup F) [Q.Normal] (hAB : A ≤ B)
    (hA : Q.relIndex A = 4) (hB : Q.relIndex B = 4) : B ≤ Q ⊔ A := by
  have hh := relIndex_mul_relIndex Q (Q ⊔ A) (Q ⊔ B) le_sup_left
    (sup_le_sup_left hAB Q)
  rw [relIndex_sup_left,relIndex_sup_left,hA,hB] at hh
  exact le_sup_right.trans (relIndex_eq_one.mp (by omega : (Q ⊔ A).relIndex (Q ⊔ B) = 1))

include h e hz hk in
/-- The whole midpoint radius is its intersection with the starting two-core joined to the full endpoint seed. -/
theorem borel_four_midpoint_radius_factorization
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    V Rg (p.walk.getVert 2) =
      (V Rg (p.walk.getVert 2) ⊓ Q Rg (alpha Rg)) ⊔ Z Rg z := by
  let c := p.walk.getVert 2
  let A := (Z Rg z).comap (embedM Rg)
  let Y := (V Rg c).comap (embedM Rg)
  let Q₀ := pCore 2 (L ⊔ R : Subgroup G)
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hzV : Z Rg z ≤ V Rg c := by
    exact le_iSup_of_le z (le_iSup_of_le (by
      rw [SimpleGraph.dist_comm,p.dist_end,hl]) le_rfl)
  have hzG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) p.critical
  have hVG : V Rg c ≤ stabilizer Rg (alpha Rg) := by
    have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
      apply (cosetGraph_adj Rg _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using
        p.walk.adj_getVert_succ (i := 0) (by omega)
    have hVJ := ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) c hc).trans
      (borel_four_large_midpoint_core_le_mover h e hz hk u hR p
        (borel_four_critical_images_large h e hz hk u hR p))
    exact hVJ.trans ((remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1.trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hat)))
  have hAm : A.map (embedM Rg) = Z Rg z :=
    map_comap_eq_self (hzG.trans_eq (stabilizer_m_base Rg))
  have hYm : Y.map (embedM Rg) = V Rg c :=
    map_comap_eq_self (hVG.trans_eq (stabilizer_m_base Rg))
  have hQm : Q₀.map (embedM Rg) = Q Rg (alpha Rg) :=
    (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
  obtain ⟨_,_,_,hVi,hZi⟩ := borel_four_midpoint_radius_image h e hz hk u hR p
  have hiA : Q₀.relIndex A = 4 := by
    rw [←relIndex_map_map_of_injective _ _ (embedM_injective Rg),hAm,hQm]
    exact hZi
  have hiY : Q₀.relIndex Y = 4 := by
    rw [←relIndex_map_map_of_injective _ _ (embedM_injective Rg),hYm,hQm]
    exact hVi
  have hAY : A ≤ Y := comap_mono hzV
  have hcover := le_sup_normal_of_equal_index Q₀ A Y hAY hiA hiY
  have he : Y = (Y ⊓ Q₀) ⊔ A := by
    apply le_antisymm
    · intro y hy
      have hyp : y ∈ (Q₀ : Set (L ⊔ R : Subgroup G)) * (A : Set (L ⊔ R : Subgroup G)) := by
        rw [←coe_mul_of_right_le_normalizer_left Q₀ A le_normalizer_of_normal]
        exact hcover hy
      obtain ⟨q,hq,a,ha,rfl⟩ := hyp
      have hqY : q ∈ Y := by
        have hh := Y.mul_mem hy (Y.inv_mem (hAY ha))
        simpa only [mul_inv_cancel_right] using hh
      exact ((Y ⊓ Q₀) ⊔ A).mul_mem (mem_sup_left ⟨hqY,hq⟩) (mem_sup_right ha)
    · exact sup_le inf_le_left hAY
  have hm := congrArg (Subgroup.map (embedM Rg)) he
  rwa [Subgroup.map_sup,Subgroup.map_inf _ _ _ (embedM_injective Rg),hYm,hQm,hAm] at hm

include h e hz hk in
/-- The entire midpoint radius has exactly the critical commutator on the starting seed. -/
theorem borel_four_midpoint_radius_movement
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ⁅Z Rg (alpha Rg),V Rg (p.walk.getVert 2)⁆ = ⁅Z Rg (alpha Rg),Z Rg z⁆ := by
  let c := p.walk.getVert 2
  let K := V Rg c ⊓ Q Rg (alpha Rg)
  let D := ⁅Z Rg (alpha Rg),Z Rg z⁆
  have hDZa := critical_seed_commutator_le h p
  have hDZz : D ≤ Z Rg z := by
    dsimp only [D]
    rw [commutator_comm]
    exact critical_seed_commutator_le h
      (CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color (reverse_pair h e p))
  have hQD : Q Rg (alpha Rg) ≤ centralizer (D : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg (alpha Rg) rfl))).trans (centralizer_le hDZa)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hzD : Z Rg z ≤ centralizer (D : Set (FreeAmalgam Rg)) :=
    (le_centralizer (Z Rg z)).trans (centralizer_le hDZz)
  have hND : Q Rg (alpha Rg) ⊔ Z Rg z ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    (sup_le hQD hzD).trans (Subgroup.centralizer_le_normalizer _)
  rw [borel_four_midpoint_radius_factorization h e hz hk u hR p,commutator_comm]
  apply le_antisymm
  · apply commutator_sup_le_of_relative_normal
      (Q Rg (alpha Rg) ⊔ Z Rg z) K (Z Rg z) (Z Rg (alpha Rg)) D hND
      (inf_le_right.trans le_sup_left) le_sup_right
    · rw [commutator_comm]
      exact (commutator_mono le_rfl inf_le_right).trans
        ((Z_centralizes_Q Rg (alpha Rg) rfl).le.trans bot_le)
    · rw [commutator_comm]
  · rw [commutator_comm (Z Rg (alpha Rg)) (Z Rg z)]
    exact commutator_mono le_sup_right le_rfl

include h e hz hk in
private theorem borel_four_reverse_critical_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (Q Rg a).relIndex (Z Rg z) = 4 := by
  obtain ⟨x,hx⟩ := exists_mVertex_of_color Rg p.start_color
  have he : act Rg x⁻¹ a = alpha Rg := by
    rw [hx,act_mVertex,mul_inv_cancel]
    rfl
  have q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x⁻¹ z) :=
    he ▸ p.act x⁻¹
  obtain ⟨_,_,_,_,hi⟩ := borel_four_midpoint_radius_image h e hz hk u hR q
  have hi' : (Q Rg (act Rg x⁻¹ a)).relIndex (Z Rg (act Rg x⁻¹ z)) = 4 := by
    rw [he]
    exact hi
  rwa [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hi'

include h e hz hk in
/-- Both original critical images have order four, on every component path. -/
theorem borel_four_critical_indices
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (Q Rg z).relIndex (Z Rg a) = 4 ∧ (Q Rg a).relIndex (Z Rg z) = 4 := by
  exact ⟨borel_four_reverse_critical_index h e hz hk u hR
    (CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color (reverse_pair h e p)),
    borel_four_reverse_critical_index h e hz hk u hR p⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
