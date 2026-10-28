module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEvenRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEvenRadius

/-!
# The even midpoint two-core on the original Borel graph

The whole derived radius is residual-fixed, centralizes the starting two-core,
and is moved by the full stabilizer. Its centralizer therefore has exactly A6
as its image under the original cubic projection. The midpoint two-core fixes
the derived radius, which lies in the midpoint seed. Thus this entire two-core
has even image. Its proper-mover containment and the critical endpoint's image
of order four identify that image with the endpoint image.

The original two-group image formula gives index four modulo Q, retaining the
odd quotient E/Q. Equal indices factor the entire midpoint two-core as its
intersection with the starting two-core joined to the full endpoint seed.
Consequently its action on the full starting seed is exactly the critical
commutator. Conjugation transports the index, factorization and movement to
every original critical path, with the literal midpoint preserved.

The internal import of EvenRadius intentionally reuses its chart and index
proofs; their private names do not enter this module's public statements.
OriginalSylowExceptional applies the results to c.L,d.S and constructs a path
with all three conclusions. Whole-radius/core fixedness and the terminal
contradiction of MS93 (5.12)(2) remain to be proved, as do CoreExhaustion and
whole intrinsic exceptional reconstruction.

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
/-- The literal cubic image of the centralizer of the whole derived radius is A6. -/
theorem borel_four_derived_centralizer_image
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    CubicAction.graphImage h e hz hk
      (centralizer ((⁅V Rg (alpha Rg),V Rg (alpha Rg)⁆ :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) = alternatingGroup (Fin 6) := by
  let a := alpha Rg
  let H := ⁅V Rg a,V Rg a⁆
  let C := (centralizer (H : Set (FreeAmalgam Rg))).comap (embedM Rg)
  have hconf := borel_four_radius_derived_configuration h e hz hk u hR
  have hHC : H ≤ centralizer (Ltilde Rg a : Set (FreeAmalgam Rg)) :=
    hconf.1.trans inf_le_right
  have hHL : Ltilde Rg a ≤ centralizer (H : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp hHC
  have hHQ : Q Rg a ≤ centralizer (H : Set (FreeAmalgam Rg)) :=
    (Q_le_centralizer_X Rg a).trans (centralizer_le hconf.2.1)
  have hLC : L.subgroupOf (L ⊔ R) ≤ C := by
    intro x hx
    apply hHL
    rw [Ltilde_alpha,h.relative_residual]
    exact mem_map_of_mem (embedM Rg) hx
  have hQC : pCore 2 (L ⊔ R : Subgroup G) ≤ C := by
    intro x hx
    apply hHQ
    rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact mem_map_of_mem (embedM Rg) hx
  have hker : (π).ker ≤ C := by
    rw [CubicAction.projection_kernel]
    exact sup_le ((map_subtype_le _).trans hLC) hQC
  have hAlt : alternatingGroup (Fin 6) ≤ C.map π := by
    rw [←CubicAction.component_image h e hz hk]
    exact map_mono hLC
  have hdiv : (C.map π).index ∣ 2 := by
    rw [←alternatingGroup.index_eq_two (α := Fin 6)]
    exact index_dvd_of_le hAlt
  change C.map π = alternatingGroup (Fin 6)
  have hCimage : C.map π = alternatingGroup (Fin 6) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
    · have hm : C.map π = ⊤ := index_eq_one.mp h1
      have hc : C = ⊤ := by
        have hh := congrArg (Subgroup.comap π) hm
        simpa only [comap_map_eq,sup_eq_left.mpr hker,comap_top] using hh
      exfalso
      apply hconf.2.2.2
      apply le_centralizer_iff.mp
      intro x hx
      change x ∈ stabilizer Rg (mVertex Rg 1) at hx
      rw [stabilizer_m_base] at hx
      obtain ⟨m,rfl⟩ := hx
      exact show m ∈ C from hc.symm ▸ mem_top m
    · exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
  exact hCimage

include h e hz hk in
/-- The midpoint two-core fixes the whole derived radius, hence has even cubic image. -/
theorem borel_four_midpoint_core_even
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    CubicAction.graphImage h e hz hk (Q Rg (p.walk.getVert 2)) ≤ alternatingGroup (Fin 6) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hHseed := (borel_four_radius_span_derived h e hz hk u hR p).2.2
  have hQC := (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q Rg (p.walk.getVert 2) hc))).trans (centralizer_le hHseed)
  exact (map_mono (comap_mono (f := embedM Rg) hQC)).trans_eq
    (borel_four_derived_centralizer_image h e hz hk u hR)

include h e hz hk in
/-- The entire midpoint two-core has exactly the even critical endpoint image and index four modulo the starting two-core. -/
theorem borel_four_midpoint_core_image
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    CubicAction.graphImage h e hz hk (Q Rg (p.walk.getVert 2)) =
      CubicAction.graphImage h e hz hk (Z Rg z) ∧
      (Q Rg (alpha Rg)).relIndex (Q Rg (p.walk.getVert 2)) = 4 := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hQJ := borel_four_large_midpoint_core_le_mover h e hz hk u hR p
    (borel_four_critical_images_large h e hz hk u hR p)
  obtain ⟨v,hv⟩ := borel_join_image_plane h e hz hk u hR t hat (Q Rg c) hQJ
  have hD : CubicAction.graphImage h e hz hk (Q Rg c) ≤ D0.map (MulAut.conj v).toMonoidHom := by
    have hAlt : (alternatingGroup (Fin 6)).map (MulAut.conj v).toMonoidHom =
        alternatingGroup (Fin 6) :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
    rw [show D0 = D ⊓ alternatingGroup (Fin 6) from rfl,
      Subgroup.map_inf _ _ _ (MulAut.conj v).injective,hAlt]
    exact le_inf hv (borel_four_midpoint_core_even h e hz hk u hR p)
  have hzQ : Z Rg z ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,hl,(sourceGeometry h).distance_constant _ p.end_color]
    exact distance_gt_two h e hz hk
  have hzG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) p.critical
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hzi := graph_two_image_card h e hz hk (Z Rg z) hzG (IsElementaryAbelian.isPGroup 2 _)
  have hi := (borel_four_critical_indices h e hz hk u hR p).2
  have hmap : CubicAction.graphImage h e hz hk (Z Rg z) ≤
      CubicAction.graphImage h e hz hk (Q Rg c) := map_mono (comap_mono hzQ)
  have hcard : Nat.card (D0.map (MulAut.conj v).toMonoidHom) = 4 := by
    rw [card_map_of_injective (MulAut.conj v).injective,D0_card]
  have hZeq := eq_of_le_of_card_ge (hmap.trans hD) (by rw [hcard,hzi,hi])
  have hQeq := le_antisymm hD (hZeq ▸ hmap)
  have hQG : Q Rg c ≤ stabilizer Rg (alpha Rg) :=
    hQJ.trans ((remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1.trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hat)))
  exact ⟨hQeq.trans hZeq.symm, by
    rw [←graph_two_image_card h e hz hk (Q Rg c) hQG
      (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc),hQeq,hcard]⟩

include h e hz hk in
/-- The whole midpoint two-core is its intersection with the starting two-core joined to the full endpoint seed. -/
theorem borel_four_midpoint_core_factorization
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    Q Rg (p.walk.getVert 2) =
      (Q Rg (p.walk.getVert 2) ⊓ Q Rg (alpha Rg)) ⊔ Z Rg z := by
  let c := p.walk.getVert 2
  let A := (Z Rg z).comap (embedM Rg)
  let Y := (Q Rg c).comap (embedM Rg)
  let Q₀ := pCore 2 (L ⊔ R : Subgroup G)
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hzV : Z Rg z ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,hl,(sourceGeometry h).distance_constant _ p.end_color]
    exact distance_gt_two h e hz hk
  have hzG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) p.critical
  have hVG : Q Rg c ≤ stabilizer Rg (alpha Rg) := by
    have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
      apply (cosetGraph_adj Rg _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using
        p.walk.adj_getVert_succ (i := 0) (by omega)
    have hVJ := borel_four_large_midpoint_core_le_mover h e hz hk u hR p
      (borel_four_critical_images_large h e hz hk u hR p)
    exact hVJ.trans ((remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1.trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hat)))
  have hAm : A.map (embedM Rg) = Z Rg z :=
    map_comap_eq_self (hzG.trans_eq (stabilizer_m_base Rg))
  have hYm : Y.map (embedM Rg) = Q Rg c :=
    map_comap_eq_self (hVG.trans_eq (stabilizer_m_base Rg))
  have hQm : Q₀.map (embedM Rg) = Q Rg (alpha Rg) :=
    (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
  have hVi := (borel_four_midpoint_core_image h e hz hk u hR p).2
  have hZi := (borel_four_critical_indices h e hz hk u hR p).2
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
/-- The entire midpoint two-core has exactly the critical commutator on the starting seed. -/
theorem borel_four_midpoint_core_movement
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ⁅Z Rg (alpha Rg),Q Rg (p.walk.getVert 2)⁆ = ⁅Z Rg (alpha Rg),Z Rg z⁆ := by
  let c := p.walk.getVert 2
  let K := Q Rg c ⊓ Q Rg (alpha Rg)
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
  rw [borel_four_midpoint_core_factorization h e hz hk u hR p,commutator_comm]
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
/-- The entire midpoint two-core lies in the starting residual times its original two-core. -/
theorem borel_four_midpoint_core_residual_core
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    Q Rg (p.walk.getVert 2) ≤ Ltilde Rg (alpha Rg) ⊔ Q Rg (alpha Rg) := by
  rw [borel_four_midpoint_core_factorization h e hz hk u hR p]
  exact sup_le (inf_le_right.trans le_sup_right)
    (borel_four_critical_endpoint_residual_core h e hz hk u hR p)

include h e hz hk in
/-- The two-core index, full factorization and exact seed movement hold at every original critical path, with its literal midpoint. -/
theorem borel_four_midpoint_core_at
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (Q Rg a).relIndex (Q Rg (p.walk.getVert 2)) = 4 ∧
      Q Rg (p.walk.getVert 2) = (Q Rg (p.walk.getVert 2) ⊓ Q Rg a) ⊔ Z Rg z ∧
      ⁅Z Rg a,Q Rg (p.walk.getVert 2)⁆ = ⁅Z Rg a,Z Rg z⁆ := by
  obtain ⟨x,hx⟩ := exists_mVertex_of_color Rg p.start_color
  have he : act Rg x⁻¹ a = alpha Rg := by
    rw [hx,act_mVertex,mul_inv_cancel]
    rfl
  obtain ⟨q,hq⟩ : ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x⁻¹ z),
      ∀ i, q.walk.getVert i = act Rg x⁻¹ (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg x⁻¹ a) (act Rg x⁻¹ z),
        ∀ i, q.walk.getVert i = act Rg x⁻¹ (p.walk.getVert i) :=
      ⟨p.act x⁻¹, fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [he] at hh
  have hi := (borel_four_midpoint_core_image h e hz hk u hR q).2
  have hf := borel_four_midpoint_core_factorization h e hz hk u hR q
  have hm := borel_four_midpoint_core_movement h e hz hk u hR q
  rw [hq 2,←he,Q_act,Q_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hi
  rw [hq 2,←he,Q_act,Q_act,Z_act,←Subgroup.map_inf _ _ _ (MulAut.conj _).injective,
    ←Subgroup.map_sup] at hf
  rw [hq 2,←he,Q_act,Z_act,Z_act,←map_commutator,←map_commutator] at hm
  exact ⟨hi,(map_injective (MulAut.conj _).injective) hf,
    (map_injective (MulAut.conj _).injective) hm⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
