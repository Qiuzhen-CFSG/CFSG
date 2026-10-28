module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusGeometry
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupAction.MaximalCosetOrbit

/-!
# Opposite-edge transfer across the full critical kernel

Let H be the retained order-two line of an escaping full radius kernel Y
on a critical path from a to z. Some conjugate of H under the same opposite
edge Q_s escapes Q_a. Otherwise the Q_s-orbit span N of H lies in the full
kernel Z_z intersect Q_a. The equality [Y,Z_z intersect Q_a] = H makes Y
normalize N. Since Q_s and Y generate G_z, N is G_z-invariant. The proved
full-seed conjugate-generator theorem moves H outside the centralizer of
Z_a, contradicting N <= Q_a. This argument uses the literal generating
stabilizer, without identifying the graph with a natural-module graph.

The escaping conjugate H' supplements the original full critical kernel
in Z_z. Both the midpoint radius kernel and the whole last-edge radius
kernel have commutator with H' outside Z_a. The same conjugator produces
a second critical path, with H' equal to its literal full-radius line.
Both joined kernels are not two-groups, and every cross-distance remains
(4-i)+(4-j) on these same paths. The whole-core and C.1.32 applications
retain the cubic projection kernel E, both moving covers and all central
attachments. These are transferred commutator obstructions; the terminal
contradiction, other distance/image cases and both exhaustions remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the full-kernel and generating-stabilizer comparisons in (5.12),
printed pp.924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e in
private theorem reverse_pair {a c : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a c) :
    CriticalPair Rg c a ((sourceGeometry h).exists_critical c p.end_color) :=
  critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    c p.end_color p.critical

include h e hz hk in
private theorem invariant_seed_kernel_excludes_noncentral_line
    {z a : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) z a)
    (hp : (Q Rg a).relIndex (Z Rg z) < 4)
    (N H : Subgroup (FreeAmalgam Rg))
    (hNZ : N ≤ Z Rg z) (hNQ : N ≤ Q Rg a)
    (hN : stabilizer Rg z ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hHN : H ≤ N) (hcard : Nat.card H = 2)
    (hnon : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) : False := by
  obtain ⟨x,hx⟩ := exists_mVertex_of_color Rg p.start_color
  have hb : act Rg x⁻¹ z = alpha Rg := by
    rw [hx,act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj x).toMonoidHom
  let N₀ := N.map f
  let H₀ := H.map f
  have pc := p.act x⁻¹
  rw [hb] at pc
  have hpc : (Q Rg (act Rg x⁻¹ a)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hb,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hp
  have hZG : (stabilizer Rg z).map f = stabilizer Rg (alpha Rg) := by
    simpa only [inv_inv,hb] using (stabilizer_act Rg x⁻¹ z).symm
  have hZ : (Z Rg z).map f = Z Rg (alpha Rg) := by
    simpa only [inv_inv,hb] using (Z_act Rg x⁻¹ z).symm
  have hNZ₀ : N₀ ≤ Z Rg (alpha Rg) := hZ ▸ map_mono hNZ
  have hNQ₀ : N₀ ≤ Q Rg (act Rg x⁻¹ a) := by
    rw [Q_act,inv_inv]
    exact map_mono hNQ
  have hN₀ : stabilizer Rg (alpha Rg) ≤ normalizer (N₀ : Set (FreeAmalgam Rg)) := by
    rw [←hZG]
    apply le_normalizer_iff_commutator_le_right.mpr
    change ⁅(stabilizer Rg z).map f,N.map f⁆ ≤ N.map f
    rw [←map_commutator]
    exact map_mono (le_normalizer_iff_commutator_le_right.mp hN)
  have hH₀ : H₀ ≤ N₀ := map_mono hHN
  have hc₀ : Nat.card H₀ = 2 := (card_map_of_injective (MulAut.conj x).injective).trans hcard
  have hn₀ : ¬ H₀ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    intro hh
    apply hnon
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply (map_injective (f := f) (MulAut.conj x).injective)
    rw [map_commutator,hZG,Subgroup.map_bot]
    exact commutator_eq_bot_iff_le_centralizer.mpr hh
  obtain ⟨g,hg,_,hmove⟩ := exists_seed_line_generator h e hz hk pc hpc H₀
    (hH₀.trans hNZ₀) hc₀ hn₀
  have hgN := hN₀ (Ltilde_le_stabilizer (alpha Rg) hg)
  have hm : H₀.map (MulAut.conj g).toMonoidHom ≤ N₀ := by
    exact (map_mono hH₀).trans_eq (mem_normalizer_iff_map_conj_eq.mp hgN)
  apply hmove
  exact (hm.trans hNQ₀).trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg _ pc.end_color)))

include h e hz hk in
/-- The opposite edge moves a noncentral full-radius line outside the original
full critical kernel. If every conjugate stayed inside, their span would be
normalized by the radius kernel and the opposite edge, hence by the endpoint
stabilizer; the full-seed conjugate-generator theorem excludes that span. -/
theorem plane_radius_line_opposite_kernel_escape
    {a z s : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y H : Subgroup (FreeAmalgam Rg))
    (hgen : Q Rg s ⊔ Y = stabilizer Rg z)
    (hHZ : H ≤ Z Rg z) (hcard : Nat.card H = 2)
    (hnon : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))
    (hcomm : ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ H) :
    ∃ g ∈ Q Rg s, ¬ H.map (MulAut.conj g).toMonoidHom ≤ Q Rg a := by
  by_contra! hn
  let N := conjugateSpanBy H (Q Rg s)
  have hHN : H ≤ N := le_conjugateSpanBy _ _
  have hNZ : N ≤ Z Rg z := conjugateSpanBy_le hHZ
    ((show Q Rg s ≤ stabilizer Rg z from hgen ▸ le_sup_left).trans (Z_normalized Rg z))
  have hNQ : N ≤ Q Rg a := by
    rw [show N = conjugateSpanBy H (Q Rg s) from rfl,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le fun g => hn g g.property
  have hYN : Y ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact ((commutator_mono le_rfl (le_inf hNZ hNQ)).trans hcomm).trans hHN
  have hGN : stabilizer Rg z ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le (le_normalizer_conjugateSpanBy _ _) hYN
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color (reverse_pair h e p)
  have hpr : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  exact invariant_seed_kernel_excludes_noncentral_line h e hz hk pr hpr N H
    hNZ hNQ hGN hHN hcard hnon

include h e hz hk in
/-- The same opposite-edge conjugator makes the full-radius line supplement
the original critical kernel and carry endpoint commutator escape for both
radius kernels. Both displaced joins remain non-two-groups on separated paths. -/
theorem plane_small_four_radius_line_transfer
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      Nat.card H = 2 ∧
      ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
        (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          let H' := H.map (MulAut.conj g).toMonoidHom
          ¬ H' ≤ Q Rg a ∧ (Z Rg z ⊓ Q Rg a) ⊔ H' = Z Rg z ∧
          ¬ ⁅Y,H'⁆ ≤ Z Rg a ∧ ¬ ⁅W,H'⁆ ≤ Z Rg a ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            ¬ IsPGroup 2 (Y ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)) :
              Subgroup (FreeAmalgam Rg)) ∧
            ¬ IsPGroup 2 (W ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)) :
              Subgroup (FreeAmalgam Rg)) ∧
            H' = ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),
              X Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) := by
  obtain ⟨a,z,p,s,hzs,hgen,hgenY,_,hiY,hiW,_,hcard,hHZ,hHlast,hHC,
    _,_,_,_,_,_,_,_,hescape⟩ := plane_small_four_radius_growth h e hz hk u hR hb4 hsmall
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let Y := V Rg a ⊓ Q Rg c
  let W := V Rg a ⊓ Q Rg t
  let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hYt : Y ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hYW : Y ≤ W := le_inf inf_le_left hYt
  have hAY : Z Rg a ≤ Y := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact distance_gt_two h e hz hk
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  have hnot : ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg a := by rwa [←hXZ]
  obtain ⟨_,_,_,_,hdis,halign⟩ := plane_radius_kernel_alignment h e hz hk u hR p
    (hsmall _ _ p) Y inf_le_left (by simpa only [hl,Nat.reduceSub] using hYt) hAY hnot
  rw [←hXZ] at hdis halign
  change H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ at hdis
  have hpair : Q Rg t ⊔ Q Rg s = stabilizer Rg z := (sup_comm _ _).trans hgen
  have hHY : H ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    hHC.trans (centralizer_le (show Y ≤ V Rg a ⊔ V Rg c from
      inf_le_left.trans le_sup_left))
  have hHZz : H ≤ Z Rg z := hHlast.trans (adjacent_Z_le Rg p.end_color hzt)
  have hnon : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    intro hh
    have he : H = ⊥ := by simpa only [inf_eq_left.mpr hh] using hdis
    change Nat.card H = 2 at hcard
    rw [he,Subgroup.card_bot] at hcard
    omega
  obtain ⟨g,hgs,hgQ⟩ := plane_radius_line_opposite_kernel_escape h e hz hk p
    (hsmall _ _ p) Y H hgenY hHZz hcard hnon (by rw [←hXZ])
  let H' := H.map (MulAut.conj g).toMonoidHom
  have hgG : g ∈ stabilizer Rg z := hgs.2 _ (adjacent_symm Rg hzs)
  have hH'Z : H' ≤ Z Rg z := (map_mono hHZz).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg z hgG))
  have hF : Z Rg z ⊓ Q Rg a =
      Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair p.end_color (reverse_pair h e p))).symm
  have hgY : ¬ H' ≤ centralizer (Y : Set (FreeAmalgam Rg)) := by
    intro hh
    apply hgQ
    exact (show H' ≤ Z Rg z ⊓ Q Rg a from hF ▸
      le_inf hH'Z (hh.trans (centralizer_le hAY))).trans inf_le_right
  have hsupp : (Z Rg z ⊓ Q Rg a) ⊔ H' = Z Rg z := by
    obtain ⟨v,hv,hvQ⟩ := SetLike.not_le_iff_exists.mp hgQ
    have hi : (Z Rg z ⊓ Q Rg a).relIndex (Z Rg z) = 2 := by
      rw [inf_relIndex_left]
      exact (small_critical_indices h e hz hk p (hsmall _ _ p)).2
    have he := sup_zpowers_eq_of_relIndex_prime (show Z Rg z ⊓ Q Rg a ≤ Z Rg z from inf_le_left)
      Nat.prime_two hi (hH'Z hv) (fun hh => hvQ hh.2)
    exact le_antisymm (sup_le inf_le_left hH'Z)
      (he.symm.le.trans (sup_le_sup_left (zpowers_le.mpr hv) _))
  have hesc : ¬ ⁅Y,H'⁆ ≤ Z Rg a := by
    intro hh
    apply hnot
    rw [←hsupp,commutator_comm]
    apply commutator_sup_le_of_relative_normal (stabilizer Rg a) _ _ Y (Z Rg a)
      (Z_normalized Rg a)
    · exact inf_le_right.trans (fun _ hx => hx.1)
    · exact hH'Z.trans (critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
        p.critical)
    · rw [commutator_comm,←hXZ]
      exact hHZ.trans inf_le_left
    · rwa [commutator_comm]
  have hescW : ¬ ⁅W,H'⁆ ≤ Z Rg a :=
    fun hh => hesc ((commutator_mono hYW le_rfl).trans hh)
  let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hsep : H.map (MulAut.conj g).toMonoidHom ⊔ C ≠ H ⊔ C := by
    intro he
    apply hgY
    apply (show H.map (MulAut.conj g).toMonoidHom ≤ H ⊔ C from he ▸ le_sup_left).trans
    exact sup_le hHY (inf_le_right.trans (centralizer_le
      (hYt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt)))))
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  have hQC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q Rg a p.start_color))
  have hfix : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p (hsmall _ _ p)).2
  have halign' : H ⊔ C = ⁅Z Rg z,Z Rg a⁆ ⊔ C := by
    rw [commutator_comm (Z Rg z)]
    change H ⊔ C = ⁅Z Rg a,X Rg z⁆ ⊔ C at halign
    rwa [hXZ] at halign
  have hYtwo := plane_displaced_line_pair_not_two h e hz hk u hR p.end_color hzt hzs hpair
    (Z Rg a) Y H hAY hYt p.critical.2 hfix hiY halign' g hgs hsep
  have hWtwo : ¬ IsPGroup 2 (W ⊔ W.map (MulAut.conj g).toMonoidHom : Subgroup (FreeAmalgam Rg)) :=
    fun hh => hYtwo (hh.to_le (sup_le_sup hYW (map_mono hYW)))
  have hfixz : act Rg g⁻¹ z = z :=
    (stabilizer Rg z).inv_mem (hgs.2 _ (adjacent_symm Rg hzs))
  have hq : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
      ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) (act Rg g⁻¹ z),
        ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i) := by
      refine ⟨p.act g⁻¹,?_⟩
      intro i
      simp only [CriticalPath.act,actWalk_getVert]
    let P := fun w : Vertex Rg =>
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) w,
        ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)
    exact (congrArg P hfixz).mp hh
  obtain ⟨q,hverts⟩ := hq
  refine ⟨a,z,p,hcard,s,hzs,hgenY,hiY,hiW,g,hgs,hfixz,hgQ,hsupp,hesc,hescW,
    q,hverts,?_,?_,?_,?_⟩
  · rw [hverts 2,V_act,Q_act,inv_inv,
      ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    exact hYtwo
  · rw [hverts 3,V_act,Q_act,inv_inv,
      ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    exact hWtwo
  · have hXfix : (X Rg z).map (MulAut.conj g).toMonoidHom = X Rg z := by
      simpa only [inv_inv,hfixz] using (X_act Rg g⁻¹ z).symm
    change (⁅V Rg a ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆).map (MulAut.conj g).toMonoidHom = _
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective,hXfix,hverts 2,V_act,Q_act,Q_act,inv_inv]
  · have hVa : V Rg a ≤ stabilizer Rg a :=
      ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color).trans
        (fun _ hx => hx.1)
    have hYz : Y ≤ stabilizer Rg z := hYt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
    have hbG : (stabilizer Rg a).map (MulAut.conj g).toMonoidHom =
        stabilizer Rg (act Rg g⁻¹ a) := by rw [stabilizer_act,inv_inv]
    have hzG : (stabilizer Rg z).map (MulAut.conj g).toMonoidHom = stabilizer Rg z :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg z).le_normalizer hgG)
    have hh := radius_pair_path_geometry_of_not_two h p.end_color p.walk q.walk
      p.shortest q.shortest Y (Y.map (MulAut.conj g).toMonoidHom)
      (inf_le_left.trans hVa) hYz
      ((map_mono (inf_le_left.trans hVa)).trans_eq hbG) ((map_mono hYz).trans_eq hzG) hYtwo
    have hq4 : q.walk.length = 4 := q.length_eq_b.trans hb4
    simpa only [hl,hq4] using hh.2.2.2


omit hk in
include h e hz in
/-- Whole-core application of the full-kernel line supplement and the paired
commutator escape, retaining the original cubic projection and both covers. -/
theorem coreExhaustion_or_cubic_plane_radius_line_transfer :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
            ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
              let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
              let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
              let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
              Nat.card H = 2 ∧
              ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
                (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
                ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
                  let H' := H.map (MulAut.conj g).toMonoidHom
                  ¬ H' ≤ Q Rg a ∧ (Z Rg z ⊓ Q Rg a) ⊔ H' = Z Rg z ∧
                  ¬ ⁅Y,H'⁆ ≤ Z Rg a ∧ ¬ ⁅W,H'⁆ ≤ Z Rg a ∧
                  ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                    (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                    ¬ IsPGroup 2 (Y ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)) :
                      Subgroup (FreeAmalgam Rg)) ∧
                    ¬ IsPGroup 2 (W ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)) :
                      Subgroup (FreeAmalgam Rg)) ∧
                    H' = ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),
                      X Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ ∧
                    (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                      (4-i) + (4-j)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_radius_line_transfer h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application on the same cubic graph. Terminal exclusion
and the remaining distance, image and core-exhaustion branches are still open. -/
theorem rankTwo_or_cubic_plane_radius_line_transfer :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
            ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
              let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
              let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
              let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
              Nat.card H = 2 ∧
              ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
                (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
                ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
                  let H' := H.map (MulAut.conj g).toMonoidHom
                  ¬ H' ≤ Q Rg a ∧ (Z Rg z ⊓ Q Rg a) ⊔ H' = Z Rg z ∧
                  ¬ ⁅Y,H'⁆ ≤ Z Rg a ∧ ¬ ⁅W,H'⁆ ≤ Z Rg a ∧
                  ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                    (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                    ¬ IsPGroup 2 (Y ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)) :
                      Subgroup (FreeAmalgam Rg)) ∧
                    ¬ IsPGroup 2 (W ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)) :
                      Subgroup (FreeAmalgam Rg)) ∧
                    H' = ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),
                      X Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ ∧
                    (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
                      (4-i) + (4-j)))) :=
  (coreExhaustion_or_cubic_plane_radius_line_transfer h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
