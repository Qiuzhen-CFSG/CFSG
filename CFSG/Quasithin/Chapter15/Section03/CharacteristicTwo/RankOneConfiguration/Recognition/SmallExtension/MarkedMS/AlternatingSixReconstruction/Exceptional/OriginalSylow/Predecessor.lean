module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Radius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePredecessor

/-!
# Predecessor commutators for equal Borel movers

A small predecessor Baumann slice identifies the full reverse critical
kernel with the intersection of its endpoint seed and that slice. This
makes its commutator with the predecessor core normal in the whole
predecessor stabilizer: the residual normalizes it by the slice definition,
and the incident edge normalizes both factors.

When the two incident Thompson movers agree, quadraticity fixes that
commutator under their common mover. The actual paired movers generate the
whole stabilizer, so normality upgrades this fixedness to centrality. Every
predecessor residual conjugation of a core actor consequently preserves its
commutator with the unchanged full kernel.

The proof uses the proper Borel mover, both moving covers and the original
cubic kernel E. The private predecessor import supplies only the generic
commutator transport lemma, not a plane-image estimate. This supplies the
equal-mover predecessor comparison in MS93 (5.8); it does not exclude the
remaining configurations or prove whole-core exhaustion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.8), printed pp.919--920; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem normal_mover_fixed_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hs : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t)
    (N : Subgroup (FreeAmalgam Rg))
    (hN : stabilizer Rg (alpha Rg) ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hfix : N ≤ centralizer (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg))) :
    N ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let C := centralizer (N : Set (FreeAmalgam Rg))
  have hCN : stabilizer Rg (alpha Rg) ≤ normalizer (C : Set (FreeAmalgam Rg)) :=
    hN.trans (normalizer_le_normalizer_centralizer N)
  have hJC : edgeOffenderJoin (alpha Rg) t ≤ C := le_centralizer_iff.mp hfix
  obtain ⟨s,has,r,hr,_,hpair,_,_⟩ :=
    remaining_small_critical_plane_selectors h e hz hk u (Or.inr hR) p hs
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hat has
  have hconj (v : Vertex Rg) (hav : Adjacent Rg (alpha Rg) v)
      (hv : edgeOffenderJoin (alpha Rg) v ≤ C)
      (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg (alpha Rg)) :
      edgeOffenderJoin (alpha Rg) (act Rg x v) ≤ C := by
    have he := remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hav x
    rw [show act Rg x (alpha Rg) = alpha Rg from hx] at he
    rw [he]
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hv
    have hC : C.map (MulAut.conj x⁻¹).toMonoidHom = C :=
      mem_normalizer_iff_map_conj_eq.mp (hCN ((stabilizer Rg (alpha Rg)).inv_mem hx))
    exact hh.trans_eq hC
  have hsC : edgeOffenderJoin (alpha Rg) s ≤ C := hgt ▸ hconj t hat hJC g hg
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  apply le_centralizer_iff.mp
  rw [←hpair]
  exact sup_le hsC (hconj s has hsC x hx)

include h e hz hk in
/-- A normal subgroup fixed by an incident Borel mover is fixed by the whole
component stabilizer whenever one small critical path starts there. -/
theorem borel_normal_subgroup_fixed_by_mover
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hs : (Q Rg z).relIndex (Z Rg a) < 4) (hat : Adjacent Rg a t)
    (N : Subgroup (FreeAmalgam Rg))
    (hN : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hfix : N ≤ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg))) :
    N ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hp : Nonempty (CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg g⁻¹ z)) := by
    rw [←hbase]
    exact ⟨p.act g⁻¹⟩
  obtain ⟨p₀⟩ := hp
  have hs₀ : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hs
  have ht₀ : Adjacent Rg (alpha Rg) (act Rg g⁻¹ t) := by
    rw [←hbase]
    exact (adjacent_act_iff Rg g⁻¹ _ _).mpr hat
  have hG : (stabilizer Rg a).map f = stabilizer Rg (alpha Rg) := by
    rw [←stabilizer_act,hbase]
  have hJ : (edgeOffenderJoin a t).map f = edgeOffenderJoin (alpha Rg) (act Rg g⁻¹ t) := by
    rw [←remaining_edge_join_act h e hz hk u (Or.inr hR) p.start_color hat g⁻¹,hbase]
  have hN₀ : stabilizer Rg (alpha Rg) ≤ normalizer (N.map f : Set (FreeAmalgam Rg)) := by
    rw [←hG]
    exact (map_mono hN).trans (N.le_normalizer_map f)
  have hf₀ : N.map f ≤ centralizer
      (edgeOffenderJoin (alpha Rg) (act Rg g⁻¹ t) : Set (FreeAmalgam Rg)) := by
    rw [←hJ]
    exact (map_mono hfix).trans (map_centralizer_le_centralizer_image _ f)
  have hout := normal_mover_fixed_base h e hz hk u hR p₀ hs₀ ht₀ (N.map f) hN₀ hf₀
  rw [←hG] at hout
  apply commutator_eq_bot_iff_le_centralizer.mp
  have he := commutator_eq_bot_iff_le_centralizer.mpr hout
  rw [←map_commutator] at he
  exact (map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp he

include h e hz hk in
/-- A small predecessor slice and equal predecessor movers make the full reverse
critical-kernel commutator central in the predecessor stabilizer. -/
theorem borel_equal_mover_predecessor_central
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (heq : edgeOffenderJoin (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-1)) =
      edgeOffenderJoin z (p.walk.getVert (p.walk.length-1))) :
    ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let K := Z Rg z ⊓ Q Rg a
  let N := ⁅K,Q Rg c⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hct : Adjacent Rg c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg t <;> simp_all
  have hslice := critical_predecessor_small_slice h e hz hk hb p hindex
  have hKB : K ≤ B Rg c ((sourceGeometry h).Z_normal _) := hslice.1.ge.trans inf_le_right
  have hVG := ((sourceGeometry h).V_le_Q hb c hc).trans
    (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)
  have hKQ : K ≤ Q Rg c := by
    intro x hx
    exact (sourceGeometry h).V_le_Q hb c hc (((mem_B_iff Rg c _ hVG x).mp (hKB hx)).1)
  have hfix : ⁅Ltilde Rg c,K⁆ ≤ centralizer (Q Rg c : Set (FreeAmalgam Rg)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff Rg c _ hVG x).mp (hKB hx)).2 l hl
  have hLn : Ltilde Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    fixed_mod_seed_normalizes_commutator K (Q Rg c) (Ltilde Rg c)
      (hKQ.trans (Q Rg c).le_normalizer)
      ((Ltilde_le_stabilizer c).trans (Q_normalized Rg c)) hfix
  have hTG : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hTZ : Q Rg t ≤ normalizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg z from fun _ hx => hx.2 _ (adjacent_symm Rg hzt)).trans
      (Z_normalized Rg z)
  have hTB : Q Rg t ≤ normalizer (B Rg c ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg)) :=
    hTG.trans (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h) hb c hc)
  have hTK : Q Rg t ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
    have hKeq : K = Z Rg z ⊓ B Rg c ((sourceGeometry h).Z_normal _) := hslice.1.symm
    rw [hKeq]
    exact (le_inf hTZ hTB).trans inf_normalizer_le_normalizer_inf
  have hTn : Q Rg t ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hTK hx),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg c (hTG hx))]
  have hgen : Ltilde Rg c ⊔ Q Rg t = stabilizer Rg c := by
    apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    · rw [h.relative_residual]
      exact (codisjoint_subgroupOf_sup L R).eq_top
    · exact hc
    · exact hct
  have hNn : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le hLn hTn
  have hQJ : Q Rg c ≤ edgeOffenderJoin z t :=
    heq ▸ (remaining_edge_thompson h e hz hk u (Or.inr hR) hc hct).2.1
  have hNJ : N ≤ centralizer (edgeOffenderJoin c t : Set (FreeAmalgam Rg)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [heq]
    exact (commutator_mono (commutator_mono inf_le_left hQJ) le_rfl).trans_eq
      (remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) p.end_color hzt)
  obtain ⟨x,hxa⟩ := exists_mVertex_of_color Rg p.start_color
  obtain ⟨y,hyc⟩ := exists_mVertex_of_color Rg hc
  let g := x⁻¹*y
  have hgc : act Rg g a = c := by
    rw [hxa,hyc,act_mVertex]
    simp only [g,mul_inv_cancel_left]
  have hpaths : Nonempty (CriticalPath Rg (sourceGeometry h) c (act Rg g z)) := by
    rw [←hgc]
    exact ⟨p.act g⟩
  obtain ⟨q⟩ := hpaths
  have hsmall : (Q Rg (act Rg g z)).relIndex (Z Rg c) < 4 := by
    rw [←hgc,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
      hslice.2.2]
    decide
  exact borel_normal_subgroup_fixed_by_mover h e hz hk u hR q hsmall hct N hNn hNJ

include h e hz hk in
/-- The same full reverse kernel has an invariant commutator under every
predecessor residual conjugation of its core actor. -/
theorem borel_equal_mover_predecessor_transport
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (heq : edgeOffenderJoin (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-1)) =
      edgeOffenderJoin z (p.walk.getVert (p.walk.length-1)))
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg z ⊓ Q Rg a,T.map (MulAut.conj k).toMonoidHom⁆ = ⁅Z Rg z ⊓ Q Rg a,T⁆ := by
  have hb := distance_gt_two h e hz hk
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hs := critical_predecessor_small_slice h e hz hk hb p hindex
  have hn := borel_equal_mover_predecessor_central h e hz hk u hR p hindex heq
  exact plane_slice_commutator_transport_of_fixed (h := h) hb hc _
    (hs.1.ge.trans inf_le_right) (hn.trans (centralizer_le (Ltilde_le_stabilizer _))) T hT k hkm

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
