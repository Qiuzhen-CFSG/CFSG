module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Radius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistinctShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelFixed

/-!
# Borel radius escape outside central generation

The full seed has index eight over every incident Borel edge seed. This
uses the actual edge fixed subgroup, so it needs no comparison between the
two Thompson movers. A trapped paired two-seed span, normalized by reverse
omega control, therefore has quotient order dividing eight over the
starting seed. The alternating-six action forces it into the Baumann slice.

An eligible neighboring seed contradicts that containment. Consequently,
unless the full omega layer is centrally generated, every original critical
radius escapes. Iterating the resulting backward paths gives a compatible
reverse prefix and forward eligibility on every path. No strict-slice or
large-image witness is required. Central generation remains an alternative;
forward eligibility does not assert a strict index bound.

The original graph, both full covers and the cubic kernel E with its odd
quotient over Q are retained. The private imports reuse the existing small
normal-section argument, seed decomposition and generic path transport.
The final theorem feeds the literal original-source reduction. The strict
forward estimates and terminal contradictions of (5.11)--(5.12), and hence
whole-core exhaustion, are still required.

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
/-- The full seed has index eight over its incident edge seed, for every
Borel edge and either full moving cover. No opposite-mover comparison is needed. -/
theorem borel_full_seed_edge_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    (Z Rg t).relIndex (Z Rg a) = 8 := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  have hseed : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hfixed : Z Rg a ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg)) = Z Rg t := by
    apply le_antisymm
    · rintro x ⟨hx,hxc⟩
      rw [Z,if_neg (by simp [ht])]
      have hZX := Z_le_X_of_positive Rg a ha ((sourceGeometry h).exists_critical a ha)
        (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
      have hZQt : Z Rg a ≤ Q Rg t := by
        apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a ha)
        rw [(sourceGeometry h).distance_constant a ha,
          SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hat)]
        exact lt_trans (by decide : 1 < 2) (distance_gt_two h e hz hk)
      exact mem_omegaCenter_iff.mpr ⟨hZQt hx,(mem_omegaCenter_iff.mp (hZX hx)).2.1,hxc⟩
    · exact le_inf (adjacent_Z_le Rg ha hat) hseed
  let := finite_Z Rg t
  have hZN : Z Rg t ≤ normalizer (U Rg a : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg ha hat).trans (Z_le_stabilizer Rg a)).trans (U_normalized a)
  have hfix : U Rg a ⊓ Z Rg t = U Rg a ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    rw [←hfixed,←inf_assoc,inf_eq_left.mpr (DistanceEight.U_le_Z Rg a)]
  rw [vertex_seed_eq_moving_sup_edge h e hz ha hat,
    relIndex_sup_of_normalizes (U Rg a) (Z Rg t) hZN,
    ←inf_relIndex_right,inf_comm (Z Rg t),hfix,inf_relIndex_left]
  exact borel_edge_fixed_index h e hz hk u hR ha hat

include h e hz hk in
/-- A trapped paired configuration lies in the Baumann slice when omega
central generation fails. The estimate covers every mover comparison. -/
theorem borel_trapped_slice_of_not_central_generation
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) :
    Z Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hseed (v : Vertex Rg) (hv : color Rg v = false) : Z Rg v ≤ X Rg v :=
    (sourceGeometry h).omega_bound v hv (by
      rw [(sourceGeometry h).distance_constant v hv]
      exact sourceDistance_pos h)
  have hTNa : Q Rg t ≤ normalizer (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg (alpha Rg) from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _)
  have hTNc : Q Rg t ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg _)
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact ((remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1.trans
        (le_inf hTNc hTNa)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (hseed z p.end_color).trans
        (small_trapped_span_normalized_of_not_central_generation h e hz hk p hp hat hct hn hbad)
    · exact (hseed z' q.end_color).trans
        (small_trapped_span_normalized_of_not_central_generation h e hz hk q hq hat hct hn hbad')
  have hZaT : Z Rg (alpha Rg) ≤ Q Rg t :=
    ((hseed _ rfl).trans (omegaCenter_le _)).trans (Q_le_adjacent_h Rg ht hat)
  let := finite_Z Rg (alpha Rg)
  have hsmall : (Z Rg (alpha Rg)).relIndex Y ∣ 8 := by
    change (Z Rg (alpha Rg)).relIndex (Z Rg c ⊔ Z Rg (alpha Rg)) ∣ 8
    rw [relIndex_sup_of_normalizes (Z Rg c) (Z Rg (alpha Rg)) (hZaT.trans hTNc)]
    have hd := relIndex_dvd_of_le_left (Z Rg c) (adjacent_Z_le Rg rfl hat)
    rw [borel_full_seed_edge_index h e hz hk u hR hc hct] at hd
    exact hd
  exact le_sup_left.trans (small_normal_radius_le_slice h e hz hk Y
    (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hsmall)


include h e hz hk in
private theorem borel_radius_escape_base_of_not_central_generation
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ¬ V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  have hb := distance_gt_two h e hz hk
  have hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    by_contra! hh
    exact large_critical_radius_escape h e hz hk p hh hbad
  obtain ⟨t,hat,r,hr,q,hqverts,hqs,hgen,_,_,_,_⟩ :=
    remaining_small_critical_paired_kernel_selectors h e hz hk u (Or.inr hR) p hp
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hqbad : V Rg (alpha Rg) ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hqverts,Q_act]
    have hV : (V Rg (alpha Rg)).map (MulAut.conj x⁻¹).toMonoidHom = V Rg (alpha Rg) :=
      mem_normalizer_iff_map_conj_eq.mp
        (DistanceEight.V_normalized Rg _ ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [←hV]
    exact map_mono hbad
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge h e hz hk hb rfl hat
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
  have hZB := borel_trapped_slice_of_not_central_generation h e hz hk u hR
    p q hp hqs hat hct hn hgen (hZV.trans hbad) (hZV.trans hqbad)
  exact hel ((DistanceEight.U_le_Z Rg c).trans hZB)

include h e hz hk in
/-- Failure of omega central generation forces radius escape on every
original critical path. No strict-slice or large-image witness is required. -/
theorem borel_radius_escape_of_not_central_generation
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      (∀ i, p₀.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
      p₀.walk.length = p.walk.length :=
    ⟨p.act g⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert],
      actWalk_length Rg g⁻¹ p.walk⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hverts,hlen⟩ := hpact
  apply borel_radius_escape_base_of_not_central_generation h e hz hk u hR hn p₀
  rw [hlen,hverts,←hbase,V_act,Q_act]
  exact map_mono hbad

include h e hz hk in
/-- Outside central generation every original path has compatible backward
and reverse-prefix paths and is eligible forward. -/
theorem borel_paths_of_not_central_generation
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
    (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
        w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
    (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
      q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
    ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  have escape := fun a z (p : CriticalPath Rg (sourceGeometry h) a z) =>
    borel_radius_escape_of_not_central_generation h e hz hk u hR hn p
  have hprefix := reverse_prefix_of_radius_escape h e hb escape p
  refine ⟨escape _ _ p,backward_path_of_radius_escape h p (escape _ _ p) hb,hprefix,?_⟩
  obtain ⟨d,q,_,hqa⟩ := hprefix
  have hh := critical_start_not_le_second_slice h e hz hb q
  rwa [hqa] at hh

include h e hz hk in
/-- The surviving Borel geometry is centrally generated or has compatible
critical paths everywhere. The uniformly-small-slice alternative no longer
blocks radius escape outside central generation. -/
theorem borel_central_or_paths
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (∀ a : Vertex Rg, color Rg a = false →
      (X Rg a = U Rg a ⊔
        (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
      X Rg a = Z Rg a) ∨
    (∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
      (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
        ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
          w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
        q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
      ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _)) := by
  classical
  by_cases hn : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))
  · apply Or.inl
    intro a ha
    have hh := omega_generation_transport (show color Rg (alpha Rg) = false from rfl) ha hn
    exact ⟨hh,omega_eq_seed_of_central_generation h a ha hh⟩
  exact Or.inr (fun _ _ p => borel_paths_of_not_central_generation h e hz hk u hR hn p)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
