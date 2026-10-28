module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EqualShifts
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.SmallSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadius

/-!
# Unconditional critical paths in the remaining Borel geometry

If one critical radius were trapped, the strict-slice shifts would force
every two-edge slice to have index at most two. The already proved uniform
small-slice comparison excludes that trapping, including central generation.
Thus every critical radius escapes. Prepending the actual two-edge walk
and reversing the resulting paths gives all backward overlaps, reverse
prefixes and forward eligibility on the original cubic graph.

OriginalSylowExceptional applies this theorem to the literal original
c.L,d.S source pair. Both full moving covers and the cubic kernel E/Q remain.
Forward eligibility is not the strict forward bound of (5.9). That bound,
the terminal distance exclusions and whole-core exhaustion remain open.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7)--(5.8), printed
pp.919--920; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
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
private theorem borel_trapped_radius_base_slices
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {c t : Vertex Rg} (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t) :
    (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    by_contra! hh
    exact large_critical_radius_escape h e hz hk p hh hbad
  by_contra! hstrict
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨k,hkG,hkt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hat ha1
  have hkfix : act Rg k (alpha Rg) = alpha Rg := hkG
  have hdelta : Adjacent Rg (act Rg k c) (p.walk.getVert 1) := by
    rw [←hkt]
    exact (adjacent_act_iff Rg k _ _).mpr hct
  have hBs := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb k (alpha Rg) rfl
  rw [hkfix] at hBs
  have hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg k c)) := by
    rw [U_act,hBs,relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hstrict
  obtain ⟨s,has,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,hindex,halt⟩ :=
    borel_strict_small_shift h e hz hk u hR p hp hdelta hs
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hqbad : V Rg (alpha Rg) ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hqverts,Q_act]
    have hV : (V Rg (alpha Rg)).map (MulAut.conj x⁻¹).toMonoidHom =
        V Rg (alpha Rg) := mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized Rg _ ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [←hV]
    exact map_mono hbad
  have hcs : Adjacent Rg (act Rg g (act Rg k c)) s := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hdelta
  have hdist : (cosetGraph Rg).dist (act Rg g (act Rg k c)) (alpha Rg) ≤ 2 :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two has hcs
  have hZV : Z Rg (act Rg g (act Rg k c)) ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  rcases halt with ⟨b,_,_⟩ | ⟨b,_,_⟩
  · exact b.critical.2 (hZV.trans hbad)
  · exact b.critical.2 (hZV.trans hqbad)

include h e hz hk in
/-- A trapped Borel radius forces every two-edge Baumann slice to have
index at most two, including central generation. The same selected switch transports
radius containment to the paired path, excluding both backward alternatives. -/
theorem borel_trapped_radius_uniform_slices
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hbad : V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {v c t : Vertex Rg} (hv : color Rg v = false)
    (hvt : Adjacent Rg v t) (hct : Adjacent Rg c t) :
    (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  obtain ⟨f,hf⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg f⁻¹ a = alpha Rg := by
    rw [hf,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg f⁻¹ a) (act Rg f⁻¹ z),
      (∀ i, p₀.walk.getVert i = act Rg f⁻¹ (p.walk.getVert i)) ∧
      p₀.walk.length = p.walk.length :=
    ⟨p.act f⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert],
      actWalk_length Rg f⁻¹ p.walk⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hverts,hlen⟩ := hpact
  have hbad₀ : V Rg (alpha Rg) ≤ Q Rg (p₀.walk.getVert (p₀.walk.length-2)) := by
    rw [hlen,hverts,←hbase,V_act,Q_act]
    exact map_mono hbad
  obtain ⟨g,hgv⟩ := exists_mVertex_of_color Rg hv
  have hgvbase : act Rg g⁻¹ v = alpha Rg := by
    rw [hgv,act_mVertex,mul_inv_cancel]
    rfl
  have hgt : Adjacent Rg (alpha Rg) (act Rg g⁻¹ t) := by
    rw [←hgvbase]
    exact (adjacent_act_iff Rg g⁻¹ _ _).mpr hvt
  have hh := borel_trapped_radius_base_slices h e hz hk u hR p₀ hbad₀ hgt
    ((adjacent_act_iff Rg g⁻¹ _ _).mpr hct)
  rw [←hgvbase,Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb g⁻¹ v hv,U_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hh
  exact hh


include h e hz hk in
/-- Every critical radius escapes in the original Borel geometry. A trapped
radius would make all slices small, where the two-slice residual comparison
already excludes trapping. No central-generation premise remains. -/
theorem borel_radius_escape
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  exact borel_radius_escape_of_uniform_slices h e hz hk u hR
    (fun _ _ _ hv hvt hct =>
      borel_trapped_radius_uniform_slices h e hz hk u hR p hbad hv hvt hct) p hbad

include h e hz hk in
/-- The complete Borel backward-path and forward-eligibility conclusion on
the original graph, with all overlaps and both full moving covers. The
strict forward estimates and terminal distance exclusions are separate. -/
theorem borel_critical_paths
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
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
    borel_radius_escape h e hz hk u hR p
  have hprefix := reverse_prefix_of_radius_escape h e hb escape p
  refine ⟨escape _ _ p,backward_path_of_radius_escape h p (escape _ _ p) hb,hprefix,?_⟩
  obtain ⟨d,q,_,hqa⟩ := hprefix
  have hh := critical_start_not_le_second_slice h e hz hb q
  rwa [hqa] at hh

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
