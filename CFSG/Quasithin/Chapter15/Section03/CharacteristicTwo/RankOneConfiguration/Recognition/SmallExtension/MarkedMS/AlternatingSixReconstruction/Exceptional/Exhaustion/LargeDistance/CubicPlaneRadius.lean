module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward

/-!
# Radius escape and uniform small slices in the cubic plane branch

A trapped radius is preserved by the actual switch in the paired plane
selector. Any strict two-edge slice would therefore produce a backward
critical path whose starting seed is still in its endpoint core, a
contradiction. Transporting the slice through the original component action
shows that one trapped radius forces every two-edge Baumann slice to have
index at most two, at every component vertex.

The predecessor-slice calculation then identifies each full reverse critical
kernel with its literal predecessor Baumann slice and gives order two for
both critical images. Consequently, a single large critical image or a
single strict slice forces radius escape for every critical path, including
paths with small images. The actual backward walks retain every overlap;
iterating and reversing them produces a critical prefix through the original
first two edges and proves forward eligibility.

The whole-core and literal C.1.32 consumers separate the original plane
branch into these path configurations or the uniform small-slice case.
The latter case is retained, as are the Borel branch, the terminal
contradictions, and both final core exhaustions. All statements use the
original graph and projection with kernel E, preserving the nontrivial E/Q
and both full moving covers. No identification with the natural graph is
made. The walk iteration adapts CubicPathExtension within this same graph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.8), printed pp.919--920; Aschbacher--Smith C.1.31--32,
printed pp.135--136. This module proves a reduction for (5.8), not its
remaining uniform small-slice exclusion or the terminal (5.11)--(5.12).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem plane_radius_failure_base_slices
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
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
    plane_small_critical_backward_shift h e hz hk u hR p hp hdelta hs
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
/-- If one plane radius is trapped, every two-edge Baumann slice in the
original graph has index at most two. The same selected switch transports
radius containment to the paired path, excluding both backward alternatives. -/
theorem plane_radius_failure_uniform_slices
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
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
  have hh := plane_radius_failure_base_slices h e hz hk u hR p₀ hbad₀ hgt
    ((adjacent_act_iff Rg g⁻¹ _ _).mpr hct)
  rw [←hgvbase,Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb g⁻¹ v hv,U_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hh
  exact hh

include h e hz hk in
private theorem critical_kernel_of_uniform_slices
    (hall : ∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
      (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    {c c' : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) c c') :
    Z Rg c' ⊓ B Rg (q.walk.getVert (q.walk.length-2))
        ((sourceGeometry h).Z_normal _) = Z Rg c' ⊓ Q Rg c ∧
      (Q Rg c).relIndex (Z Rg c') = 2 ∧
      (Q Rg c').relIndex (Z Rg c) = 2 := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb
  have hc : color Rg (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : q.walk.length = sourceDistance h := q.length_eq_b
    omega
  have hlast : Adjacent Rg c' (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hpre : Adjacent Rg (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  exact critical_predecessor_small_slice h e hz hk hb q
    (hall _ _ _ hc hpre hlast)

include h e hz hk in
/-- A single trapped plane radius forces the exact full reverse-kernel
identity and both order-two critical images on every critical path. -/
theorem plane_radius_failure_critical_kernels
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hbad : V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {c c' : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) c c') :
    Z Rg c' ⊓ B Rg (q.walk.getVert (q.walk.length-2))
        ((sourceGeometry h).Z_normal _) = Z Rg c' ⊓ Q Rg c ∧
      (Q Rg c).relIndex (Z Rg c') = 2 ∧
      (Q Rg c').relIndex (Z Rg c) = 2 := by
  exact critical_kernel_of_uniform_slices h e hz hk
    (fun _ _ _ hv hvt hct =>
      plane_radius_failure_uniform_slices h e hz hk u hR p hbad hv hvt hct) q

include h e hz hk in
/-- One large critical image forces every critical radius to escape, including
those on paths whose own critical images are small. -/
theorem plane_radius_escape_of_large_pair
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a))
    {c c' : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) c c') :
    ¬ V Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
  intro hbad
  have hh := (plane_radius_failure_critical_kernels h e hz hk u hR q hbad p).2.2
  omega

include h e hz hk in
/-- One strict two-edge slice forces radius escape on every critical path,
with no assumption on that path's image size. -/
theorem plane_radius_escape_of_strict_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {v c t : Vertex Rg} (hv : color Rg v = false)
    (hvt : Adjacent Rg v t) (hct : Adjacent Rg c t)
    (hs : 2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  exact (Nat.not_le_of_gt hs)
    (plane_radius_failure_uniform_slices h e hz hk u hR p hbad hv hvt hct)

include h in
private theorem backward_path_of_radius_escape
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (he : ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hb : 2 < sourceDistance h) :
    ∃ d, ∃ w : (cosetGraph Rg).Walk d a,
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
        w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hd : (cosetGraph Rg).dist a (p.walk.getVert (p.walk.length-2)) + 2 =
      (sourceGeometry h).b Rg := by
    rw [p.dist_start (Nat.sub_le _ _),←p.length_eq_b]
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    omega
  obtain ⟨d,hdc,hda,hn⟩ := exists_critical_shift Rg p.start_color hd he
  obtain ⟨w,hw⟩ := (cosetGraph_connected Rg).exists_walk_length_eq_dist d a
  have hw2 : w.length = 2 := hw.trans hda
  have hb2 : 2 ≤ (sourceGeometry h).b Rg := by change 2 ≤ sourceDistance h; omega
  exact ⟨d,w,p.prepend_two hb2 hdc w hw2 hn.2,hw2,rfl,
    fun _ hi => p.prepend_two_overlap hb2 hdc w hw2 hn.2 hi⟩

include h in
private theorem iterated_paths_of_radius_escape
    (hb : 2 < sourceDistance h)
    (escape : ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (n : ℕ) (hn : 2*n ≤ p.walk.length) :
    ∃ d d', ∃ q : CriticalPath Rg (sourceGeometry h) d d',
      ∀ i ≤ p.walk.length-2*n, q.walk.getVert (i+2*n) = p.walk.getVert i := by
  induction n with
  | zero => exact ⟨a,z,p,fun i _ => by simp⟩
  | succ n ih =>
    obtain ⟨d,d',q,hq⟩ := ih (by omega)
    obtain ⟨c,w,r,hw,hr,hover⟩ := backward_path_of_radius_escape h q (escape _ _ q) hb
    refine ⟨c,q.walk.getVert (q.walk.length-2),r,?_⟩
    intro i hi
    have hl : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    calc
      r.walk.getVert (i+2*(n+1)) = r.walk.getVert ((i+2*n)+2) := by congr 1
      _ = q.walk.getVert (i+2*n) := hover _ (by omega)
      _ = p.walk.getVert i := hq _ (by omega)

include h e in
private theorem reverse_prefix_of_radius_escape
    (hb : 2 < sourceDistance h)
    (escape : ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
      q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have heven := sourceDistance_even h
  rw [Nat.even_iff] at heven
  let n := (p.walk.length-2)/2
  have hn : 2*n+2 = p.walk.length := by dsimp [n]; omega
  obtain ⟨d,d',q,hover⟩ := iterated_paths_of_radius_escape h hb escape p n (by omega)
  have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans hl.symm
  have hend : d' = p.walk.getVert 2 := by
    have hh := hover 2 (by omega)
    rw [show 2+2*n = q.walk.length by omega,q.walk.getVert_length] at hh
    exact hh
  let r : CriticalPath Rg (sourceGeometry h) d' d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        d q.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.start_color]
          exact sourceDistance_pos h) d' q.end_color q.critical⟩
  have hr1 : r.walk.getVert 1 = p.walk.getVert 1 := by
    change q.walk.reverse.getVert 1 = _
    rw [SimpleGraph.Walk.getVert_reverse,show q.walk.length-1 = 1+2*n by omega]
    exact hover 1 (by omega)
  have hr2 : r.walk.getVert 2 = a := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,show q.walk.length-2 = 0+2*n by omega,
      hover 0 (by omega),SimpleGraph.Walk.getVert_zero]
  have hh : ∃ r : CriticalPath Rg (sourceGeometry h) d' d,
      r.walk.getVert 1 = p.walk.getVert 1 ∧ r.walk.getVert 2 = a := ⟨r,hr1,hr2⟩
  rw [hend] at hh
  exact ⟨d,hh⟩

include h e hz hk in
/-- A large critical witness or a strict slice gives backward paths at every
component vertex, retaining the entire overlap. Iterating those very paths
also gives a reverse prefix and forward eligibility for every critical path. -/
theorem plane_paths_of_large_pair_or_strict_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hwitness : (∃ a z, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
        4 ≤ (Q Rg z).relIndex (Z Rg a)) ∨
      (∃ v c t : Vertex Rg, color Rg v = false ∧ Adjacent Rg v t ∧ Adjacent Rg c t ∧
        2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)))
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
  have escape : ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    intro a z p
    rcases hwitness with ⟨a₀,z₀,p₀,hlarge⟩ | ⟨v,c,t,hv,hvt,hct,hs⟩
    · exact plane_radius_escape_of_large_pair h e hz hk u hR p₀ hlarge p
    · exact plane_radius_escape_of_strict_slice h e hz hk u hR hv hvt hct hs p
  have hprefix := reverse_prefix_of_radius_escape h e hb escape p
  refine ⟨escape _ _ p,backward_path_of_radius_escape h p (escape _ _ p) hb,hprefix,?_⟩
  obtain ⟨d,q,_,hqa⟩ := hprefix
  have hh := critical_start_not_le_second_slice h e hz hb q
  rwa [hqa] at hh

omit hk in
include h e hz in
/-- Whole-core assembly separates the plane branch into actual backward and
forward critical paths, or uniformly small slices with exact full kernels.
The original Borel branch, cubic kernel and both full covers are retained. -/
theorem coreExhaustion_or_cubic_plane_radius_reduction :
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
        ((∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
          (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
          (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
            ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
              w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
            q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _)) ∨
        ((∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
          (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) ∧
          ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
            Z Rg z ⊓ B Rg (p.walk.getVert (p.walk.length-2))
                ((sourceGeometry h).Z_normal _) = Z Rg z ⊓ Q Rg a ∧
              (Q Rg a).relIndex (Z Rg z) = 2 ∧
              (Q Rg z).relIndex (Z Rg a) = 2))) := by
  classical
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hplane | hborel⟩
  · exact Or.inl hex
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    by_cases hw : (∃ a z, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
        4 ≤ (Q Rg z).relIndex (Z Rg a)) ∨
      (∃ v c t : Vertex Rg, color Rg v = false ∧ Adjacent Rg v t ∧ Adjacent Rg c t ∧
        2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    · exact Or.inl (fun a z p => plane_paths_of_large_pair_or_strict_slice h e hz hk u hplane hw p)
    · have hall : ∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
          (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
        intro v c t hv hvt hct
        by_contra! hh
        exact hw (Or.inr ⟨v,c,t,hv,hvt,hct,hh⟩)
      exact Or.inr ⟨hall,fun a z p => critical_kernel_of_uniform_slices h e hz hk hall p⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩

omit hk in
include h e hz in
/-- The literal C.1.32 consumer has the same plane radius alternatives on
its original cubic graph; no whole-core conclusion is assumed. -/
theorem rankTwo_or_cubic_plane_radius_reduction :
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
        ((∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
          (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
          (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
            ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
              w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
            q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _)) ∨
        ((∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
          (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) ∧
          ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
            Z Rg z ⊓ B Rg (p.walk.getVert (p.walk.length-2))
                ((sourceGeometry h).Z_normal _) = Z Rg z ⊓ Q Rg a ∧
              (Q Rg a).relIndex (Z Rg z) = 2 ∧
              (Q Rg z).relIndex (Z Rg a) = 2))) :=
  (coreExhaustion_or_cubic_plane_radius_reduction h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
