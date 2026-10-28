module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedSlices
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneFixedKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels

/-!
# Simultaneous shifted paths for the original cubic plane selector

At distance four, consider a small critical path a--z and its path under
the normalized component switch. Their midpoints c and c' are retained
separately. For an earlier critical path d--c through a, let K = Z_d
intersect Q_c. If K lies in Q_c', the full-omega control theorem and the
literal paired generation make K join Z_a normal in G_a. The original
normal-section theorem then identifies Z_d intersect B_a with K and gives
both the full-seed and moving-slice index two. This requires neither equal
midpoints nor equal first vertices of the two forward paths.

Assume the source's small critical images and a strict slice on an original
neighbor of the first edge. Transport that same slice to the selected edge.
If both midpoints contain its full seed, the existing paired control gives
central generation of omega. Otherwise an actual backward critical path
is obtained by prepending the selected two-edge walk. The kernel comparison
forces escape from the other midpoint core and constructs a second backward
critical path along the same earlier edge. All overlap vertices are retained.

The two full earlier kernels are distinct and have intersection index four.
Their joined endpoint seeds have image larger than two over Q_d: equal small
images would give equal commutator lines and hence equal kernels. Transport
the original first-edge partner to d and apply large-subactor generation.
This supplies both generating edge groups and generation by the actual
joined midpoint seeds at the same earlier vertex. The original component
switch, its two generation identities and its large joint endpoint image
are retained throughout.

The whole-core and literal C.1.32 consumers preserve both full moving covers,
the central attachments, and the cubic projection with kernel E, not Q.
Distance four, the small-critical-image premise and the strict slice remain
explicit. Central generation of full omega, the two end-slice bounds, the
remaining plane/Borel exclusions and both final core exhaustions are still
required; this is not the complete source (5.12).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)--(5.8) and the shifted-kernel comparison in (5.12)(3), printed
pp.917--920,926--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
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
private theorem plane_radius_subgroup_control_or_omega
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) (hYV : Y ≤ V Rg a)
    (hYc : Y ≤ Q Rg (p.walk.getVert 2)) :
    (X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) ∨
    ⁅Y,X Rg z⁆ ≤ Z Rg a := by
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hpr : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  rcases small_critical_omega_generation_or_control_at h e hz hk pr hpr with hg | hc
  · exact Or.inl hg
  right
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hcolor : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hYQ := hYV.trans
    ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)
  have hYG : Y ≤ stabilizer Rg z := hYc.trans
    (Q_le_stabilizer_of_dist_le_two _ z hcolor p.end_color (by rw [p.dist_end,hl]))
  have hline : ⁅X Rg z,Z Rg a⁆ ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_right.mp
      ((critical_X_le_vertex h e z p.end_color a pr.critical).trans (Z_normalized Rg a))
  have hZaX : Z Rg a ≤ X Rg a := (sourceGeometry h).omega_bound a p.start_color (by
    rw [(sourceGeometry h).distance_constant _ p.start_color]
    exact sourceDistance_pos h)
  have hfixed : Y ≤ centralizer ((⁅X Rg z,Z Rg a⁆ : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) :=
    (hYQ.trans (Q_le_centralizer_X Rg a)).trans (centralizer_le (hline.trans hZaX))
  exact (hc Y hYG hfixed).trans (sup_le hline
    ((commutator_mono hYV inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)))

include h e hz hk in
/-- The shifted midpoint may differ. Containment of the full earlier kernel
in its core, together with the literal paired generation, suffices for the
small-slice conclusion. -/
theorem plane_shifted_kernel_slice_or_omega
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a z z' c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hp' : (Q Rg z').relIndex (Z Rg a) < 4)
    (hq : (Q Rg c).relIndex (Z Rg d) < 4)
    (hgen : (Q Rg (q.walk.getVert 1) ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a)
    (hcross : Z Rg d ⊓ Q Rg c ≤ Q Rg (p'.walk.getVert 2)) :
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (stabilizer Rg a ≤ normalizer
        ((Z Rg d ⊓ Q Rg c ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg d ⊓ Q Rg c ∧
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 2 ∧
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 2) := by
  have finish (w : Vertex Rg) (hw : color Rg w = false)
      (hc : X Rg w = U Rg w ⊔
        (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg)))) :
      ∀ v : Vertex Rg, color Rg v = false →
        (X Rg v = U Rg v ⊔
          (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
        X Rg v = Z Rg v := by
    intro v hv
    have hh := omega_generation_transport hw hv hc
    exact ⟨hh,omega_eq_seed_of_central_generation h v hv hh⟩
  have hb := distance_gt_two h e hz hk
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  let K := Z Rg d ⊓ Q Rg c
  let N := K ⊔ Z Rg a
  let s := q.walk.getVert 1
  have has : Adjacent Rg a s := by
    rw [←hqa]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hKV : K ≤ V Rg a := inf_le_left.trans
    (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hKc : K ≤ Q Rg (p.walk.getVert 2) := by rw [hpc]; exact inf_le_right
  rcases plane_radius_subgroup_control_or_omega h e hz hk u hR hb4 p hp K hKV hKc with hc | hmove
  · exact Or.inl (finish z p.end_color hc)
  rcases plane_radius_subgroup_control_or_omega h e hz hk u hR hb4 p' hp' K hKV hcross with hc | hmove'
  · exact Or.inl (finish z' p'.end_color hc)
  right
  have hNV : N ≤ V Rg a := sup_le hKV (Z_le_VBall Rg _ 2)
  have hNG : N ≤ stabilizer Rg a :=
    hNV.trans ((sourceGeometry h).V_local _ p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact hb))
  have hKN : Q Rg s ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    plane_small_critical_first_edge_normalizes_kernel h e hz hk u hR q hq
  have hNs : Q Rg s ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hKN ((show Q Rg s ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg has)).trans (Z_normalized Rg _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have move {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) a w)
      (hm : ⁅K,X Rg w⁆ ≤ Z Rg a) :
      ⁅N,Z Rg w⁆ ≤ Z Rg a := by
    have hZX : Z Rg w ≤ X Rg w := (sourceGeometry h).omega_bound w r.end_color (by
      rw [(sourceGeometry h).distance_constant _ r.end_color]
      exact sourceDistance_pos h)
    apply commutator_sup_le_of_relative_normal (stabilizer Rg a)
      K (Z Rg a) (Z Rg w) (Z Rg a) (Z_normalized Rg _)
      (le_sup_left.trans hNG) (Z_le_stabilizer Rg _)
      ((commutator_mono le_rfl hZX).trans hm)
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpN := move p hmove
  have hpN' := move p' hmove'
  have hNn : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le (sup_le hNs
      (le_normalizer_iff_commutator_le_left.mpr (hpN.trans le_sup_right)))
      (le_normalizer_iff_commutator_le_left.mpr (hpN'.trans le_sup_right))
  have hKB : K ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (shifted_normalized_radius_le_slice h e hz hb p N hNV hNn hpN)
  let := finite_Z Rg d
  let : Finite (U Rg d) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
  have hindex : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ≤ 2 := by
    have hi := relIndex_le_of_le_left hKB
      (index_ne_zero_of_finite (H := K.subgroupOf (Z Rg d)))
    change (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) ≤
      (Z Rg d ⊓ Q Rg c).relIndex (Z Rg d) at hi
    rw [inf_relIndex_left,(small_critical_indices h e hz hk q hq).1] at hi
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite).trans hi
  let qr : CriticalPath Rg (sourceGeometry h) c d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],reverse_pair h e q⟩
  have hqra : qr.walk.getVert (qr.walk.length-2) = a := by
    change q.walk.reverse.getVert (q.walk.reverse.length-2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
    exact hqa
  have hslice := critical_predecessor_small_slice h e hz hk hb qr
    (by simpa only [hqra] using hindex)
  have heq : Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg d ⊓ Q Rg c := by
    simpa only [hqra] using hslice.1
  have hfull : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 2 := by
    rw [←inf_relIndex_left,heq,inf_relIndex_left,(small_critical_indices h e hz hk q hq).1]
  have hlo := critical_start_slice_index_two_le h e hz hb q
  rw [hqa] at hlo
  exact ⟨hNn,heq,hfull,Nat.le_antisymm hindex hlo⟩

include h e hz hk in
private theorem plane_strict_slice_second_backward
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {z z' d t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hq1 : q.walk.getVert 1 = t) (hq2 : q.walk.getVert 2 = alpha Rg)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hp' : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hgen : (Q Rg t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
      q'.walk.getVert 1 = t ∧
      (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
      ¬ Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ Q Rg (p'.walk.getVert 2)) := by
  have hb : 2 ≤ (sourceGeometry h).b Rg := by change 2 ≤ sourceDistance h; omega
  by_cases hc : Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ Q Rg (p'.walk.getVert 2)
  · rcases plane_shifted_kernel_slice_or_omega h e hz hk u hR hb4 p p' q rfl hq2
      hp hp' hq (by simpa only [hq1] using hgen) hc with hg | hb
    · exact Or.inl hg
    · rw [hb.2.2.2] at hs
      omega
  right
  have hn : ¬ Z Rg d ≤ Q Rg (p'.walk.getVert 2) := fun hh => hc (inf_le_left.trans hh)
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have hdt : Adjacent Rg d t := by
    rw [←hq1]
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hta : Adjacent Rg t (alpha Rg) := by
    simpa only [hq1,hq2] using
      (cosetGraph_adj Rg _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega))
  let w : (cosetGraph Rg).Walk d (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hdt)
      (.cons ((cosetGraph_adj Rg _ _).mpr hta) .nil)
  have hw : w.length = 2 := rfl
  have hns : ¬ Z Rg d ≤ Q Rg (p'.walk.getVert (p'.walk.length-2)) := by
    simpa only [hl',Nat.reduceSub] using hn
  let q' := p'.prepend_two hb q.start_color w hw hns
  have he : p'.walk.getVert (p'.walk.length-2) = p'.walk.getVert 2 := by rw [hl']
  have hresult : ∃ r : CriticalPath Rg (sourceGeometry h) d
      (p'.walk.getVert (p'.walk.length-2)),
      r.walk.getVert 1 = t ∧ ∀ i ≤ 2, r.walk.getVert (i+2) = p'.walk.getVert i := by
    refine ⟨q',?_,?_⟩
    · change (p'.prepend_two _ _ _ _ _).walk.getVert 1 = t
      rw [p'.prepend_two_walk]
      simp only [SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    · intro i hi
      exact p'.prepend_two_overlap _ _ _ _ _ (by omega)
  rw [he] at hresult
  obtain ⟨r,hr1,hrv⟩ := hresult
  exact ⟨r,hr1,hrv,hc⟩

include h e hz hk in
private theorem plane_paired_backward_configuration
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z z' d t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hat : Adjacent Rg (alpha Rg) t) (hdt : Adjacent Rg d t)
    (hgen : (Q Rg t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
      q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = t ∧
      (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
      Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (p'.walk.getVert 2) ∧
      ((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
        (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))).relIndex (Z Rg d) = 4) := by
  have hb : 2 ≤ (sourceGeometry h).b Rg := by change 2 ≤ sourceDistance h; omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have hd : color Rg d = false := by
    have h₁ := adjacent_color_ne Rg hat
    have h₂ := adjacent_color_ne Rg hdt
    change false ≠ color Rg t at h₁
    cases he : color Rg d <;> cases ht : color Rg t <;> simp_all
  have extend {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hn : ¬ Z Rg d ≤ Q Rg (r.walk.getVert 2)) :
      ∃ q : CriticalPath Rg (sourceGeometry h) d (r.walk.getVert 2),
        q.walk.getVert 1 = t ∧ ∀ i ≤ 2, q.walk.getVert (i+2) = r.walk.getVert i := by
    have hrl : r.walk.length = 4 := r.length_eq_b.trans hb4
    let w₀ : (cosetGraph Rg).Walk d (alpha Rg) :=
      .cons ((cosetGraph_adj Rg _ _).mpr hdt)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
    have hw : w₀.length = 2 := rfl
    have hns : ¬ Z Rg d ≤ Q Rg (r.walk.getVert (r.walk.length-2)) := by
      simpa only [hrl,Nat.reduceSub] using hn
    let q := r.prepend_two hb hd w₀ hw hns
    have he : r.walk.getVert (r.walk.length-2) = r.walk.getVert 2 := by rw [hrl]
    have hr : ∃ q : CriticalPath Rg (sourceGeometry h) d
        (r.walk.getVert (r.walk.length-2)),
        q.walk.getVert 1 = t ∧ ∀ i ≤ 2, q.walk.getVert (i+2) = r.walk.getVert i := by
      refine ⟨q,?_,?_⟩
      · change (r.prepend_two _ _ _ _ _).walk.getVert 1 = t
        rw [r.prepend_two_walk]
        simp only [SimpleGraph.Walk.getVert_append,
          hw,show 1<2 from by decide,ite_true,w₀,SimpleGraph.Walk.getVert_cons_succ,
          SimpleGraph.Walk.getVert_zero]
      · intro i hi
        exact r.prepend_two_overlap _ _ _ _ _ (by omega)
    rwa [he] at hr
  have finish {v w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) v)
      (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (q : CriticalPath Rg (sourceGeometry h) d (r.walk.getVert 2))
      (q' : CriticalPath Rg (sourceGeometry h) d (s.walk.getVert 2))
      (hne : ¬ Z Rg d ⊓ Q Rg (r.walk.getVert 2) ≤ Q Rg (s.walk.getVert 2)) :
      Z Rg d ⊓ Q Rg (r.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (s.walk.getVert 2) ∧
      ((Z Rg d ⊓ Q Rg (r.walk.getVert 2)) ⊓
        (Z Rg d ⊓ Q Rg (s.walk.getVert 2))).relIndex (Z Rg d) = 4 := by
    have hneq : Z Rg d ⊓ Q Rg (r.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (s.walk.getVert 2) :=
      fun he => hne (he ▸ inf_le_right)
    let := finite_Z Rg d
    refine ⟨hneq,intersection_index_four _ _ _ inf_le_left inf_le_left ?_ ?_ hneq⟩
    · rw [inf_relIndex_left]
      exact (small_critical_indices h e hz hk q (hsmall _ _ q)).1
    · rw [inf_relIndex_left]
      exact (small_critical_indices h e hz hk q' (hsmall _ _ q')).1
  by_cases hn : Z Rg d ≤ Q Rg (p.walk.getVert 2)
  · by_cases hn' : Z Rg d ≤ Q Rg (p'.walk.getVert 2)
    · apply Or.inl
      apply plane_paired_trapped_omega_generation h e hz hk u hR p p'
        (hsmall _ _ p) (hsmall _ _ p') hat hdt
        (by rwa [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat])
        (by simpa only [hl,Nat.reduceSub] using hn)
        (by simpa only [hl',Nat.reduceSub] using hn') hs
    obtain ⟨q',hq1,hqv⟩ := extend p' hn'
    have hq2 : q'.walk.getVert 2 = alpha Rg := by simpa using hqv 0 (by omega)
    have hgens : (Q Rg t ⊔ Z Rg z') ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
      simpa only [sup_assoc,sup_comm,sup_left_comm] using hgen
    rcases plane_strict_slice_second_backward h e hz hk u hR hb4 p' p q' hq1 hq2
      (hsmall _ _ p') (hsmall _ _ p) (hsmall _ _ q') hgens hs with hg | ⟨q,hr1,hrv,hne⟩
    · exact Or.inl hg
    · have hf := finish p' p q' q hne
      exact Or.inr ⟨q,q',hr1,hq1,hrv,hqv,Ne.symm hf.1,by simpa only [inf_comm] using hf.2⟩
  · obtain ⟨q,hq1,hqv⟩ := extend p hn
    have hq2 : q.walk.getVert 2 = alpha Rg := by simpa using hqv 0 (by omega)
    rcases plane_strict_slice_second_backward h e hz hk u hR hb4 p p' q hq1 hq2
      (hsmall _ _ p) (hsmall _ _ p') (hsmall _ _ q) hgen hs with hg | ⟨q',hr1,hrv,hne⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q,q',hq1,hr1,hqv,hrv,finish p p' q q' hne⟩

include h e hz hk in
/-- Distinct full kernels of two small critical paths force a joint endpoint
image larger than two over the actual starting two-core. -/
theorem small_critical_distinct_kernels_joint_image
    {a z z' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hp' : (Q Rg z').relIndex (Z Rg a) < 4)
    (hne : Z Rg a ⊓ Q Rg z ≠ Z Rg a ⊓ Q Rg z') :
    2 < (Q Rg a).relIndex (Z Rg z ⊔ Z Rg z') := by
  have hQG : Q Rg a ≤ stabilizer Rg a := fun _ hx => hx.1
  have hpG := critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
    (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h) p.critical
  have hpG' := critical_Z_le_stabilizer Rg (sourceGeometry h) a p'.start_color
    (by rw [(sourceGeometry h).distance_constant a p'.start_color]; exact sourceDistance_pos h) p'.critical
  let W := Q Rg a ⊔ (Z Rg z ⊔ Z Rg z')
  have hWG : W ≤ stabilizer Rg a := sup_le hQG (sup_le hpG hpG')
  let := finite_stabilizer Rg a
  let : Finite W := Finite.of_injective (inclusion hWG) (inclusion_injective _)
  have idx (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg a) :
      (Q Rg a).relIndex (Q Rg a ⊔ A) = (Q Rg a).relIndex A := by
    let : ((Q Rg a).subgroupOf (stabilizer Rg a)).Normal :=
      normal_subgroupOf_of_le_normalizer (Q_normalized Rg a)
    have hh := relIndex_sup_left (A.subgroupOf (stabilizer Rg a))
      ((Q Rg a).subgroupOf (stabilizer Rg a))
    rw [←subgroupOf_sup hQG hAG,relIndex_subgroupOf (sup_le hQG hAG),
      relIndex_subgroupOf hAG] at hh
    exact hh
  by_contra! hle
  have hW : (Q Rg a).relIndex W ≤ 2 := by
    rw [idx _ (sup_le hpG hpG')]
    exact hle
  have join (A : Subgroup (FreeAmalgam Rg)) (hAW : A ≤ Z Rg z ⊔ Z Rg z')
      (hi : (Q Rg a).relIndex A = 2) : Q Rg a ⊔ A = W := by
    have hleW : Q Rg a ⊔ A ≤ W := sup_le le_sup_left (hAW.trans le_sup_right)
    have hm := relIndex_mul_relIndex (Q Rg a) (Q Rg a ⊔ A) W le_sup_left hleW
    rw [idx A (hAW.trans (sup_le hpG hpG')),hi] at hm
    have hpos : 0 < (Q Rg a ⊔ A).relIndex W := Nat.pos_of_ne_zero index_ne_zero_of_finite
    exact le_antisymm hleW (relIndex_eq_one.mp (by omega))
  have he : Q Rg a ⊔ Z Rg z = Q Rg a ⊔ Z Rg z' :=
    (join _ le_sup_left (small_critical_indices h e hz hk p hp).2).trans
      (join _ le_sup_right (small_critical_indices h e hz hk p' hp').2).symm
  have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color))
  have hline : ⁅Z Rg a,Z Rg z⁆ = ⁅Z Rg a,Z Rg z'⁆ :=
    (commutator_eq_of_centralizing_sup rfl hQC (hpG.trans (Z_normalized Rg a))).trans
      ((congrArg (fun A => ⁅Z Rg a,A⁆) he).trans
        (commutator_eq_of_centralizing_sup rfl hQC (hpG'.trans (Z_normalized Rg a))).symm)
  exact hne (small_critical_equal_lines_kernels h e hz hk p p' hp hp' hline)

include h e hz hk in
private theorem plane_small_critical_first_edge_partner
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ s, Adjacent Rg a s ∧
      Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color Rg p.start_color
  have hback : act Rg g⁻¹ a = alpha Rg := by
    rw [hga]
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have hreturn : act Rg g (alpha Rg) = a := by
    rw [←hback,←act_mul,inv_mul_cancel,act_one]
  have hcancel (v : Vertex Rg) : act Rg g (act Rg g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hpaths : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      ∀ i, p₀.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i) :=
    ⟨p.act g⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hback] at hpaths
  obtain ⟨p₀,hverts⟩ := hpaths
  have hp₀ : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hback,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hp
  obtain ⟨s,has,_,_,_,_,hfirst,_⟩ :=
    plane_small_critical_subactor_selectors h e hz hk u hR p₀ hp₀
  have hadj : Adjacent Rg a (act Rg g s) := by
    rw [←hreturn]
    exact (adjacent_act_iff Rg g _ _).mpr has
  refine ⟨act Rg g s,hadj,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hfirst
  rwa [Subgroup.map_sup,←Q_act,←Q_act,←stabilizer_act,hverts 1,hcancel,hreturn] at hh

include h e hz hk in
private theorem plane_paired_midpoints_generate
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {d c c' t : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (q' : CriticalPath Rg (sourceGeometry h) d c')
    (hq1 : q.walk.getVert 1 = t) (hq1' : q'.walk.getVert 1 = t)
    (hq : (Q Rg c).relIndex (Z Rg d) < 4)
    (hlarge : 2 < (Q Rg d).relIndex (Z Rg c ⊔ Z Rg c')) :
    ∃ s, Adjacent Rg d s ∧ Q Rg s ⊔ Q Rg t = stabilizer Rg d ∧
      Q Rg s ⊔ (Z Rg c ⊔ Z Rg c') = stabilizer Rg d := by
  obtain ⟨s,hds,hpair⟩ := plane_small_critical_first_edge_partner h e hz hk u hR q hq
  rw [hq1] at hpair
  have hdt : Adjacent Rg d t := by
    rw [←hq1]
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (q.length_eq_b ▸ sourceDistance_pos h)
  have endpoint {w : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) d w)
      (hr1 : r.walk.getVert 1 = t) : Z Rg w ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w r.end_color)
    rw [←hr1,SimpleGraph.dist_comm,r.dist_end,
      (sourceGeometry h).distance_constant w r.end_color]
    change r.walk.length-1 < sourceDistance h
    have hl : r.walk.length = sourceDistance h := r.length_eq_b
    have hb := sourceDistance_pos h
    omega
  exact ⟨s,hds,hpair,plane_edge_pair_large_subactor_generates h e hz hk u hR
    q.start_color hds hdt hpair _ (sup_le (endpoint q hq1) (endpoint q' hq1')) hlarge⟩

include h e hz hk in
/-- Construct the simultaneous earlier paths from the original normalized
selector. Small critical images and a strict slice force distinct earlier
kernels and a large joint midpoint image, unless full omega is centrally
generated. No equality of the switched midpoints is assumed. -/
theorem plane_small_critical_shifted_configuration
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        2 < (Q Rg (alpha Rg)).relIndex (Z Rg z ⊔ Z Rg (act Rg x z)) ∧
        x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
            q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = t ∧
            (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
            Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (p'.walk.getVert 2) ∧
            ((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))).relIndex (Z Rg d) = 4 ∧
            2 < (Q Rg d).relIndex (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) ∧
            ∃ s, Adjacent Rg d s ∧ Q Rg s ⊔ Q Rg t = stabilizer Rg d ∧
              Q Rg s ⊔ (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) = stabilizer Rg d) := by
  obtain ⟨t,hat,r,hr,p',hverts,hps,hgen,hpair,hnorm,hinside,hneqOriginal,_,_,_,_,_,_,htransport⟩ :=
    remaining_small_critical_paired_kernel_selectors h e hz hk u (Or.inl hR) p (hsmall _ _ p)
  obtain ⟨g,hg,hgt,hstrict,_⟩ := htransport delta hd hs
  let x := (embedM Rg r)⁻¹
  let d := act Rg g delta
  have hdt : Adjacent Rg d t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  have hat₀ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat'] at hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat₀] at hnorm hinside
  rcases plane_paired_backward_configuration h e hz hk u hR hb4 hsmall p p'
    hat hdt hgen hstrict with hc | ⟨q,q',hq1,hq1',hqv,hqv',hne,hindex⟩
  · exact Or.inl hc
  · have hlarge := small_critical_distinct_kernels_joint_image h e hz hk q q'
      (hsmall _ _ q) (hsmall _ _ q') hne
    exact Or.inr ⟨t,hat,r,hr,p',hverts,hgen,hpair,
      small_critical_distinct_kernels_joint_image h e hz hk p p' (hsmall _ _ p) hps hneqOriginal,
      hnorm,hinside,g,hg,hgt,hstrict,
      q,q',hq1,hq1',hqv,hqv',hne,hindex,hlarge,
      plane_paired_midpoints_generate h e hz hk u hR q q' hq1 hq1' (hsmall _ _ q) hlarge⟩

omit hk in
include h e hz in
/-- Whole-core application constructing the paired backward paths and their
large joint image from the retained small-image premise and a strict slice. -/
theorem coreExhaustion_or_cubic_plane_shifted_configuration :
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
          ∀ z delta (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            Adjacent Rg delta (p.walk.getVert 1) →
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        2 < (Q Rg (alpha Rg)).relIndex (Z Rg z ⊔ Z Rg (act Rg x z)) ∧
        x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
            q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = t ∧
            (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
            Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (p'.walk.getVert 2) ∧
            ((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))).relIndex (Z Rg d) = 4 ∧
            2 < (Q Rg d).relIndex (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) ∧
            ∃ s, Adjacent Rg d s ∧ Q Rg s ⊔ Q Rg t = stabilizer Rg d ∧
              Q Rg s ⊔ (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) = stabilizer Rg d))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall _ _ p hd hstrict =>
        plane_small_critical_shifted_configuration h e hz hk u hplane hb4 hsmall p hd hstrict⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, preserving the original projection and both
full covers. The small-image and central-omega branches remain explicit. -/
theorem rankTwo_or_cubic_plane_shifted_configuration :
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
          ∀ z delta (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            Adjacent Rg delta (p.walk.getVert 1) →
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        2 < (Q Rg (alpha Rg)).relIndex (Z Rg z ⊔ Z Rg (act Rg x z)) ∧
        x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
            q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = t ∧
            (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
            Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (p'.walk.getVert 2) ∧
            ((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))).relIndex (Z Rg d) = 4 ∧
            2 < (Q Rg d).relIndex (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) ∧
            ∃ s, Adjacent Rg d s ∧ Q Rg s ⊔ Q Rg t = stabilizer Rg d ∧
              Q Rg s ⊔ (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) = stabilizer Rg d))) :=
  (coreExhaustion_or_cubic_plane_shifted_configuration h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
