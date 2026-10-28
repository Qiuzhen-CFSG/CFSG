module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCriticalSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedSlices

/-!
# Paired full-kernel slices after raw critical comparison

Take two normalized critical paths with the same starting vertex, generating
midpoint edges and strict backward midpoint slices. The raw comparison controls
their common backward full kernel against both endpoint seeds. Its join with
the starting seed is therefore normalized by the literal joint generators.
The normal-radius theorem puts this common kernel in the Baumann subgroup.
This argument retains the full central attachment on both moving covers.

A strict opposite slice now forces both raw preceding walks to be critical.
Their full kernels intersect exactly in the shared edge seed, generate the
whole backward seed and have joint endpoint image larger than two. The actual
original backward selector supplies the midpoint generation and backward
slice. Its output is a small opposite slice or this simultaneous pair; it
requires no extra next-path or next-slice premise.

The whole-core and literal C.1.32 applications keep the original projection
with kernel E and its nontrivial odd E/Q, and the original proper radical.
This is an intermediate reduction toward MS93 (5.12)(3). Excluding the
remaining paired configuration and completing the small-slice terminal
argument, the other distance/Borel branches and both core exhaustions are
still necessary for the unconditional reconstruction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(1)--(3), printed pp.924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped Pointwise IsMulCommutative commutatorElement
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
private theorem raw_preceding_critical_path
    (hb4 : sourceDistance h = 4)
    {a z d s : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (has : Adjacent Rg a s) (hds : Adjacent Rg d s)
    (hn : ¬ Z Rg d ≤ Q Rg (p.walk.getVert 2)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      q.walk.getVert 1 = s ∧ ∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb := distance_gt_two h e hz hk
  have hd : color Rg d = false := by
    have h₁ := adjacent_color_ne Rg has
    have h₂ := adjacent_color_ne Rg hds
    rw [p.start_color] at h₁
    cases he : color Rg d <;> cases ht : color Rg s <;> simp_all
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  let w : (cosetGraph Rg).Walk d a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hds)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg has)) .nil)
  have hw : w.length = 2 := rfl
  have hns : ¬ Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hn
  let q := p.prepend_two (Nat.le_of_lt hb) hd w hw hns
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  have hr : ∃ q : CriticalPath Rg (sourceGeometry h) d
      (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = s ∧ ∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q,?_,?_⟩
    · simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    · intro i hi
      exact p.prepend_two_overlap _ _ _ _ _ (by omega)
  rwa [he] at hr

include h e hz hk in
private theorem raw_preceding_kernel_normalized
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d s : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (has : Adjacent Rg a s) (hds : Adjacent Rg d s) :
    Q Rg s ≤ normalizer ((Z Rg d ⊓ Q Rg (p.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) ≤ 2 := by
  by_cases hn : Z Rg d ≤ Q Rg (p.walk.getVert 2)
  · rw [inf_eq_left.mpr hn,relIndex_eq_one.mpr hn]
    exact ⟨(show Q Rg s ≤ stabilizer Rg d from
      fun _ hv => hv.2 _ (adjacent_symm Rg hds)).trans (Z_normalized Rg d),by decide⟩
  obtain ⟨q,hq1,_⟩ := raw_preceding_critical_path h e hz hk hb4 p has hds hn
  have hh := plane_small_critical_first_edge_normalizes_kernel h e hz hk u hR q (hsmall _ _ q)
  rw [hq1] at hh
  exact ⟨hh,((small_critical_indices h e hz hk q (hsmall _ _ q)).1).le⟩

include h e hz hk in
/-- The common full kernel of two raw preceding walks lies in the literal
Baumann subgroup. Only the two original paths are assumed critical. -/
theorem plane_raw_paired_kernel_le_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z z' d s : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (has : Adjacent Rg a s) (hds : Adjacent Rg d s)
    (hgen : (Q Rg s ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a)
    (hfirst : Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a)
    (hfirst' : Q Rg s ⊔ Q Rg (p'.walk.getVert 1) = stabilizer Rg a)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgd : act Rg g (p.walk.getVert 2) = d)
    (g' : FreeAmalgam Rg) (hg' : g' ∈ stabilizer Rg a)
    (hgd' : act Rg g' (p'.walk.getVert 2) = d)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hmid' : Q Rg (p'.walk.getVert 1) ⊔ Q Rg (p'.walk.getVert 3) =
      stabilizer Rg (p'.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a))
    (hback' : 2 < (B Rg (p'.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)) :
    let I := (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
      (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))
    stabilizer Rg a ≤ normalizer ((I ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      I ≤ B Rg a ((sourceGeometry h).Z_normal _) ∧ I.relIndex (Z Rg d) ≤ 4 := by
  let I := (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
    (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))
  let N := I ⊔ Z Rg a
  have hb := distance_gt_two h e hz hk
  let w : (cosetGraph Rg).Walk d a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hds)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg has)) .nil)
  have hda : (cosetGraph Rg).dist d a ≤ 2 := (cosetGraph Rg).dist_le w
  have hIV : I ≤ V Rg a := (inf_le_left.trans inf_le_left).trans
    (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hIG : I ≤ stabilizer Rg a :=
    hIV.trans ((sourceGeometry h).V_local a p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact hb))
  have hn := raw_preceding_kernel_normalized h e hz hk u hR hb4 hsmall p has hds
  have hn' := raw_preceding_kernel_normalized h e hz hk u hR hb4 hsmall p' has hds
  have hIN : Q Rg s ≤ normalizer (I : Set (FreeAmalgam Rg)) :=
    (le_inf hn.1 hn'.1).trans inf_normalizer_le_normalizer_inf
  have hNs : Q Rg s ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hIN ((show Q Rg s ≤ stabilizer Rg a from
      fun _ hv => hv.2 _ (adjacent_symm Rg has)).trans (Z_normalized Rg a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hm := (plane_raw_shifted_kernels_of_midpoint_generation h e hz hk u hR hb4 hsmall
    p hds has I inf_le_left hfirst g hg hgd hmid hback).2
  have hm' := (plane_raw_shifted_kernels_of_midpoint_generation h e hz hk u hR hb4 hsmall
    p' hds has I inf_le_right hfirst' g' hg' hgd' hmid' hback').2
  have move {v : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) a v)
      (hm : ⁅I,Z Rg v⁆ ≤ ⁅Z Rg a,Z Rg v⁆) : ⁅N,Z Rg v⁆ ≤ Z Rg a := by
    have hline : ⁅Z Rg a,Z Rg v⁆ ≤ Z Rg a :=
      le_normalizer_iff_commutator_le_left.mp
        ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
          (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
          r.critical).trans (Z_normalized Rg a))
    exact commutator_sup_le_of_relative_normal (stabilizer Rg a) I (Z Rg a)
      (Z Rg v) (Z Rg a) (Z_normalized Rg a) hIG (Z_le_stabilizer Rg a)
      (hm.trans hline) hline
  have hNm := move p hm
  have hNm' := move p' hm'
  have hNG : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le (sup_le hNs
      (le_normalizer_iff_commutator_le_left.mpr (hNm.trans le_sup_right)))
      (le_normalizer_iff_commutator_le_left.mpr (hNm'.trans le_sup_right))
  have hNB : N ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
    shifted_normalized_radius_le_slice h e hz hb p N
      (sup_le hIV (Z_le_VBall Rg a 2)) hNG hNm
  refine ⟨hNG,le_sup_left.trans hNB,?_⟩
  have hi : I.relIndex (Z Rg d) ≤
      (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) *
        (Q Rg (p'.walk.getVert 2)).relIndex (Z Rg d) := by
    simpa only [inf_relIndex_left] using
      (relIndex_inf_le (H := Z Rg d ⊓ Q Rg (p.walk.getVert 2))
        (K := Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) (L := Z Rg d))
  exact hi.trans (Nat.mul_le_mul hn.2 hn'.2)

include h e hz hk in
private theorem raw_paired_paths_of_strict_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z z' d s : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (has : Adjacent Rg a s) (hds : Adjacent Rg d s)
    (hIB : (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
      (Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) ≤ B Rg a ((sourceGeometry h).Z_normal _))
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
        q.walk.getVert 1 = s ∧ q'.walk.getVert 1 = s ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
        (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
          (Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) = Z Rg s ∧
        (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔
          (Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) = Z Rg d ∧
        Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (p'.walk.getVert 2) := by
  let K := Z Rg d ⊓ Q Rg (p.walk.getVert 2)
  let K' := Z Rg d ⊓ Q Rg (p'.walk.getVert 2)
  let I := K ⊓ K'
  have hb := distance_gt_two h e hz hk
  have hd : color Rg d = false := by
    have h₁ := adjacent_color_ne Rg has
    have h₂ := adjacent_color_ne Rg hds
    rw [p.start_color] at h₁
    cases he : color Rg d <;> cases ht : color Rg s <;> simp_all
  have hsB := plane_strict_slice_eq_edge h e hz hk u hR p.start_color hd has hds hs
  have edge {v : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) a v) :
      Z Rg s ≤ Z Rg d ⊓ Q Rg (r.walk.getVert 2) := by
    have hl : r.walk.length = 4 := r.length_eq_b.trans hb4
    refine le_inf (adjacent_Z_le Rg hd hds) ((adjacent_Z_le Rg p.start_color has).trans ?_)
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
    rw [(sourceGeometry h).distance_constant a p.start_color,r.dist_start (by omega)]
    exact hb
  have hI : I = Z Rg s :=
    le_antisymm ((le_inf (inf_le_left.trans inf_le_left) hIB).trans_eq hsB.1)
      (le_inf (edge p) (edge p'))
  have hi : I.relIndex (Z Rg d) = 4 := by
    rw [hI,←hsB.1,inf_relIndex_left,hsB.2.2.1]
  have hn : ¬ Z Rg d ≤ Q Rg (p.walk.getVert 2) := by
    intro hn
    have hh := (raw_preceding_kernel_normalized h e hz hk u hR hb4 hsmall p' has hds).2
    have he : I = K' := by
      dsimp only [I,K,K']
      rw [inf_eq_left.mpr hn,inf_eq_right.mpr inf_le_left]
    rw [he,show K'.relIndex (Z Rg d) =
      (Q Rg (p'.walk.getVert 2)).relIndex (Z Rg d) from inf_relIndex_left _ _] at hi
    omega
  have hn' : ¬ Z Rg d ≤ Q Rg (p'.walk.getVert 2) := by
    intro hn'
    have hh := (raw_preceding_kernel_normalized h e hz hk u hR hb4 hsmall p has hds).2
    have he : I = K := by
      dsimp only [I,K,K']
      rw [inf_eq_left.mpr hn',inf_eq_left.mpr inf_le_left]
    rw [he,show K.relIndex (Z Rg d) =
      (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) from inf_relIndex_left _ _] at hi
    omega
  obtain ⟨q,hq1,hqv⟩ := raw_preceding_critical_path h e hz hk hb4 p has hds hn
  obtain ⟨q',hq1',hqv'⟩ := raw_preceding_critical_path h e hz hk hb4 p' has hds hn'
  have hiK : K.relIndex (Z Rg d) = 2 := by
    rw [show K = Z Rg d ⊓ Q Rg (p.walk.getVert 2) from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk q (hsmall _ _ q)).1
  have hiK' : K'.relIndex (Z Rg d) = 2 := by
    rw [show K' = Z Rg d ⊓ Q Rg (p'.walk.getVert 2) from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk q' (hsmall _ _ q')).1
  have hne : K ≠ K' := by
    intro he
    have hIK : I = K := by change K ⊓ K' = K; rw [he,inf_idem]
    rw [hIK,hiK] at hi
    omega
  have hnot : ¬ K' ≤ K := by
    intro hle
    have hm := relIndex_mul_relIndex K' K (Z Rg d) hle inf_le_left
    rw [hiK,hiK'] at hm
    exact hne (le_antisymm (relIndex_eq_one.mp (by omega)) hle)
  have hj := relIndex_mul_relIndex K (K ⊔ K') (Z Rg d) le_sup_left
    (sup_le inf_le_left inf_le_left)
  rw [hiK] at hj
  have hjn : K.relIndex (K ⊔ K') ≠ 1 := fun he =>
    hnot (le_sup_right.trans (relIndex_eq_one.mp he))
  have hout : (K ⊔ K').relIndex (Z Rg d) = 1 := by
    rcases Nat.prime_mul_iff.mp (hj ▸ Nat.prime_two) with hh | hh
    · exact hh.2
    · exact (hjn hh.2).elim
  exact ⟨q,q',hq1,hq1',hqv,hqv',hI,
    le_antisymm (sup_le inf_le_left inf_le_left) (relIndex_eq_one.mp hout),hne⟩

include h e hz hk in
private theorem normalized_plane_selectors_at
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ s, Adjacent Rg a s ∧ ∃ x ∈ stabilizer Rg a,
      (Q Rg s ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg a ∧
      Q Rg s ⊔ Q Rg (act Rg x s) = stabilizer Rg a ∧
      x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
      Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) := by
  have base {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
      (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
      ∃ s, Adjacent Rg (alpha Rg) s ∧ ∃ x ∈ stabilizer Rg (alpha Rg),
        (Q Rg s ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg s ⊔ Q Rg (act Rg x s) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) := by
    obtain ⟨s,has,r,hr,hgen,hpair,hfix,hnorm,hinside,hcomm⟩ :=
      remaining_small_critical_normalized_plane_selectors h e hz hk u (Or.inl hR) p hp
    let x := (embedM Rg r)⁻¹
    have hx : x ∈ stabilizer Rg (alpha Rg) := by
      change x ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨r⁻¹,by rw [map_inv]⟩
    have hav : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
      apply (cosetGraph_adj Rg _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using
        p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
    have has' : Adjacent Rg (alpha Rg) (act Rg x s) := by
      simpa only [show act Rg x (alpha Rg) = alpha Rg from hx] using
        (adjacent_act_iff Rg x _ _).mpr has
    rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl has] at hgen hpair
    rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl has'] at hpair
    rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hav] at hnorm hinside
    exact ⟨s,has,x,hx,hgen,hpair,hnorm,hinside⟩
  obtain ⟨f,ha⟩ := exists_mVertex_of_color Rg p.start_color
  have hfa : act Rg f (alpha Rg) = a := by
    simpa only [alpha,act_mVertex,one_mul] using ha.symm
  have hfia : act Rg f⁻¹ a = alpha Rg := by
    rw [←hfa,←act_mul,mul_inv_cancel,act_one]
  have hp0 : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg f⁻¹ a) (act Rg f⁻¹ z),
      ∀ i, p₀.walk.getVert i = act Rg f⁻¹ (p.walk.getVert i) :=
    ⟨p.act f⁻¹,fun _ => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hfia] at hp0
  obtain ⟨p₀,hverts⟩ := hp0
  have hp₀ : (Q Rg (act Rg f⁻¹ z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hfia,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hp
  obtain ⟨s₀,has₀,x₀,hx₀,hgen,hpair,hnorm,hinside⟩ := base p₀ hp₀
  let x := (MulAut.conj f⁻¹) x₀
  have hcancel (v : Vertex Rg) : act Rg f (act Rg f⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have htransport (v : Vertex Rg) : act Rg f (act Rg x₀ v) = act Rg x (act Rg f v) := by
    rw [←act_mul,←act_mul]
    congr 1
    simp only [x,MulAut.conj_apply,inv_inv]
    group
  have hx : x ∈ stabilizer Rg a := by
    have hh := mem_map_of_mem (MulAut.conj f⁻¹).toMonoidHom hx₀
    rwa [←stabilizer_act,hfa] at hh
  have has : Adjacent Rg a (act Rg f s₀) := by
    rw [←hfa]
    exact (adjacent_act_iff Rg f _ _).mpr has₀
  have hgen' := congrArg (Subgroup.map (MulAut.conj f⁻¹).toMonoidHom) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,←Q_act,←Z_act,←Z_act,←stabilizer_act,
    hfa,hcancel,htransport,hcancel] at hgen'
  have hpair' := congrArg (Subgroup.map (MulAut.conj f⁻¹).toMonoidHom) hpair
  rw [Subgroup.map_sup,←Q_act,←Q_act,←stabilizer_act,hfa,htransport] at hpair'
  have hnorm' := (Q Rg (p₀.walk.getVert 1)).le_normalizer_map
    (MulAut.conj f⁻¹).toMonoidHom (mem_map_of_mem _ hnorm)
  rw [←Q_act,hverts 1,hcancel] at hnorm'
  have hinside' := map_mono (f := (MulAut.conj f⁻¹).toMonoidHom) hinside
  rw [Subgroup.map_sup,←Z_act,←Z_act,←Q_act,hverts 1,hcancel,htransport,hcancel] at hinside'
  rw [hcancel] at hinside'
  exact ⟨act Rg f s₀,has,x,hx,hgen',hpair',hnorm',hinside'⟩

include h e hz hk in
/-- The normalized selector on a path with generating midpoint edges and
strict reciprocal slices supplies two simultaneous backward critical paths.
Their full kernels meet in the preceding edge seed and generate its full seed. -/
theorem plane_strict_reciprocal_paired_critical_kernels
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a))
    (hforward : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2))) :
    ∃ s, Adjacent Rg a s ∧ ∃ x ∈ stabilizer Rg a,
      (Q Rg s ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg a ∧
      Q Rg s ⊔ Q Rg (act Rg x s) = stabilizer Rg a ∧
      Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a ∧
      ∃ p' : CriticalPath Rg (sourceGeometry h) a (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        ∃ g ∈ stabilizer Rg a, act Rg g (p.walk.getVert 1) = s ∧
          let d := act Rg g (p.walk.getVert 2)
          ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
            ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
              q.walk.getVert 1 = s ∧ q'.walk.getVert 1 = s ∧
              (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
              (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
              (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
                (Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) = Z Rg s ∧
              (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔
                (Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) = Z Rg d ∧
              2 < (Q Rg d).relIndex (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨s,has,x,hx,hgen,hpair,hnorm,hinside⟩ :=
    normalized_plane_selectors_at h e hz hk u hR p (hsmall _ _ p)
  have hfirst : Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg has))
        (fun _ hv => hv.2 _ (adjacent_symm Rg hav))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hxa : act Rg x a = a := hx
  have hpx : ∃ p' : CriticalPath Rg (sourceGeometry h) (act Rg x a) (act Rg x z),
      ∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i) :=
    ⟨p.act x,fun _ => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa] at hpx
  obtain ⟨p',hverts⟩ := hpx
  have hmid' : Q Rg (p'.walk.getVert 1) ⊔ Q Rg (p'.walk.getVert 3) =
      stabilizer Rg (p'.walk.getVert 2) := by
    rw [hverts 1,hverts 3,hverts 2,Q_act,Q_act,stabilizer_act,←Subgroup.map_sup,hmid]
  have hU : U Rg a = (U Rg a).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [←U_act,hxa]
  have hback' : 2 < (B Rg (p'.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) := by
    rw [hverts 2,Escape.PairingControl.FirstPairing.B_act hb x _ hc,hU,
      relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hback
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  obtain ⟨g,hg,hgs⟩ := stabilizer_transitive_neighbors Rg a hav has
  let d := act Rg g (p.walk.getVert 2)
  have hds : Adjacent Rg d s := by
    rw [←hgs]
    exact (adjacent_act_iff Rg g _ _).mpr hcv
  have hg' : x⁻¹*g ∈ stabilizer Rg a :=
    (stabilizer Rg a).mul_mem ((stabilizer Rg a).inv_mem hx) hg
  have hgd' : act Rg (x⁻¹*g) (p'.walk.getVert 2) = d := by
    rw [hverts 2,←act_mul,mul_inv_cancel_left]
  have hBmap : (B Rg a ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg a ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb a p.start_color
      ((stabilizer Rg a).inv_mem hg))
  have hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) := by
    change 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg g (p.walk.getVert 2)))
    rw [U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hforward
  have hcommon := plane_raw_paired_kernel_le_slice h e hz hk u hR hb4 hsmall p p' has hds
    hgen hfirst (by rwa [hQfirst]) g hg rfl (x⁻¹*g) hg' hgd' hmid hmid' hback hback'
  obtain ⟨q,q',hq1,hq1',hqv,hqv',hI,hjoin,hne⟩ :=
    raw_paired_paths_of_strict_slice h e hz hk u hR hb4 hsmall p p' has hds hcommon.2.1 hstrict
  exact ⟨s,has,x,hx,hgen,hpair,hfirst,p',hverts,g,hg,hgs,
    q,q',hq1,hq1',hqv,hqv',hI,hjoin,
    small_critical_distinct_kernels_joint_image h e hz hk q q' (hsmall _ _ q) (hsmall _ _ q') hne⟩

include h e hz hk in
/-- Actual application to the original backward selector. Midpoint generation
and the backward strict slice are discharged on the same selected path.
The next step is a small opposite slice or two simultaneous critical kernels. -/
theorem plane_selected_backward_kernel_reduction
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ d c, ∃ q : CriticalPath Rg (sourceGeometry h) d c,
      q.walk.getVert 2 = alpha Rg ∧
      Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) = stabilizer Rg (alpha Rg) ∧
      2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
      ((B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≤ 2 ∨
        ∃ b c' s, Adjacent Rg d s ∧
          Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
          ∃ q₀ : CriticalPath Rg (sourceGeometry h) b (alpha Rg),
            ∃ q₁ : CriticalPath Rg (sourceGeometry h) b c',
              q₀.walk.getVert 1 = s ∧ q₁.walk.getVert 1 = s ∧
              q₀.walk.getVert 2 = d ∧ q₁.walk.getVert 2 = d ∧
              (Z Rg b ⊓ Q Rg (alpha Rg)) ⊓ (Z Rg b ⊓ Q Rg c') = Z Rg s ∧
              (Z Rg b ⊓ Q Rg (alpha Rg)) ⊔ (Z Rg b ⊓ Q Rg c') = Z Rg b ∧
              2 < (Q Rg b).relIndex (Z Rg (alpha Rg) ⊔ Z Rg c')) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hav : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,r,hr,p',hverts,hps,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,halt⟩ :=
    plane_small_critical_backward_shift h e hz hk u hR p (hsmall _ _ p) hcv hs
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hav] at hnorm hinside
  have hfirst : Q Rg t ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg hat))
        (fun _ hv => hv.2 _ (adjacent_symm Rg hav))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  have finish {w : Vertex Rg}
      (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
        (v.walk.getVert (v.walk.length-2)))
      (hq1 : q.walk.getVert 1 = t)
      (hqv : ∀ i ≤ v.walk.length-2, q.walk.getVert (i+2) = v.walk.getVert i)
      (hgenq : Q Rg t ⊔ Q Rg (v.walk.getVert 1) = stabilizer Rg (alpha Rg)) :
      ∃ d c, ∃ q : CriticalPath Rg (sourceGeometry h) d c,
        q.walk.getVert 2 = alpha Rg ∧
        Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) = stabilizer Rg (alpha Rg) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
        ((B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≤ 2 ∨
          ∃ b c' s, Adjacent Rg d s ∧
            Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
            ∃ q₀ : CriticalPath Rg (sourceGeometry h) b (alpha Rg),
              ∃ q₁ : CriticalPath Rg (sourceGeometry h) b c',
                q₀.walk.getVert 1 = s ∧ q₁.walk.getVert 1 = s ∧
                q₀.walk.getVert 2 = d ∧ q₁.walk.getVert 2 = d ∧
                (Z Rg b ⊓ Q Rg (alpha Rg)) ⊓ (Z Rg b ⊓ Q Rg c') = Z Rg s ∧
                (Z Rg b ⊓ Q Rg (alpha Rg)) ⊔ (Z Rg b ⊓ Q Rg c') = Z Rg b ∧
                2 < (Q Rg b).relIndex (Z Rg (alpha Rg) ⊔ Z Rg c')) := by
    have hvlen : v.walk.length = 4 := v.length_eq_b.trans hb4
    have hqa : q.walk.getVert 2 = alpha Rg := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hqv 0 (by omega)
    have hmid : Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) =
        stabilizer Rg (q.walk.getVert 2) := by
      rw [hqa,hq1,hqv 1 (by omega)]
      exact hgenq
    refine ⟨_,_,q,hqa,(by simpa only [hqa] using hmid),hstrict,?_⟩
    by_cases hf : (B Rg (act Rg g (p.walk.getVert 2)) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (alpha Rg)) ≤ 2
    · exact Or.inl hf
    have hback : 2 < (B Rg (q.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (act Rg g (p.walk.getVert 2))) := by rwa [hqa]
    have hforward : 2 < (B Rg (act Rg g (p.walk.getVert 2)) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (q.walk.getVert 2)) := by rw [hqa]; exact Nat.lt_of_not_ge hf
    obtain ⟨s,hds,x,hx,hgen',hpair',hfirst',q',hvs,k,hkG,hks,
      q₀,q₁,h₀,h₁,hv₀,hv₁,hI,hjoin,hlarge⟩ :=
      plane_strict_reciprocal_paired_critical_kernels h e hz hk u hR hb4 hsmall q hmid hback hforward
    have hq₀ : q₀.walk.getVert 2 = act Rg g (p.walk.getVert 2) := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hv₀ 0 (by omega)
    have hq₁ : q₁.walk.getVert 2 = act Rg g (p.walk.getVert 2) := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hv₁ 0 (by omega)
    have out : ∃ b c' s, Adjacent Rg (act Rg g (p.walk.getVert 2)) s ∧
        Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg (act Rg g (p.walk.getVert 2)) ∧
        ∃ q₀ : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2),
          ∃ q₁ : CriticalPath Rg (sourceGeometry h) b c',
            q₀.walk.getVert 1 = s ∧ q₁.walk.getVert 1 = s ∧
            q₀.walk.getVert 2 = act Rg g (p.walk.getVert 2) ∧
            q₁.walk.getVert 2 = act Rg g (p.walk.getVert 2) ∧
            (Z Rg b ⊓ Q Rg (q.walk.getVert 2)) ⊓ (Z Rg b ⊓ Q Rg c') = Z Rg s ∧
            (Z Rg b ⊓ Q Rg (q.walk.getVert 2)) ⊔ (Z Rg b ⊓ Q Rg c') = Z Rg b ∧
            2 < (Q Rg b).relIndex (Z Rg (q.walk.getVert 2) ⊔ Z Rg c') :=
      ⟨_,_,s,hds,hfirst',q₀,q₁,h₀,h₁,hq₀,hq₁,hI,hjoin,hlarge⟩
    rw [hqa] at out
    exact Or.inr out
  rcases halt with ⟨q,hq1,hqv⟩ | ⟨q,hq1,hqv⟩
  · exact finish p q hq1 hqv hfirst
  · exact finish p' q hq1 hqv (by rwa [hQfirst])

omit hk in
include h e hz in
/-- Whole-core application of the actual backward kernel reduction, retaining
both moving covers and the original cubic projection and radical. -/
theorem coreExhaustion_or_cubic_backward_kernel_reduction :
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
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
          ∃ d c, ∃ q : CriticalPath Rg (sourceGeometry h) d c,
            q.walk.getVert 2 = alpha Rg ∧
            Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) = stabilizer Rg (alpha Rg) ∧
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
            ((B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≤ 2 ∨
              ∃ b c' s, Adjacent Rg d s ∧
                Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
                ∃ q₀ : CriticalPath Rg (sourceGeometry h) b (alpha Rg),
                  ∃ q₁ : CriticalPath Rg (sourceGeometry h) b c',
                    q₀.walk.getVert 1 = s ∧ q₁.walk.getVert 1 = s ∧
                    q₀.walk.getVert 2 = d ∧ q₁.walk.getVert 2 = d ∧
                    (Z Rg b ⊓ Q Rg (alpha Rg)) ⊓ (Z Rg b ⊓ Q Rg c') = Z Rg s ∧
                    (Z Rg b ⊓ Q Rg (alpha Rg)) ⊔ (Z Rg b ⊓ Q Rg c') = Z Rg b ∧
                    2 < (Q Rg b).relIndex (Z Rg (alpha Rg) ⊔ Z Rg c')))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall z p hstrict
    exact plane_selected_backward_kernel_reduction h e hz hk u hplane hb4 hsmall p hstrict

omit hk in
include h e hz in
/-- Literal C.1.32 application of the actual backward kernel reduction, retaining
both moving covers and the original cubic projection and radical. -/
theorem rankTwo_or_cubic_backward_kernel_reduction :
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
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
          ∃ d c, ∃ q : CriticalPath Rg (sourceGeometry h) d c,
            q.walk.getVert 2 = alpha Rg ∧
            Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) = stabilizer Rg (alpha Rg) ∧
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
            ((B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≤ 2 ∨
              ∃ b c' s, Adjacent Rg d s ∧
                Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
                ∃ q₀ : CriticalPath Rg (sourceGeometry h) b (alpha Rg),
                  ∃ q₁ : CriticalPath Rg (sourceGeometry h) b c',
                    q₀.walk.getVert 1 = s ∧ q₁.walk.getVert 1 = s ∧
                    q₀.walk.getVert 2 = d ∧ q₁.walk.getVert 2 = d ∧
                    (Z Rg b ⊓ Q Rg (alpha Rg)) ⊓ (Z Rg b ⊓ Q Rg c') = Z Rg s ∧
                    (Z Rg b ⊓ Q Rg (alpha Rg)) ⊔ (Z Rg b ⊓ Q Rg c') = Z Rg b ∧
                    2 < (Q Rg b).relIndex (Z Rg (alpha Rg) ⊔ Z Rg c')))) :=
  (coreExhaustion_or_cubic_backward_kernel_reduction h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
