module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalJointImages
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels

/-!
# Reverse joint images and stabilizers on the original Borel graph

A subgroup of an original two-core, normalized by its whole stabilizer and
centralized by an opposite critical seed, is fixed by the local two-residual.
The proof uses the original cubic normal-section detection theorem through
an actual vertex embedding. Its odd kernel E/Q is retained throughout.

Above distance six, the two reverse selected seeds are at distance at most
six from the earlier endpoint. Thus their commutator join is centralized
there. If their joint image had order four, it would give the entire
neighboring-core movement. Its known edge normalization would then extend
to the entire intermediate stabilizer, forcing residual fixedness contrary
to the previously established escaping critical line. The reverse joint
image therefore has order two, with equal full critical kernels and a
common nonzero commutator line.

For a small neighboring critical kernel normalized by the generating actor,
the strict whole-seed Baumann slice forces the intermediate core into the
opposite proper Thompson mover. Otherwise residual generation normalizes
the kernel/seed join, whose quotient over the intermediate seed has order
dividing eight, contradicting that slice. Applying this to both reverse
selectors puts their common line in the entire reverse omega subgroup.
This proves centrality under its two-core, not its entire stabilizer.

OriginalSylowExceptional applies the result on the literal original c.L,d.S.
Both full moving covers, full central attachments, actual switches and all
path overlaps are preserved. The distance-six order-four comparison, full
stabilizer centrality of the common line, mover equality, terminal distance
exclusions and whole-core reconstruction remain required.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c), (5.9) and (5.10), printed pp.916--917,921--923.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags Theory.SpecificGroups.SymmetricSix
open Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
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
/-- A subgroup of the original two-core normalized by the entire stabilizer
and fixed by an opposite critical seed is fixed by the local residual. -/
theorem critical_normal_core_le_fixed
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (D : Subgroup (FreeAmalgam Rg)) (hDQ : D ≤ Q Rg a)
    (hDN : stabilizer Rg a ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hDZ : D ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg))) :
    D ≤ fixedCore Rg a := by
  obtain ⟨i,hi,hir,hiQ,_⟩ := graph_cover h e hz hk a p.start_color
  let D₀ := D.comap i
  let A₀ := (Z Rg z).comap i
  have hDG : D ≤ stabilizer Rg a := hDQ.trans (fun _ hx => hx.1)
  have hDm : D₀.map i = D := map_comap_eq_self (hDG.trans_eq hir.symm)
  have hAm : A₀.map i = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical).trans_eq hir.symm)
  have hg (m : (L ⊔ R : Subgroup G)) : i m ∈ stabilizer Rg a := hir ▸ ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro x hx m
    change i (m*x*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (i x)).mp hx⟩
  have hcomm : ⁅D₀,A₀⁆ ≤ ⊥ := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [map_commutator,hDm,hAm,Subgroup.map_bot]
    exact (commutator_eq_bot_iff_le_centralizer.mpr hDZ).le
  have hne : ¬ A₀ ≤ pCore 2 (L ⊔ R : Subgroup G) := by
    intro he
    have hh := map_mono (f := i) he
    rw [hAm,hiQ] at hh
    exact (reverse_pair h e p).2 hh
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hAtwo : IsPGroup 2 A₀ :=
    (IsElementaryAbelian.isPGroup 2 (Z Rg z)).comap_of_injective i hi
  have hm := map_mono (f := i)
    (CubicAction.normal_commutator_le_of_escaping_two h e hz D₀ ⊥ A₀ hAtwo hne hcomm)
  let j : (L ⊔ R : Subgroup G) →* stabilizer Rg a := i.codRestrict _ hg
  have hjs : Function.Surjective j := by
    intro x
    have hx : (x : FreeAmalgam Rg) ∈ i.range := hir.symm ▸ x.property
    obtain ⟨m,hm⟩ := hx
    exact ⟨m,Subtype.ext hm⟩
  have hj : (stabilizer Rg a).subtype.comp j = i := rfl
  have hLm : (L.subgroupOf (L ⊔ R)).map i = Ltilde Rg a := by
    rw [←h.relative_residual,←hj,←map_map,map_pResidual_of_surjective 2 j hjs]
    rfl
  rw [map_commutator,hDm,hLm,Subgroup.map_bot] at hm
  exact le_inf hDQ (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hm))

include h e hz hk in
/-- A three-shift core commutator cannot be both normalized by the entire
intermediate stabilizer and fixed by its critical endpoint. -/
theorem borel_three_shift_core_not_stabilizer_invariant
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path)
    (hfix : ⁅Z Rg t.start,Q Rg r.start⁆ ≤
      centralizer (Z Rg (q.path.walk.getVert (q.path.walk.length-2)) : Set (FreeAmalgam Rg))) :
    ¬ stabilizer Rg r.start ≤ normalizer
      ((⁅Z Rg t.start,Q Rg r.start⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  have hh := borel_three_shift_core_movement h e hz hk hb u hR p q r t
  intro hn
  exact hh.2.2.2.2.2 (critical_normal_core_le_fixed h e hz hk r.path _
    (hh.2.1.trans inf_le_left |>.trans (omegaCenter_le _)) hn hfix)

include h e hz hk in
/-- Above distance six, two actual reverse selected commutators cannot
span the whole neighboring-core movement. Their radius-six placement would
make that movement invariant under the entire intermediate stabilizer. -/
theorem borel_four_shift_reverse_core_span_false_gt_six
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) (s : BorelBackwardShift (h := h) t.path)
    {c₁ c₂ : Vertex Rg}
    (w₁ : CriticalPath Rg (sourceGeometry h) c₁ t.start)
    (w₂ : CriticalPath Rg (sourceGeometry h) c₂ t.start)
    (ho₁ : ∀ i ≤ s.path.walk.length-2,
      w₁.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i))
    (ho₂ : ∀ i ≤ s.path.walk.length-2,
      w₂.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i))
    (hspan : ⁅Z Rg c₁,Z Rg t.start⁆ ⊔ ⁅Z Rg c₂,Z Rg t.start⁆ =
      ⁅Z Rg t.start,Q Rg r.start⁆) : False := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := t.path.walk.getVert (t.path.walk.length-2)
  let f := r.path.walk.getVert (r.path.walk.length-2)
  let H := ⁅Z Rg t.start,Q Rg r.start⁆
  have hb4 : 4 < sourceDistance h := by omega
  have hrl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
  have htl : t.path.walk.length = sourceDistance h := t.path.length_eq_b
  have hvf : (cosetGraph Rg).dist v f = 2 := by
    rw [show v = t.path.walk.getVert (t.path.walk.length-2) from rfl,t.path.dist_end]
    omega
  have hfz : (cosetGraph Rg).dist f z = 2 := by
    rw [show f = r.path.walk.getVert (r.path.walk.length-2) from rfl,r.path.dist_end]
    omega
  have hvz : (cosetGraph Rg).dist v z ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := v) (v := f) (w := z)
    omega
  have seed_fixed {c : Vertex Rg} (w : CriticalPath Rg (sourceGeometry h) c t.start)
      (ho : ∀ i ≤ s.path.walk.length-2,
        w.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) :
      ⁅Z Rg c,Z Rg t.start⁆ ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := by
    have hw2 : w.walk.getVert 2 = v := by
      simpa only [Nat.zero_add,Nat.sub_zero,SimpleGraph.Walk.getVert_length] using
        ho 0 (Nat.zero_le _)
    have hwl : w.walk.length = sourceDistance h := w.length_eq_b
    have hcv : (cosetGraph Rg).dist c v = 2 := by
      rw [←hw2,w.dist_start (by omega : 2 ≤ w.walk.length)]
    have hcz : (cosetGraph Rg).dist c z ≤ 6 := by
      have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := v) (w := z)
      omega
    have hcQ : Z Rg c ≤ Q Rg z := by
      apply Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c w.start_color)
      rw [(sourceGeometry h).distance_constant _ w.start_color]
      change (cosetGraph Rg).dist c z < sourceDistance h
      omega
    exact ((critical_seed_commutator_le h w).trans hcQ).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg z r.path.end_color)))
  have hfix : H ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := by
    rw [show H = ⁅Z Rg t.start,Q Rg r.start⁆ from rfl,←hspan]
    exact sup_le (seed_fixed w₁ ho₁) (seed_fixed w₂ ho₂)
  have hmove := borel_three_shift_core_movement h e hz hk hb4 u hR p q r t
  have hnormal : stabilizer Rg r.start ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    rw [←t.generation]
    exact sup_le hmove.2.2.1
      ((le_centralizer_iff.mp hfix).trans (Subgroup.centralizer_le_normalizer _))
  exact borel_three_shift_core_not_stabilizer_invariant h e hz hk hb4 u hR p q r t hfix hnormal

include h e hz hk in
/-- Above distance six, both actual reverse selectors have joint image two,
equal nonzero commutator lines and equal full critical kernels. The
order-four alternative is excluded by whole-stabilizer invariance. -/
theorem borel_four_shift_reverse_joint_image_two_gt_six
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) (s : BorelBackwardShift (h := h) t.path)
    (hse : act Rg s.transporter (t.path.walk.getVert 1) = s.edge)
    (hne : edgeOffenderJoin t.start s.edge ≠ edgeOffenderJoin s.start s.edge) :
    let v := t.path.walk.getVert (t.path.walk.length-2)
    ∃ g ∈ stabilizer Rg v, ∃ x ∈ stabilizer Rg v,
      let d := act Rg g (s.path.walk.getVert (s.path.walk.length-1))
      let c := act Rg g (s.path.walk.getVert (s.path.walk.length-2))
      let A := Z Rg c ⊔ Z Rg (act Rg x c)
      Q Rg d ⊔ Z Rg s.start = stabilizer Rg v ∧
      Q Rg (act Rg x d) ⊔ Z Rg s.start = stabilizer Rg v ∧
      edgeOffenderJoin v d ⊔ edgeOffenderJoin v (act Rg x d) = stabilizer Rg v ∧
      x ∈ normalizer (edgeOffenderJoin v
        (s.path.walk.getVert (s.path.walk.length-1)) : Set (FreeAmalgam Rg)) ∧
      X Rg s.start ≤ normalizer (((Z Rg c ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg s.start ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      A ≤ Q Rg r.start ∧
      (Q Rg t.start).relIndex A = 2 ∧
      ⁅Z Rg c,Z Rg t.start⁆ = ⁅Z Rg (act Rg x c),Z Rg t.start⁆ ∧
      Nat.card (⁅Z Rg c,Z Rg t.start⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      Z Rg t.start ⊓ Q Rg c = Z Rg t.start ⊓ Q Rg (act Rg x c) ∧
      ∃ (s₁ : CriticalPath Rg (sourceGeometry h) c t.start)
        (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) t.start),
        s₁.walk.getVert 1 = d ∧ s₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ s.path.walk.length-2,
          s₁.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) ∧
        (∀ i ≤ s.path.walk.length-2,
          s₂.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) := by
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hN₁,hN₂,hAC,hi,htwo,hfour,
    s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩ :=
    borel_four_shift_reverse_joint_image h e hz hk (by omega) u hR p q r t s hse hne
  have hsmall : (Q Rg t.start).relIndex
      (Z Rg (act Rg g (s.path.walk.getVert (s.path.walk.length-2))) ⊔
        Z Rg (act Rg x (act Rg g (s.path.walk.getVert (s.path.walk.length-2))))) = 2 := by
    rcases hi with hi | hi
    · exact hi
    · exact (borel_four_shift_reverse_core_span_false_gt_six h e hz hk hb u hR p q r t s
        s₁ s₂ ho₁ ho₂ (hfour hi).2).elim
  have hlines := htwo hsmall
  exact ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hN₁,hN₂,hAC,hsmall,
    hlines.1,hlines.2.1,hlines.2.2,s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩

include h e hz hk in
/-- A normalized neighboring critical kernel and a strict whole-seed slice
force the intermediate core into the opposite proper mover. The critical
line then lies in the intermediate full omega layer. -/
theorem borel_normalized_neighbor_kernel_core
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c d w z : Vertex Rg} (ha : color Rg a = false)
    (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : (Q Rg w).relIndex (Z Rg c) < 4)
    (hfirst : p.walk.getVert 1 = d)
    (had : Adjacent Rg a d) (hcd : Adjacent Rg c d)
    (hgen : Q Rg d ⊔ Z Rg z = stabilizer Rg a)
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    (hn : Z Rg z ≤ normalizer (((Z Rg c ⊓ Q Rg w) ⊔ Z Rg a :
      Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    Q Rg a ≤ edgeOffenderJoin c d ∧ ⁅Z Rg c,Z Rg w⁆ ≤ X Rg a := by
  let K := Z Rg c ⊓ Q Rg w
  let N := K ⊔ Z Rg a
  have hb2 := distance_gt_two h e hz hk
  have hd : color Rg d = true := by
    have hh := adjacent_color_ne Rg had
    rw [ha] at hh
    cases he : color Rg d <;> simp_all
  have hcv := terminal_neighbor_seed_radius had hcd
  have hNV : N ≤ V Rg a := sup_le (inf_le_left.trans hcv) (Z_le_VBall Rg a 2)
  have hZaT : Z Rg a ≤ Q Rg d :=
    (((sourceGeometry h).omega_bound a ha (by
      rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)).trans
      (omegaCenter_le _)).trans (Q_le_adjacent_h Rg hd had)
  have hTNc : Q Rg d ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg d ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hcd)).trans (Z_normalized Rg c)
  let := finite_Z Rg c
  let := finite_Z Rg a
  have hnot : ¬ K ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
    intro hKB
    have hki : K.relIndex (Z Rg c) = 2 := by
      rw [show K = Z Rg c ⊓ Q Rg w from rfl,inf_relIndex_left]
      exact (small_critical_indices h e hz hk p hp).1
    have hi := relIndex_le_of_le_left hKB
      (index_ne_zero_of_finite : K.relIndex (Z Rg c) ≠ 0)
    have hj := relIndex_le_of_le_right (H := B Rg a ((sourceGeometry h).Z_normal _))
      (DistanceEight.U_le_Z Rg c) index_ne_zero_of_finite
    rw [hki] at hi
    exact (Nat.not_le_of_gt hstrict) (hj.trans hi)
  have hsmall : (Z Rg a).relIndex N ∣ 8 := by
    have hbig : (Z Rg a).relIndex (Z Rg c ⊔ Z Rg a) ∣ 8 := by
      rw [relIndex_sup_of_normalizes (Z Rg c) (Z Rg a) (hZaT.trans hTNc)]
      have hh := relIndex_dvd_of_le_left (Z Rg c) (adjacent_Z_le Rg ha had)
      rw [borel_full_seed_edge_index h e hz hk u hR p.start_color hcd] at hh
      exact hh
    have hm := relIndex_mul_relIndex (Z Rg a) N (Z Rg c ⊔ Z Rg a)
      le_sup_right (sup_le_sup_right inf_le_left _)
    exact (Dvd.intro _ hm).trans hbig
  have hJdata := borel_small_mover_normalizes_critical_kernel h e hz hk u hR p hp
  rw [hfirst] at hJdata
  obtain ⟨J,_,hJ,_,hJT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR p.start_color hcd
  have hJN : edgeOffenderJoin c d ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hJdata.2 (((hJ.le.trans hJT).trans
      (show Q Rg d ≤ stabilizer Rg a from
        fun _ hx => hx.2 _ (adjacent_symm Rg had))).trans (Z_normalized Rg a))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQa : Q Rg a ≤ edgeOffenderJoin c d := by
    by_contra hbad
    have hL := (borel_opposite_generation_of_core_not_le h e hz hk u hR ha p.start_color
      had hcd (Z Rg z) hgen hbad).2
    exact hnot (le_sup_left.trans (terminal_residual_small_radius_le_slice h e hz hk ha N
      hNV (hL.trans (sup_le hJN hn)) hsmall))
  have hHQ : ⁅Z Rg c,Z Rg w⁆ ≤ Q Rg a :=
    ((critical_seed_commutator_le h p).trans hcv).trans ((sourceGeometry h).V_le_Q hb2 a ha)
  have hHC : ⁅Z Rg c,Z Rg w⁆ ≤ centralizer (Q Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (hQa.trans hJdata.1)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.start_color
  refine ⟨hQa,?_⟩
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hHQ hx,
    elemPow_eq_one_of_isElementaryAbelian x ((critical_seed_commutator_le h p) hx),hHC hx⟩

include h e hz hk in
/-- The common reverse line above distance six lies in the entire omega
subgroup of the reverse vertex. Both opposite proper movers contain its
core. All selectors, normalizers and original path overlaps are retained. -/
theorem borel_four_shift_reverse_common_omega_gt_six
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) (s : BorelBackwardShift (h := h) t.path)
    (hse : act Rg s.transporter (t.path.walk.getVert 1) = s.edge)
    (hne : edgeOffenderJoin t.start s.edge ≠ edgeOffenderJoin s.start s.edge) :
    let v := t.path.walk.getVert (t.path.walk.length-2)
    ∃ g ∈ stabilizer Rg v, ∃ x ∈ stabilizer Rg v,
      let d := act Rg g (s.path.walk.getVert (s.path.walk.length-1))
      let c := act Rg g (s.path.walk.getVert (s.path.walk.length-2))
      let A := Z Rg c ⊔ Z Rg (act Rg x c)
      Q Rg d ⊔ Z Rg s.start = stabilizer Rg v ∧
      Q Rg (act Rg x d) ⊔ Z Rg s.start = stabilizer Rg v ∧
      edgeOffenderJoin v d ⊔ edgeOffenderJoin v (act Rg x d) = stabilizer Rg v ∧
      x ∈ normalizer (edgeOffenderJoin v
        (s.path.walk.getVert (s.path.walk.length-1)) : Set (FreeAmalgam Rg)) ∧
      X Rg s.start ≤ normalizer (((Z Rg c ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg s.start ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      A ≤ Q Rg r.start ∧
      (Q Rg t.start).relIndex A = 2 ∧
      ⁅Z Rg c,Z Rg t.start⁆ = ⁅Z Rg (act Rg x c),Z Rg t.start⁆ ∧
      Nat.card (⁅Z Rg c,Z Rg t.start⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      Z Rg t.start ⊓ Q Rg c = Z Rg t.start ⊓ Q Rg (act Rg x c) ∧
      Q Rg v ≤ edgeOffenderJoin c d ∧
      Q Rg v ≤ edgeOffenderJoin (act Rg x c) (act Rg x d) ∧
      ⁅Z Rg c,Z Rg t.start⁆ ≤ X Rg v ∧
      ∃ (s₁ : CriticalPath Rg (sourceGeometry h) c t.start)
        (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) t.start),
        s₁.walk.getVert 1 = d ∧ s₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ s.path.walk.length-2,
          s₁.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) ∧
        (∀ i ≤ s.path.walk.length-2,
          s₂.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) := by
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hN₁,hN₂,hAC,hi,hline,hcard,hkernel,
    s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩ :=
    borel_four_shift_reverse_joint_image_two_gt_six h e hz hk hb u hR p q r t s hse hne
  let v := t.path.walk.getVert (t.path.walk.length-2)
  let rev : CriticalPath Rg (sourceGeometry h) v s.start :=
    { start_color := s.path.end_color
      walk := s.path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,s.path.shortest,SimpleGraph.dist_comm]
      critical := reverse_pair h e s.path }
  have hb4 : 4 < sourceDistance h := by omega
  have hb2 : 2 < sourceDistance h := by omega
  have hZX : Z Rg s.start ≤ X Rg s.start :=
    (sourceGeometry h).omega_bound s.start s.path.start_color (by
      rw [(sourceGeometry h).distance_constant _ s.path.start_color]
      exact sourceDistance_pos h)
  have strict (k : FreeAmalgam Rg) (hkG : k ∈ stabilizer Rg v) :
      2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (act Rg k (s.path.walk.getVert (s.path.walk.length-2)))) := by
    have hB : (B Rg v ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj k⁻¹).toMonoidHom = B Rg v ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb2 v rev.start_color ((stabilizer Rg v).inv_mem hkG))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    simpa only [rev,SimpleGraph.Walk.getVert_reverse] using
      borel_forward_slice_strict_at h e hz hk hb4 u hR rev
  have small₁ : (Q Rg t.start).relIndex
      (Z Rg (act Rg g (s.path.walk.getVert (s.path.walk.length-2)))) < 4 := by
    have hh := relIndex_le_of_le_right
      (H := Q Rg t.start)
      (show Z Rg (act Rg g (s.path.walk.getVert (s.path.walk.length-2))) ≤
        Z Rg (act Rg g (s.path.walk.getVert (s.path.walk.length-2))) ⊔
          Z Rg (act Rg x (act Rg g (s.path.walk.getVert (s.path.walk.length-2)))) from le_sup_left)
      (by rw [hi]; decide)
    rw [hi] at hh
    omega
  have small₂ : (Q Rg t.start).relIndex
      (Z Rg (act Rg x (act Rg g (s.path.walk.getVert (s.path.walk.length-2))))) < 4 := by
    have hh := relIndex_le_of_le_right
      (H := Q Rg t.start)
      (show Z Rg (act Rg x (act Rg g (s.path.walk.getVert (s.path.walk.length-2)))) ≤
        Z Rg (act Rg g (s.path.walk.getVert (s.path.walk.length-2))) ⊔
          Z Rg (act Rg x (act Rg g (s.path.walk.getVert (s.path.walk.length-2)))) from le_sup_right)
      (by rw [hi]; decide)
    rw [hi] at hh
    omega
  have apply_neighbor {c d : Vertex Rg} (w : CriticalPath Rg (sourceGeometry h) c t.start)
      (hw1 : w.walk.getVert 1 = d)
      (ho : ∀ i ≤ s.path.walk.length-2,
        w.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i))
      (hw : (Q Rg t.start).relIndex (Z Rg c) < 4)
      (hgen : Q Rg d ⊔ Z Rg s.start = stabilizer Rg v)
      (hN : X Rg s.start ≤ normalizer (((Z Rg c ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)))
      (hstrict : 2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
      Q Rg v ≤ edgeOffenderJoin c d ∧ ⁅Z Rg c,Z Rg t.start⁆ ≤ X Rg v := by
    have hw2 : w.walk.getVert 2 = v := by
      simpa only [Nat.zero_add,Nat.sub_zero,SimpleGraph.Walk.getVert_length] using
        ho 0 (Nat.zero_le _)
    have hl : w.walk.length = sourceDistance h := w.length_eq_b
    have hcd : Adjacent Rg c d := by
      have hh := (cosetGraph_adj Rg _ _).mp (w.walk.adj_getVert_succ (i := 0) (by omega))
      simpa only [SimpleGraph.Walk.getVert_zero,hw1] using hh
    have had : Adjacent Rg v d := by
      have hh := adjacent_symm Rg
        ((cosetGraph_adj Rg _ _).mp (w.walk.adj_getVert_succ (i := 1) (by omega)))
      simpa only [hw1,hw2] using hh
    exact borel_normalized_neighbor_kernel_core h e hz hk u hR rev.start_color
      w hw hw1 had hcd hgen hstrict (hZX.trans hN)
  have hcore₁ := apply_neighbor s₁ hs₁ ho₁ small₁ hgen₁ hN₁ (strict g hg)
  have hstrict₂ : 2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x (act Rg g (s.path.walk.getVert (s.path.walk.length-2))))) := by
    simpa only [act_mul] using strict (g*x) ((stabilizer Rg v).mul_mem hg hx)
  have hcore₂ := apply_neighbor s₂ hs₂ ho₂ small₂ hgen₂ hN₂ hstrict₂
  exact ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hN₁,hN₂,hAC,hi,hline,hcard,hkernel,
    hcore₁.1,hcore₂.1,hcore₁.2,s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
