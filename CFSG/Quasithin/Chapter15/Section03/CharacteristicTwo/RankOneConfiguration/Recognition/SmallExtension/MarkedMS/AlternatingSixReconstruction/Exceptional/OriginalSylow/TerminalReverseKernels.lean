module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalCoreMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer

/-!
# Both reverse selected kernels in the terminal Borel configuration

For a small critical path, failure of central generation forces the full
endpoint omega group to normalize the join of the starting seed with every
neighboring seed restricted to the opposite predecessor core. The proof uses
the full-X commutator inequality and the actual common-edge normalizers.

At a generating edge, a trapped selected seed would therefore have a span
normalized by the whole starting stabilizer. Its quotient over the starting
seed has order dividing eight, so residual control puts it in the Baumann
slice. The strict forward bound excludes this. Thus both choices of the
existing Borel selector give compatible critical paths with nonzero
whole-seed commutators; their proper movers generate the starting stabilizer.
The actual switch and both path overlaps are retained.

In the three-shift terminal configuration, distinct opposite movers and the
proved core containment supply failure of central generation. Applying the
result to the literal reversed last path gives the two reverse selected
kernels used in MS93 (5.10). Both full moving covers, their central attachments
and the original cubic kernel E are retained. The joint image comparison,
mover equality, terminal exclusions and whole-core reconstruction remain
separate obligations. OriginalSylowExceptional gives the original c.L,d.S
application.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.5)(c), (5.9)--(5.10), especially printed p.923.
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
/-- In the nonsplit case the full endpoint omega subgroup normalizes the
join of the starting seed with every neighboring restricted kernel. -/
theorem small_neighbor_kernel_omega_normalization
    {a c d z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (had : Adjacent Rg a d) (hcd : Adjacent Rg c d)
    (hn : X Rg a ≠ U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) :
    X Rg z ≤ normalizer
      (((Z Rg c ⊓ Q Rg (p.walk.getVert (p.walk.length-2))) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let v := p.walk.getVert (p.walk.length-2)
  let K := Z Rg c ⊓ Q Rg v
  let N := K ⊔ Z Rg a
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hd : color Rg d = true := by
    have hh := adjacent_color_ne Rg had
    rw [p.start_color] at hh
    cases he : color Rg d <;> simp_all
  have hKQ : K ≤ Q Rg a :=
    (inf_le_left.trans (terminal_neighbor_seed_radius had hcd)).trans
      ((sourceGeometry h).V_le_Q hb a p.start_color)
  have hKG : K ≤ stabilizer Rg z :=
    inf_le_right.trans (terminal_last_edge_inputs h p hb).2.2
  have hXc : X Rg z ⊓ Q Rg a ≤ stabilizer Rg c :=
    (inf_le_right.trans (Q_le_adjacent_h Rg hd had)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hcd))
  have hzv : (cosetGraph Rg).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_end]
    omega
  have hXv : X Rg z ⊓ Q Rg a ≤ stabilizer Rg v :=
    (inf_le_left.trans (omegaCenter_le _)).trans
      (Q_le_stabilizer_of_dist_two Rg z v p.end_color hzv)
  have hNK : X Rg z ⊓ Q Rg a ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    (le_inf (hXc.trans (Z_normalized Rg c)) (hXv.trans (Q_normalized Rg v))).trans
      inf_normalizer_le_normalizer_inf
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  rcases small_critical_omega_generation_or_control_at h e hz hk pr hs with hgen | hc
  · exact (hn (omega_generation_transport p.end_color p.start_color hgen)).elim
  have hXN : X Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_X_le_vertex h e z p.end_color a pr.critical).trans (Z_normalized Rg a)
  have hRZ : ⁅X Rg z,Z Rg a⁆ ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_right.mp hXN
  have hKR : K ≤ centralizer ((⁅X Rg z,Z Rg a⁆ :
      Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
    (hKQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color)))).trans (centralizer_le hRZ)
  have hbound : ⁅X Rg z,K⁆ ≤ N := by
    rw [commutator_comm]
    exact (hc K hKG hKR).trans (sup_le (hRZ.trans le_sup_right)
      ((le_normalizer_iff_commutator_le_left.mp hNK).trans le_sup_left))
  change X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))
  apply le_normalizer_iff.mpr
  intro x hx y hy
  have hm : N.map (MulAut.conj x).toMonoidHom ≤ N := by
    rw [show N = K ⊔ Z Rg a from rfl,Subgroup.map_sup]
    refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
    rintro _ ⟨k,hkK,rfl⟩
    have hh := N.mul_mem (hbound (commutator_mem_commutator hx hkK)) (mem_sup_left hkK)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hy)

include h e hz hk in
/-- A generating neighboring seed cannot be trapped when full omega is
not centrally generated: normalization would put its whole span in the
Baumann slice, contrary to the strict forward bound. -/
theorem borel_nonsplit_generating_neighbor_not_trapped
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c d z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (had : Adjacent Rg a d) (hcd : Adjacent Rg c d)
    (hn : X Rg a ≠ U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))))
    (hgen : Q Rg d ⊔ Z Rg z = stabilizer Rg a)
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  let N := Z Rg c ⊔ Z Rg a
  have hb := distance_gt_two h e hz hk
  have hd : color Rg d = true := by
    have hh := adjacent_color_ne Rg had
    rw [p.start_color] at hh
    cases he : color Rg d <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hcd
    rw [hd] at hh
    cases he : color Rg c <;> simp_all
  have hXN := small_neighbor_kernel_omega_normalization h e hz hk p hp had hcd hn
  rw [inf_eq_left.mpr hbad] at hXN
  have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
    rw [(sourceGeometry h).distance_constant z p.end_color]
    exact sourceDistance_pos h)
  have hTNa : Q Rg d ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (show Q Rg d ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg had)).trans (Z_normalized Rg a)
  have hTNc : Q Rg d ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg d ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hcd)).trans (Z_normalized Rg c)
  have hGN : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le ((le_inf hTNc hTNa).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) (hZX.trans hXN)
  have hZaT : Z Rg a ≤ Q Rg d :=
    (((sourceGeometry h).omega_bound a p.start_color (by
      rw [(sourceGeometry h).distance_constant a p.start_color]
      exact sourceDistance_pos h)).trans (omegaCenter_le _)).trans (Q_le_adjacent_h Rg hd had)
  let := finite_Z Rg a
  have hsmall : (Z Rg a).relIndex N ∣ 8 := by
    change (Z Rg a).relIndex (Z Rg c ⊔ Z Rg a) ∣ 8
    rw [relIndex_sup_of_normalizes (Z Rg c) (Z Rg a) (hZaT.trans hTNc)]
    have hh := relIndex_dvd_of_le_left (Z Rg c) (adjacent_Z_le Rg p.start_color had)
    rw [borel_full_seed_edge_index h e hz hk u hR hc hcd] at hh
    exact hh
  have hNB := terminal_residual_small_radius_le_slice h e hz hk p.start_color N
    (sup_le (terminal_neighbor_seed_radius had hcd) (Z_le_VBall Rg a 2))
    ((Ltilde_le_stabilizer a).trans hGN) hsmall
  have hUB : U Rg c ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
    ((DistanceEight.U_le_Z Rg c).trans le_sup_left).trans hNB
  rw [relIndex_eq_one.mpr hUB] at hstrict
  omega

include h e hz hk in
/-- Every generating conjugate of the second vertex supplies a backward
critical path in the nonsplit case, with full-omega normalization of its
restricted-kernel join and nonzero whole-seed commutator. -/
theorem borel_nonsplit_generating_shift
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hn : X Rg a ≠ U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))))
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgen : Q Rg (act Rg g (p.walk.getVert 1)) ⊔ Z Rg z = stabilizer Rg a) :
    let c := act Rg g (p.walk.getVert 2)
    let d := act Rg g (p.walk.getVert 1)
    let v := p.walk.getVert (p.walk.length-2)
    X Rg z ≤ normalizer (((Z Rg c ⊓ Q Rg v) ⊔ Z Rg a :
      Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
    ⁅Z Rg c,Z Rg v⁆ ≠ ⊥ ∧
    ∃ q : CriticalPath Rg (sourceGeometry h) c v,
      q.walk.getVert 1 = d ∧
      ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hfirst : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hsecond : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  let c := act Rg g (p.walk.getVert 2)
  let d := act Rg g (p.walk.getVert 1)
  have had : Adjacent Rg a d := by
    simpa only [show act Rg g a = a from hg] using
      (adjacent_act_iff Rg g _ _).mpr hfirst
  have hcd : Adjacent Rg c d := (adjacent_act_iff Rg g _ _).mpr hsecond
  have hc : color Rg c = false := by
    rw [show c = act Rg g (p.walk.getVert 2) from rfl,action_preserves_color]
    exact (p.vertex_color (by omega : 2 ≤ p.walk.length)).mpr (by decide)
  have hB : (B Rg a ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg a ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 a p.start_color ((stabilizer Rg a).inv_mem hg))
  have hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
    change 2 < (B Rg a _).relIndex (U Rg (act Rg g (p.walk.getVert 2)))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact borel_forward_slice_strict_at h e hz hk hb u hR p
  have hnot := borel_nonsplit_generating_neighbor_not_trapped h e hz hk u hR
    p hp had hcd hn hgen hstrict
  let w : (cosetGraph Rg).Walk c a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hcd)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg had)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb2) hc w hw hnot
  have hcomm : ⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length-2))⁆ ≠ ⊥ := by
    intro hzero
    exact critical_commutator_not_central h e hz hk q (by rw [hzero]; exact bot_le)
  refine ⟨small_neighbor_kernel_omega_normalization h e hz hk p hp had hcd hn,
    hcomm,q,?_,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩
  simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
    hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
    SimpleGraph.Walk.getVert_zero,d]

include h e hz hk in
private theorem borel_paired_generating_transports_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ g ∈ stabilizer Rg (alpha Rg), ∃ x ∈ stabilizer Rg (alpha Rg),
      let d := act Rg g (p.walk.getVert 1)
      Q Rg d ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Q Rg (act Rg x d) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      edgeOffenderJoin (alpha Rg) d ⊔ edgeOffenderJoin (alpha Rg) (act Rg x d) =
        stabilizer Rg (alpha Rg) ∧
      x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) := by
  obtain ⟨d,_,r,_,_,hpair,_,_,hgen₁,hgen₂,_,_,hnorm,_,_,g,hg,hgd,_⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hp
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  refine ⟨g,hg,x,hx,?_⟩
  dsimp only
  rw [hgd]
  exact ⟨hgen₁,hgen₂,hpair,hnorm⟩

include h e hz hk in
private theorem borel_paired_generating_transports
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ g ∈ stabilizer Rg a, ∃ x ∈ stabilizer Rg a,
      let d := act Rg g (p.walk.getVert 1)
      Q Rg d ⊔ Z Rg z = stabilizer Rg a ∧
      Q Rg (act Rg x d) ⊔ Z Rg z = stabilizer Rg a ∧
      edgeOffenderJoin a d ⊔ edgeOffenderJoin a (act Rg x d) = stabilizer Rg a ∧
      x ∈ normalizer (edgeOffenderJoin a (p.walk.getVert 1) : Set (FreeAmalgam Rg)) := by
  obtain ⟨k,hkvertex⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg k⁻¹ a = alpha Rg := by
    rw [hkvertex,act_mVertex,mul_inv_cancel]
    rfl
  have hpbase : (Q Rg (act Rg k⁻¹ z)).relIndex (Z Rg (act Rg k⁻¹ a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hp
  have hh := borel_paired_generating_transports_base h e hz hk u hR
    (z := act Rg k⁻¹ z)
  rw [←hbase] at hh
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm⟩ := hh (p.act k⁻¹) hpbase
  let g' := k⁻¹*g*k
  let x' := k⁻¹*x*k
  have transform (v : Vertex Rg) (y : FreeAmalgam Rg) :
      act Rg (k⁻¹*y*k) v = act Rg k (act Rg y (act Rg k⁻¹ v)) := by
    simp only [act_mul]
  have cancel (v : Vertex Rg) : act Rg k (act Rg k⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hg' : g' ∈ stabilizer Rg a := by
    change act Rg g' a = a
    rw [transform,show act Rg g (act Rg k⁻¹ a) = act Rg k⁻¹ a from hg,cancel]
  have hx' : x' ∈ stabilizer Rg a := by
    change act Rg x' a = a
    rw [transform,show act Rg x (act Rg k⁻¹ a) = act Rg k⁻¹ a from hx,cancel]
  let d := act Rg g ((p.act k⁻¹).walk.getVert 1)
  have hd : act Rg k d = act Rg g' (p.walk.getVert 1) := by
    simp only [d,CriticalPath.act,actWalk_getVert,g',transform]
  have hdx : act Rg k (act Rg x d) = act Rg x' (act Rg g' (p.walk.getVert 1)) := by
    rw [←hd]
    simp only [x',←act_mul]
    congr 1
    group
  have hfirst : Adjacent Rg (act Rg k⁻¹ a) ((p.act k⁻¹).walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (p.act k⁻¹).walk.adj_getVert_succ (i := 0)
        ((p.act k⁻¹).length_eq_b ▸ sourceDistance_pos h)
  have had : Adjacent Rg (act Rg k⁻¹ a) d := by
    simpa only [show act Rg g (act Rg k⁻¹ a) = act Rg k⁻¹ a from hg] using
      (adjacent_act_iff Rg g _ _).mpr hfirst
  have hadx : Adjacent Rg (act Rg k⁻¹ a) (act Rg x d) := by
    simpa only [show act Rg x (act Rg k⁻¹ a) = act Rg k⁻¹ a from hx] using
      (adjacent_act_iff Rg x _ _).mpr had
  have hcol : color Rg (act Rg k⁻¹ a) = false := (p.act k⁻¹).start_color
  have mapJ (d₀ : Vertex Rg) (had₀ : Adjacent Rg (act Rg k⁻¹ a) d₀) :
      (edgeOffenderJoin (act Rg k⁻¹ a) d₀).map (MulAut.conj k⁻¹).toMonoidHom =
        edgeOffenderJoin a (act Rg k d₀) := by
    rw [←remaining_edge_join_act h e hz hk u (Or.inr hR) hcol had₀ k,cancel]
  have hm₁ := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hgen₁
  have hm₂ := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hgen₂
  have hmJ := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hpair
  change (Q Rg d ⊔ Z Rg (act Rg k⁻¹ z)).map _ = _ at hm₁
  change (Q Rg (act Rg x d) ⊔ Z Rg (act Rg k⁻¹ z)).map _ = _ at hm₂
  change (edgeOffenderJoin (act Rg k⁻¹ a) d ⊔
    edgeOffenderJoin (act Rg k⁻¹ a) (act Rg x d)).map _ = _ at hmJ
  rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,cancel,cancel,hd] at hm₁
  rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,cancel,cancel,hdx] at hm₂
  rw [Subgroup.map_sup,mapJ d had,mapJ _ hadx,←stabilizer_act,cancel,hd,hdx] at hmJ
  have hmN := le_normalizer_map (MulAut.conj k⁻¹).toMonoidHom
    (mem_map_of_mem (MulAut.conj k⁻¹).toMonoidHom hnorm)
  rw [mapJ _ hfirst] at hmN
  have hvert : act Rg k ((p.act k⁻¹).walk.getVert 1) = p.walk.getVert 1 := by
    simp only [CriticalPath.act,actWalk_getVert,cancel]
  rw [hvert] at hmN
  refine ⟨g',hg',x',hx',hm₁,hm₂,hmJ,?_⟩
  simpa only [x',MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using hmN

include h e hz hk in
/-- Both generating selector choices are critical in the nonsplit branch.
Their proper movers generate the whole starting stabilizer. Each full
restricted-kernel join is normalized by the same endpoint omega subgroup,
and both whole-seed commutators are nonzero. -/
theorem borel_nonsplit_paired_backward
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hn : X Rg a ≠ U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) :
    ∃ g ∈ stabilizer Rg a, ∃ x ∈ stabilizer Rg a,
      let d := act Rg g (p.walk.getVert 1)
      let c := act Rg g (p.walk.getVert 2)
      let v := p.walk.getVert (p.walk.length-2)
      Q Rg d ⊔ Z Rg z = stabilizer Rg a ∧
      Q Rg (act Rg x d) ⊔ Z Rg z = stabilizer Rg a ∧
      edgeOffenderJoin a d ⊔ edgeOffenderJoin a (act Rg x d) = stabilizer Rg a ∧
      x ∈ normalizer (edgeOffenderJoin a (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
      X Rg z ≤ normalizer (((Z Rg c ⊓ Q Rg v) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg z ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg v) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      ⁅Z Rg c,Z Rg v⁆ ≠ ⊥ ∧ ⁅Z Rg (act Rg x c),Z Rg v⁆ ≠ ⊥ ∧
      ∃ (q₁ : CriticalPath Rg (sourceGeometry h) c v)
        (q₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) v),
        q₁.walk.getVert 1 = d ∧ q₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ p.walk.length-2, q₁.walk.getVert (i+2) = p.walk.getVert i) ∧
        (∀ i ≤ p.walk.length-2, q₂.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm⟩ :=
    borel_paired_generating_transports h e hz hk u hR p hp
  have hgen₂' : Q Rg (act Rg (g*x) (p.walk.getVert 1)) ⊔ Z Rg z = stabilizer Rg a := by
    simpa only [act_mul] using hgen₂
  obtain ⟨hN₁,hH₁,q₁,hq₁,ho₁⟩ :=
    borel_nonsplit_generating_shift h e hz hk hb u hR p hp hn g hg hgen₁
  have hh₂ := borel_nonsplit_generating_shift h e hz hk hb u hR p hp hn (g*x)
    ((stabilizer Rg a).mul_mem hg hx) hgen₂'
  obtain ⟨hN₂,hH₂,hex₂⟩ := hh₂
  rw [act_mul] at hex₂
  obtain ⟨q₂,hq₂,ho₂⟩ := hex₂
  simp only [act_mul] at hN₂ hH₂ hq₂
  exact ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hN₁,hN₂,hH₁,hH₂,q₁,q₂,hq₁,hq₂,ho₁,ho₂⟩

include h e hz hk in
/-- The actual three-shift terminal configuration supplies both reverse
selected critical paths in the distinct-mover branch. Their full restricted
kernels are normalized by the whole last omega subgroup, and both selected
seeds have nonzero commutator with the preceding seed. -/
theorem borel_three_shift_reverse_choices
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path)
    (hne : edgeOffenderJoin r.start t.edge ≠ edgeOffenderJoin t.start t.edge) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ∃ g ∈ stabilizer Rg v, ∃ x ∈ stabilizer Rg v,
      let d := act Rg g (t.path.walk.getVert (t.path.walk.length-1))
      let c := act Rg g (t.path.walk.getVert (t.path.walk.length-2))
      Q Rg d ⊔ Z Rg t.start = stabilizer Rg v ∧
      Q Rg (act Rg x d) ⊔ Z Rg t.start = stabilizer Rg v ∧
      edgeOffenderJoin v d ⊔ edgeOffenderJoin v (act Rg x d) = stabilizer Rg v ∧
      x ∈ normalizer (edgeOffenderJoin v
        (t.path.walk.getVert (t.path.walk.length-1)) : Set (FreeAmalgam Rg)) ∧
      X Rg t.start ≤ normalizer (((Z Rg c ⊓ Q Rg r.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg t.start ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg r.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      ⁅Z Rg c,Z Rg r.start⁆ ≠ ⊥ ∧ ⁅Z Rg (act Rg x c),Z Rg r.start⁆ ≠ ⊥ ∧
      ∃ (s₁ : CriticalPath Rg (sourceGeometry h) c r.start)
        (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) r.start),
        s₁.walk.getVert 1 = d ∧ s₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ t.path.walk.length-2,
          s₁.walk.getVert (i+2) = t.path.walk.getVert (t.path.walk.length-i)) ∧
        (∀ i ≤ t.path.walk.length-2,
          s₂.walk.getVert (i+2) = t.path.walk.getVert (t.path.walk.length-i)) := by
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let rev : CriticalPath Rg (sourceGeometry h) v t.start :=
    { start_color := t.path.end_color
      walk := t.path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,t.path.shortest,SimpleGraph.dist_comm]
      critical := reverse_pair h e t.path }
  have hcore := (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2
  have hn₀ := borel_opposite_containing_core_nonsplit h e hz hk u hR
    r.path.start_color t.path.start_color t.adjacent_start t.adjacent_shift hne hcore
  have hn : X Rg v ≠ U Rg v ⊔
      (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg))) := by
    intro hs
    exact hn₀ (omega_generation_transport t.path.end_color r.path.start_color hs)
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hs : (Q Rg t.start).relIndex (Z Rg v) < 4 := by rw [ht.2.2.1]; decide
  have hv (i : ℕ) : rev.walk.getVert i = t.path.walk.getVert (t.path.walk.length-i) := by
    exact SimpleGraph.Walk.getVert_reverse _ _
  have hlen : rev.walk.length = t.path.walk.length := SimpleGraph.Walk.length_reverse _
  have htlen : t.path.walk.length = sourceDistance h := t.path.length_eq_b
  have hrlast : rev.walk.getVert (rev.walk.length-2) = r.start := by
    rw [hv,hlen,show t.path.walk.length-(t.path.walk.length-2)=2 by omega]
    simpa only [SimpleGraph.Walk.getVert_zero] using t.overlap 0 (by omega)
  obtain ⟨g,hg,x,hx,hg₁,hg₂,hpair,hnorm,hN₁,hN₂,hH₁,hH₂,s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩ :=
    borel_nonsplit_paired_backward h e hz hk hb u hR rev hs hn
  simp only [hrlast,hv] at hN₁ hN₂ hH₁ hH₂ hg₁ hg₂ hpair hnorm
  have hex : ∃ (s₁ : CriticalPath Rg (sourceGeometry h) (act Rg g (rev.walk.getVert 2))
      (rev.walk.getVert (rev.walk.length-2)))
      (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x (act Rg g (rev.walk.getVert 2)))
      (rev.walk.getVert (rev.walk.length-2))),
      s₁.walk.getVert 1 = act Rg g (rev.walk.getVert 1) ∧
      s₂.walk.getVert 1 = act Rg x (act Rg g (rev.walk.getVert 1)) ∧
      (∀ i ≤ t.path.walk.length-2,
        s₁.walk.getVert (i+2) = t.path.walk.getVert (t.path.walk.length-i)) ∧
      (∀ i ≤ t.path.walk.length-2,
        s₂.walk.getVert (i+2) = t.path.walk.getVert (t.path.walk.length-i)) := by
    exact ⟨s₁,s₂,hs₁,hs₂,fun i hi => (ho₁ i (hlen.symm ▸ hi)).trans (hv i),
      fun i hi => (ho₂ i (hlen.symm ▸ hi)).trans (hv i)⟩
  rw [hrlast,hv,hv] at hex
  exact ⟨g,hg,x,hx,hg₁,hg₂,hpair,hnorm,hN₁,hN₂,hH₁,hH₂,hex⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
