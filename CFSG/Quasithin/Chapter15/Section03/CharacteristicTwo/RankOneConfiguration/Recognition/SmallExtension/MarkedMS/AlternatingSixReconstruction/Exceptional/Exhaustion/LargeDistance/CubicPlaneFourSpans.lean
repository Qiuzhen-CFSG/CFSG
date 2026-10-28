module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLargeShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFourExclusion

/-!
# Large-image spans at distance four in the remaining cubic branches

For a large critical image at distance four, the general backward path
ends at the original midpoint. Reversing that path and using critical
nonnormality proves that the midpoint's entire moving cover escapes the
starting Baumann slice. This step applies to every radical image.

In the remaining plane and Borel branches the controlled even subactor
has a generating edge. Transport the original midpoint to this edge.
If its seed lay in the old midpoint core, the controlled actor would put
that seed in the Baumann slice. Thus the transported seed and original
midpoint form a critical pair inside the same original selected span,
which is consequently nonabelian.

Its central quotient is elementary abelian and has action kernel contained
in E. A common-core index at most two would make the controlled even
involution fix a subgroup of index at most two in that quotient, contrary
to the even-lift displacement bound. Both the common-core index and the
forward Baumann index therefore exceed two. All paths use the actual
cubic graph, with the same transporter and complete overlap.

The vertex transport and whole-core and literal C.1.32 applications retain
both moving covers and the nontrivial kernel quotient E/Q. These are
strict-slice and nonabelian-span conclusions in the large-image
distance-four branch. They do not supply its terminal contradiction,
the compatible small-image choices, larger-distance R4/R6 calculations,
either core exhaustion or the final reconstruction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.2)(iv), (5.7)--(5.8), printed pp.919--920, and the selected
central-quotient argument of (5.12)(2), pp.925--926;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
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
/-- At distance four a large critical image forces the original midpoint's
moving cover to escape the starting Baumann slice, for every radical image. -/
theorem large_critical_four_forward_eligible
    (hb : sourceDistance h = 4)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a)) :
    ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨d,_,g,_,q,_,hover⟩ := large_critical_backward_path h e hz hk p hat hlarge
  let rev : CriticalPath Rg (sourceGeometry h)
      (p.walk.getVert (p.walk.length-2)) (act Rg g d) :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.start_color]
          exact sourceDistance_pos h) _ q.end_color q.critical⟩
  have hq2 : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hr2 : rev.walk.getVert 2 = a := by
    change q.walk.reverse.getVert 2 = a
    rw [SimpleGraph.Walk.getVert_reverse,
      show q.walk.length-2=2 from by
        have hh : q.walk.length = 4 := q.length_eq_b.trans hb
        omega,hq2]
  have hn := critical_start_not_le_second_slice h e hz (by omega) rev
  simpa only [hl,Nat.reduceSub,hr2] using hn

include h e hz hk in
private theorem large_four_nonabelian_span_core_index
    (hb : sourceDistance h = 4)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)))
    (hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    2 < (Q Rg (p.walk.getVert 2)).relIndex
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) := by
  by_contra! hindex
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hd : (cosetGraph Rg).dist (p.walk.getVert 2) (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    (localZSpan_le_V Rg hd).trans ((sourceGeometry h).V_local _ rfl hb2)
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let := selected_span_central_quotient_elementary h e hz hk hb2 (p.walk.getVert 2) hd
  let ρ := forwardSpanCentralAction Rg (p.walk.getVert 2)
  let σ := Offenders.linearize ρ
  have hker : σ.ker ≤ (π).ker := by
    rw [CubicAction.projection_kernel]
    apply le_trans ?_ (selected_span_central_action_kernel_le_extension h e hz hk hb2 p hnon)
    intro m hm
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro v
    exact congrArg Additive.toMul (LinearMap.congr_fun hm (Additive.ofMul v))
  obtain ⟨A,hAU,hdisp,a,haA,ha,heven⟩ := critical_radius_even_actor h e hz hk p hlarge
  obtain ⟨m,hm,rfl⟩ := haA
  have hcomm : ⁅P ⊓ Q Rg (p.walk.getVert 2),A⁆ ≤ Z Rg (alpha Rg) := by
    have he : p.walk.length-2 = 2 := by omega
    rw [he] at hdisp
    exact (commutator_mono (inf_le_inf_right _ (localZSpan_le_V Rg hd)) le_rfl).trans hdisp
  have hfixed := selected_span_actor_fixed_index h hb2 p hd hindex A hcomm m hm
  have hup := linearized_cyclic_codim_le_one ρ m hfixed
  change fixedCodim σ (zpowers m) ≤ 1 at hup
  have hlo := EvenLift.fixedCodim_lower π (CubicEven.projection_surjective h e hz hk)
    σ hker m heven ha
  omega

include h e hz hk in
/-- In both remaining cubic branches, a large critical path at distance four
has a nonabelian original selected span and a backward critical path through
a generating edge. Both its core index and its forward slice exceed two. -/
theorem large_remaining_four_span_configuration
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))) :
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
    2 < (Q Rg (p.walk.getVert 2)).relIndex
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) ∧
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ∧
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ g ∈ stabilizer Rg (alpha Rg),
      act Rg g (p.walk.getVert 1) = t ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
        (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha Rg ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (act Rg g (p.walk.getVert 2))) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat₁ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hdelta : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨A,hAU,htwo,hAn,hdisp,t,hat,hgen⟩ :=
    large_remaining_generating_actor h e hz hk u hR p hlarge
  have hAZ : A ≤ Z Rg a' := hAU.trans (DistanceEight.U_le_Z Rg a')
  have hZG : Z Rg a' ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical
  have hAG := hAZ.trans hZG
  have hgenZ : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) :=
    le_antisymm (sup_le (le_sup_left.trans hgen.le) hZG)
      (hgen.symm.le.trans (sup_le_sup_left hAZ _))
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hat₁ hat
  let c := act Rg g (p.walk.getVert 2)
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hdelta
  have hcol : color Rg c = false := by
    rw [action_preserves_color]
    exact (p.vertex_color (by omega)).mpr (by decide)
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hel := large_critical_four_forward_eligible h e hz hk hb p hlarge
  have helc : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hh
    apply hel
    change U Rg (act Rg g (p.walk.getVert 2)) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hbad : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    intro hh
    apply helc
    exact (DistanceEight.U_le_Z Rg c).trans
      (controlled_backward_kernel_le_slice h e hz hb2 p A hAG htwo hAn hdisp hat hct
        hgen (Z Rg c) le_rfl hh ((show Q Rg t ≤ stabilizer Rg c from
          fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c)))
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb2) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      p.prepend_two_overlap (Nat.le_of_lt hb2) hcol w hw hbad (i := 0) (Nat.zero_le _)
  have hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    have hcP : Z Rg (p.walk.getVert 2) ≤ P := Z_le_localZSpan Rg _ _
    have hgP : Z Rg c ≤ P := by
      rw [Z_act]
      exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg _ _ ((stabilizer Rg (alpha Rg)).inv_mem hg)))
    intro hn
    apply critical_commutator_not_central h e hz hk q
    exact (commutator_mono hgP (by simpa only [hl,Nat.reduceSub] using hcP)).trans (hn ▸ bot_le)
  have hi := large_four_nonabelian_span_core_index h e hz hk hb p hlarge hnon
  have hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
    by_contra! hs
    exact (Nat.not_le_of_gt hi) (selected_span_index_of_forward_slice h e hz hk hb2 p hs).2
  refine ⟨hnon,hi,hs,t,hat,hgenZ,g,hg,hgt,?_⟩
  have hs' : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
    dsimp only [c]
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hs
  have hout : ∃ q : CriticalPath Rg (sourceGeometry h) c
      (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha Rg ∧
      (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) :=
    ⟨q,hqt,hq2,fun i hi => p.prepend_two_overlap _ _ _ _ _ (by omega),hs'⟩
  rw [show p.walk.length-2=2 from by omega] at hout
  exact hout

include h e hz hk in
/-- The strict distance-four slice bound transports along the actual cubic
action, retaining the original critical path and its midpoint. -/
theorem large_remaining_four_forward_slice_strict_at
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a)) :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ a'),
      p₀.walk.getVert 2 = act Rg g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hlarge₀ : 4 ≤ (Q Rg (act Rg g⁻¹ a')).relIndex (Z Rg (alpha Rg)) := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hlarge
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) (by change 2 < sourceDistance h; omega) g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := (large_remaining_four_span_configuration h e hz hk hb u hR p₀ hlarge₀).2.2.1
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

omit hk in
include h e hz in
/-- Whole-core assembly supplies strict forward slices for all large critical
images at distance four in both remaining cubic branches. -/
theorem coreExhaustion_or_cubic_remaining_four_slices :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        (sourceDistance h = 4 → ∀ a a'
          (p : CriticalPath Rg (sourceGeometry h) a a'),
          4 ≤ (Q Rg a').relIndex (Z Rg a) →
          2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2))) := by
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hR⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,hR,fun hb4 a a' p hlarge =>
      large_remaining_four_forward_slice_strict_at h e hz hk hb4 u hR p hlarge⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the strict large-image distance-four slices,
with the full cubic kernel and both complete moving covers retained. -/
theorem rankTwo_or_cubic_remaining_four_slices :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        (sourceDistance h = 4 → ∀ a a'
          (p : CriticalPath Rg (sourceGeometry h) a a'),
          4 ≤ (Q Rg a').relIndex (Z Rg a) →
          2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2))) :=
  (coreExhaustion_or_cubic_remaining_four_slices h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
