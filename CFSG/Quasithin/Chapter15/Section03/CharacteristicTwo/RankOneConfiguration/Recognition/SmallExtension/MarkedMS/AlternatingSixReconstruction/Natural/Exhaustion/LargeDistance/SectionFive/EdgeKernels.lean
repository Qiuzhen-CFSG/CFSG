module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.KernelTransport

/-!
# Full critical kernels at the two end edges

For a small critical image, the full starting kernel is normalized by the
first edge kernel exactly when the critical commutator lies in the first
edge seed. The proof uses the kernel--line normalizer identity and the
literal omega-center definition of the edge seed.

When the original radical has abelian symmetric image, its derived group
lies in the local two-core. Consequently the first edge normalizes the
critical commutator. That commutator has order two, so the edge fixes it.
Reversing the same walk gives both end-seed containments and normalization
of both full critical kernels. The replacement application retains the
noncentral critical line and both possible cover orders; it does not
remove the central line of the order-thirty-two cover.

This is the abelian radical-image branch of the edge calculations used in
MS93 (5.7)--(5.11), printed pp.919--924, using (3.3)(ii), pp.866--867.
The normalization argument adapts SymplecticSetup.LargeDistance and
BackwardEscape to the full cover. It does not assume a full point-core
image. The source-selected shifts, strict indices and intermediate R4/R6
noncentrality, the remaining (5.12) estimates, and final distance assembly
remain with qt-e-ms-small-a6-exhaustion-large-distance. Unconditional
reconstruction remains with qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem edge_derived_le_core_of_abelian_image
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical a := by
  have hr : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup := by
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    exact hab
  have hbase : ⁅Q d.radical (beta d.radical),Q d.radical (beta d.radical)⁆ ≤
      Q d.radical (alpha d.radical) := by
    rw [Q_beta,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),←map_commutator]
    exact map_mono hr
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [map_commutator,←Q_act,←Q_act] at hh
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
  · rw [hg.1] at ha
    cases ha

private theorem fixed_mod_central_normalizes_line {H : Type*} [Group H]
    (A Q D : Subgroup H) (hAQ : A ≤ normalizer (Q : Set H))
    (hDQ : D ≤ normalizer (Q : Set H))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set H)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup H) : Set H) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set H) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'

include s in
/-- An abelian radical image places the actual small critical line in the
first edge seed, for either central cover. -/
theorem small_critical_line_le_first_seed_of_abelian_image
    (hc : DistanceTwo.CentralLayer d)
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical (p.walk.getVert 1) := by
  let t := p.walk.getVert 1
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hpos
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    rw [p.start_color] at hn
    cases he : color d.radical t <;> simp_all
  have hAe : Z d.radical a' ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant a' p.end_color]
    change p.walk.length - 1 < replacementDistance h d
    have hlen : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have htG : Q d.radical t ≤ stabilizer d.radical a := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have htZ := htG.trans (Z_normalized d.radical a)
  have hcomm : ⁅Q d.radical t,Z d.radical a'⁆ ≤ centralizer
      (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono le_rfl hAe).trans
      (edge_derived_le_core_of_abelian_image s hab p.start_color hat)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
  have hnorm : Q d.radical t ≤ normalizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm (Z d.radical a)]
    exact fixed_mod_central_normalizes_line (Z d.radical a') (Z d.radical a) (Q d.radical t)
      (hAe.trans htZ) htZ hcomm
  have hfix : ⁅Z d.radical a,Z d.radical a'⁆ ≤ centralizer
      (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hnorm.trans (normalizer_le_centralizer_of_card_two _
      (small_critical_commutator_card s hc p hsmall)))
  have hlineZ : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hZQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant a p.start_color]
    exact replacementDistance_pos h d
  have hlineQ := (hlineZ.trans hZQ).trans (Q_le_adjacent_h d.radical ht hat)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  intro x hx
  change x ∈ Z d.radical t
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr
    ⟨hlineQ hx,elemPow_eq_one_of_isElementaryAbelian x (hlineZ hx),hfix hx⟩

include s in
/-- Normality of the full critical kernel under the first edge is exactly
containment of the critical line in that edge's seed. -/
theorem small_critical_kernel_normalized_iff_first_seed
    (hc : DistanceTwo.CentralLayer d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    Q d.radical (p.walk.getVert 1) ≤ normalizer
        ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ↔
      ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical (p.walk.getVert 1) := by
  let t := p.walk.getVert 1
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hpos
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have htG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hlineZ : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hZQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant a p.start_color]
    exact replacementDistance_pos h d
  have hlineQ := (hlineZ.trans hZQ).trans (Q_le_adjacent_h d.radical ht hat)
  have he := small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall
  constructor
  · intro hn
    have hfix := le_inf htG hn
    rw [he] at hfix
    have hcent := le_centralizer_iff.mp (hfix.trans inf_le_right)
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
    intro x hx
    change x ∈ Z d.radical t
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr
      ⟨hlineQ hx,elemPow_eq_one_of_isElementaryAbelian x (hlineZ hx),hcent hx⟩
  · intro hseed
    have hfix : ⁅Z d.radical a,Z d.radical a'⁆ ≤ centralizer
        (Q d.radical t : Set (FreeAmalgam d.radical)) := by
      intro x hx
      have hxt := hseed hx
      change x ∈ Z d.radical t at hxt
      rw [Z,if_neg (by simp [ht])] at hxt
      exact (mem_omegaCenter_iff.mp hxt).2.2
    have hh := le_inf htG (le_centralizer_iff.mp hfix)
    rw [←he] at hh
    exact hh.trans inf_le_right

include s in
/-- The original walk is reversed literally, so both seed containments refer
to its own first and last edges. -/
theorem small_critical_line_le_end_seeds_of_abelian_image
    (hc : DistanceTwo.CentralLayer d)
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ⁅Z d.radical a,Z d.radical a'⁆ ≤
      Z d.radical (p.walk.getVert 1) ⊓ Z d.radical (p.walk.getVert (p.walk.length - 1)) := by
  let q : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hsmall' := (small_critical_indices s hc p hsmall).2
  have hlast := small_critical_line_le_first_seed_of_abelian_image s hc hab q (by omega)
  change ⁅Z d.radical a',Z d.radical a⁆ ≤ Z d.radical (p.walk.reverse.getVert 1) at hlast
  rw [commutator_comm,SimpleGraph.Walk.getVert_reverse] at hlast
  exact le_inf (small_critical_line_le_first_seed_of_abelian_image s hc hab p hsmall) hlast

include s in
/-- Both full endpoint kernels are normalized by their actual incident edge
kernels in the abelian radical-image branch. -/
theorem small_critical_end_kernels_normalized_of_abelian_image
    (hc : DistanceTwo.CentralLayer d)
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    Q d.radical (p.walk.getVert 1) ≤ normalizer
        ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      Q d.radical (p.walk.getVert (p.walk.length - 1)) ≤ normalizer
        ((Z d.radical a' ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hseeds := small_critical_line_le_end_seeds_of_abelian_image s hc hab p hsmall
  refine ⟨(small_critical_kernel_normalized_iff_first_seed s hc p hsmall).mpr
    (hseeds.trans inf_le_left),?_⟩
  let q : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hi := (small_critical_indices s hc p hsmall).2
  have he := (small_critical_kernel_normalized_iff_first_seed s hc q (by omega)).mpr
    (small_critical_line_le_first_seed_of_abelian_image s hc hab q (by omega))
  change Q d.radical (p.walk.reverse.getVert 1) ≤ _ at he
  rwa [SimpleGraph.Walk.getVert_reverse] at he

/-- The actual replacement's small-radius, abelian-image branch supplies
both full kernels and the same noncentral order-two line on the two end seeds.
No fixed-space condition is imposed on the order-thirty-two cover. -/
theorem small_opposite_radius_end_seeds_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (hab : ⁅d.radical.map (fullSymmetricAction_knownSimple h e hz hn d hb).projection,
      d.radical.map (fullSymmetricAction_knownSimple h e hz hn d hb).projection⁆ = ⊥)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 8) :
    let H := ⁅Z d.radical a,Z d.radical a'⁆
    Nat.card H = 2 ∧
      H ≤ Z d.radical (p.walk.getVert 1) ⊓ Z d.radical (p.walk.getVert (p.walk.length - 1)) ∧
      H ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) = ⊥ ∧
      Q d.radical (p.walk.getVert 1) ≤ normalizer
        ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      Q d.radical (p.walk.getVert (p.walk.length - 1)) ≤ normalizer
        ((Z d.radical a' ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := critical_index_two_of_small_opposite_radius s hc hb p hsmall
  exact ⟨small_critical_commutator_card s hc p (by omega),
    small_critical_line_le_end_seeds_of_abelian_image s hc hab p (by omega),
    small_critical_commutator_inf_centralizer s hc p (by omega),
    small_critical_end_kernels_normalized_of_abelian_image s hc hab p (by omega)⟩


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
