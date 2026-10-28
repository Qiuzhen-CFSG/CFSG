module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelLine

/-!
# Simultaneous reverse kernels for the three-pair branch

A selected order-two reverse-kernel commutator need not be invariant under
the whole starting stabilizer. The generating configuration has two critical
seeds. This module retains both, with their original cubic relation, and
proves the common-kernel normalization required by the strict-slice argument.

If both backward candidates are trapped, let A and A' be their full reverse
critical kernels, with the backward vertex c and starting vertex a fixed.
The common fixer F = C_{Z_c}(A join A') is edge-invariant because the edge
acts abelianly on the full seed. Each critical seed normalizes F Z_a, by
the small predecessor-commutator estimate. The generating pair therefore
makes F Z_a normal in the starting stabilizer. Its order over Z_a is at most
four, using the full three-pair edge index on both covers. The small normal
section theorem puts F in the starting Baumann slice.

Consequently the source's strict slice index greater than two forces
[U_c,A join A'] to have order greater than two. For the selected endpoint
which fails normalization, the earlier line bound gives |[Z_c,A]| = 2.
This line is centralized by the common edge, by its actual edge-seed
containment. If [Z_c,A'] lay in it, relative-normal commutator generation
would contradict the strict bound. Thus the second kernel moves outside
the selected line.

The original nonsylow application constructs the three-pair image and
transports the strict slice through the same neighbor conjugator. It either
constructs a backward critical walk with every overlapping vertex, or retains
both trapped walks and their separated commutators. This is not yet exclusion
of that pair, and no whole-stabilizer centrality of the line is asserted.
The pair exclusion, small-slice argument, terminal contradictions, original
Sylow branches and distance-four obligations remain with this owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.5)--(5.7), printed pp.866--867,915--919. The last
source proof uses two seed candidates and the strict inequality >q (q=2).
The edge-invariance and normal-section proofs adapt the existing SmallBackward
and CubeSmallSeeds arguments to the simultaneous kernels. All graph objects,
quotient maps and central attachments belong to the original replacement;
both moved-cover orders sixteen and thirty-two are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)
namespace CubePairedKernel
private theorem abelian_action_preserves_fixed {H : Type*} [Group H]
    (P V A : Subgroup H) (hPV : P ≤ normalizer (V : Set H)) (hA : A ≤ P)
    (hcom : ⁅P,P⁆ ≤ centralizer (V : Set H)) :
    P ≤ normalizer ((V ⊓ centralizer (A : Set H) : Subgroup H) : Set H) := by
  let f : P →* MulAut V := V.normalizerMonoidHom.comp (inclusion hPV)
  have hf (p q : P) : Commute (f p) (f q) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    ext v
    change ⁅(p:H),(q:H)⁆*(v:H)*⁅(p:H),(q:H)⁆⁻¹ = (v:H)
    rw [←hcom (commutator_mem_commutator p.property q.property) v v.property,mul_inv_cancel_right]
  apply le_normalizer_iff.mpr
  intro g hg v hv
  have hgv : g*v*g⁻¹ ∈ V := (mem_normalizer_iff.mp (hPV hg) v).mp hv.1
  refine ⟨hgv,?_⟩
  intro a ha
  have hvfix : f ⟨a,hA ha⟩ ⟨v,hv.1⟩ = (⟨v,hv.1⟩:V) := by
    apply Subtype.ext
    change a*v*a⁻¹ = v
    rw [hv.2 a ha,mul_inv_cancel_right]
  have hh := DFunLike.congr_fun (hf ⟨a,hA ha⟩ ⟨g,hg⟩).eq (⟨v,hv.1⟩:V)
  change f ⟨a,hA ha⟩ (f ⟨g,hg⟩ ⟨v,hv.1⟩) = f ⟨g,hg⟩ (f ⟨a,hA ha⟩ ⟨v,hv.1⟩) at hh
  rw [hvfix] at hh
  have he : a*(g*v*g⁻¹)*a⁻¹ = g*v*g⁻¹ := congrArg Subtype.val hh
  exact mul_inv_eq_iff_eq_mul.mp he

include s in
private theorem edge_preserves_seed_fixer (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t) :
    Q d.radical t ≤ normalizer ((Z d.radical c ⊓ centralizer
      (A : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
  let : IsElementaryAbelian 2 ((D 6).map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
  let helem : IsElementaryAbelian 2 (d.radical.map s.projection) := IsElementaryAbelian.of_le hR
  have hbase : ⁅Q d.radical (beta d.radical),Q d.radical (beta d.radical)⁆ ≤
      Q d.radical (alpha d.radical) := by
    rw [Q_beta,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),←map_commutator]
    apply map_mono
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  have hderived : ⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
      rw [map_commutator,←Q_act,←Q_act] at hh
      simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
    · rw [hg.1] at hcol
      cases hcol
  have htG : Q d.radical t ≤ stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  exact abelian_action_preserves_fixed _ _ A (htG.trans (Z_normalized d.radical c)) hA
    (hderived.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c hcol))))

include s in
private theorem normal_small_radius_le_slice
    (hb : 2 < replacementDistance h d)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYV : Y ≤ V d.radical (alpha d.radical))
    (hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hindex : (Z d.radical (alpha d.radical)).relIndex Y ≤ 8) :
    Y ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let f := embedM d.radical
  let Y₀ := Y.comap f
  let Z₀ := (Z d.radical (alpha d.radical)).comap f
  have hg (m : d.overgroup) : f m ∈ stabilizer d.radical (alpha d.radical) := by
    change f m ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : Y₀.Normal := ⟨by
    intro v hv m
    change f (m*v*m⁻¹) ∈ Y
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hYN (hg m)) (f v)).mp hv⟩
  let : Z₀.Normal := ⟨by
    intro v hv m
    change f (m*v*m⁻¹) ∈ Z d.radical (alpha d.radical)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized d.radical _) (hg m)) (f v)).mp hv⟩
  have hVQ : V d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) :=
    V_le_Q d.radical rfl hb
  have hYG : Y ≤ f.range := (hYV.trans ((replacementGeometry h d).V_local _ rfl hb)).trans_eq
    (stabilizer_m_base d.radical)
  have hYm : Y₀.map f = Y := map_comap_eq_self hYG
  have hZm : Z₀.map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  have hYker : Y₀ ≤ s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hYm,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact hYV.trans hVQ
  have hk : IsPGroup 2 s.projection.ker := s.projection_kernel.symm ▸ pCore_isPGroup
  have hi : Z₀.relIndex Y₀ ≤ 8 := by
    rw [relIndex_comap,hYm]
    exact hindex
  have hh := map_mono (f := f)
    (commutator_pResidual_le_of_symmetricSix_small_section s.projection s.surjective hk Y₀ Z₀ hYker hi)
  rw [map_commutator,hYm,hZm,←Ltilde_alpha] at hh
  intro v hv
  apply (mem_B_iff d.radical _ ((replacementGeometry h d).Z_normal _)
    ((replacementGeometry h d).V_local _ rfl hb) v).mpr
  refine ⟨hYV hv,fun l hl => ?_⟩
  rw [commutator_comm] at hh
  exact hh (commutator_mem_commutator hl hv)

include s in
private theorem cube_backward_product_index (u : S)
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t) :
    (Z d.radical (alpha d.radical)).relIndex
      (Z d.radical c ⊔ Z d.radical (alpha d.radical)) ≤ 4 := by
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change color d.radical c ≠ color d.radical t at h2
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hZaQ : Z d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ rfl]
    exact replacementDistance_pos h d
  have hZaN : Z d.radical (alpha d.radical) ≤ normalizer
      (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    (hZaQ.trans (Q_le_adjacent_h d.radical ht hat)).trans
      ((show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c))
  let := finite_Z d.radical c
  let := finite_Z d.radical (alpha d.radical)
  rw [relIndex_sup_of_normalizes _ _ hZaN]
  exact (relIndex_le_of_le_left (adjacent_Z_le d.radical rfl hat)
    index_ne_zero_of_finite).trans_eq (cube_edge_seed_index s u hfull hcol hct)


end CubePairedKernel
include s in
/-- The common fixed subgroup of two trapped reverse kernels lies in the
starting slice. Both selected critical seeds are used in the normalization
argument, with the original edge and full central attachments. -/
theorem cube_paired_trapped_fixer_le_slice
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' b' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) b')
    (hps : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hqs : (Q d.radical b').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical b' = stabilizer d.radical (alpha d.radical))
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))) :
    Z d.radical c ⊓ centralizer
      ((Z d.radical a' ⊓ Q d.radical (alpha d.radical) ⊔
        Z d.radical b' ⊓ Q d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
          Set (FreeAmalgam d.radical)) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let A := Z d.radical a' ⊓ Q d.radical (alpha d.radical) ⊔
    Z d.radical b' ⊓ Q d.radical (alpha d.radical)
  let F := Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  let Y := F ⊔ Z d.radical (alpha d.radical)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hZV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hFt := CubePairedKernel.edge_preserves_seed_fixer s u hfull.le hcol hct A
    ((sup_le inf_le_right inf_le_right).trans (Q_le_adjacent_h d.radical ht hat))
  have hmove {z : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
      (hrs : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
      (hrbad : Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2)))
      (hA : Z d.radical z ⊓ Q d.radical (alpha d.radical) ≤ A) :
      Z d.radical z ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    have hFmove : ⁅F,Z d.radical z⁆ ≤ Z d.radical (alpha d.radical) :=
      small_critical_predecessor_commutator s hc hb r hrs F (inf_le_left.trans hrbad)
        (inf_le_right.trans (centralizer_le hA))
    have hYmove : ⁅Y,Z d.radical z⁆ ≤ Z d.radical (alpha d.radical) :=
      commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
        F (Z d.radical (alpha d.radical)) (Z d.radical z) (Z d.radical (alpha d.radical))
        (Z_normalized d.radical _) ((inf_le_left.trans hZV).trans
          ((replacementGeometry h d).V_local _ rfl hb)) (Z_le_stabilizer d.radical _) hFmove
        (((critical_Z_commutator_le_moving (h := h) r).trans inf_le_left).trans
          (DistanceEight.U_le_Z d.radical _))
    exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  have hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ (hmove p hps hpbad le_sup_left)) (hmove q hqs hqbad le_sup_right)
    exact (le_inf hFt ((show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hYV : Y ≤ V d.radical (alpha d.radical) :=
    sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical _ 2)
  let := finite_Z d.radical c
  let := finite_Z d.radical (alpha d.radical)
  have hYprod : Y ≤ Z d.radical c ⊔ Z d.radical (alpha d.radical) := sup_le_sup inf_le_left le_rfl
  have hprodG : Z d.radical c ⊔ Z d.radical (alpha d.radical) ≤
      stabilizer d.radical (alpha d.radical) :=
    sup_le (hZV.trans ((replacementGeometry h d).V_local _ rfl hb)) (Z_le_stabilizer d.radical _)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite (Z d.radical c ⊔ Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hprodG) (inclusion_injective _)
  have hindex : (Z d.radical (alpha d.radical)).relIndex Y ≤ 8 :=
    ((relIndex_le_of_le_right hYprod index_ne_zero_of_finite).trans
      (CubePairedKernel.cube_backward_product_index s u hfull hat hct)).trans (by decide)
  exact le_sup_left.trans (CubePairedKernel.normal_small_radius_le_slice s hb Y hYV hYN hindex)

include s in
/-- With the strict source slice bound, two trapped candidates have joint
reverse-kernel movement larger than a line. An order-two commutator alone
cannot supply the two-seed normalization argument. -/
theorem cube_paired_trapped_joint_movement_gt_two
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' b' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) b')
    (hps : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hqs : (Q d.radical b').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical b' = stabilizer d.radical (alpha d.radical))
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    2 < Nat.card (⁅U d.radical c,
      Z d.radical a' ⊓ Q d.radical (alpha d.radical) ⊔
        Z d.radical b' ⊓ Q d.radical (alpha d.radical)⁆ : Subgroup (FreeAmalgam d.radical)) := by
  by_contra! hcard
  let A := Z d.radical a' ⊓ Q d.radical (alpha d.radical) ⊔
    Z d.radical b' ⊓ Q d.radical (alpha d.radical)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hAG : A ≤ stabilizer d.radical c :=
    ((sup_le inf_le_right inf_le_right).trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hi := moving_small_commutator_fixed_index s hc hcol A hAG hcard
  have hFB := cube_paired_trapped_fixer_le_slice s hc hb u hfull p q hps hqs hat hct hgen hpbad hqbad
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hh := relIndex_le_of_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z d.radical c)).trans hFB)
    (index_ne_zero_of_finite (H := (U d.radical c ⊓ centralizer
      (A : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical c)))
  rw [inf_relIndex_left] at hh
  exact (Nat.not_le_of_gt hindex) (hh.trans hi)

include s in
/-- If the selected trapped endpoint fails normalization, its obstruction is
a line and the other trapped endpoint moves outside that line. The strict
slice bound is essential; the line is only centralized by the common edge. -/
theorem cube_paired_trapped_kernels_separate
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' b' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) b')
    (hps : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hqs : (Q d.radical b').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical b' = stabilizer d.radical (alpha d.radical))
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hnorm : ¬ Z d.radical a' ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆
    Nat.card H = 2 ∧ H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
      ¬ ⁅Z d.radical c,Z d.radical b' ⊓ Q d.radical (alpha d.radical)⁆ ≤ H := by
  let A := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let A' := Z d.radical b' ⊓ Q d.radical (alpha d.radical)
  let H := ⁅Z d.radical c,A⁆
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have he := cube_backward_kernel_le_edge_seeds s hc hb u hfull.le p hat hct hpbad
  have hHedge : H ≤ Z d.radical t := he.1.trans inf_le_left
  have hHc : H ≤ Z d.radical c := hHedge.trans (adjacent_Z_le d.radical hcol hct)
  have hHcentral : H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro y hy
    have hh := hHedge hy
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hZG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical) := by
    have hZQ : Z d.radical c ≤ Q d.radical c := by
      apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ hcol)
      rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ hcol]
      exact replacementDistance_pos h d
    exact (hZQ.trans (Q_le_adjacent_h d.radical ht hct)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hne : H ≠ ⊥ := by
    intro hzero
    have hmove := small_critical_predecessor_commutator s hc hb p hps
      (Z d.radical c) hpbad (commutator_eq_bot_iff_le_centralizer.mp hzero)
    have hZmove : ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ≤
        Z d.radical (alpha d.radical) :=
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)
    have hh := commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      (Z d.radical c) (Z d.radical (alpha d.radical)) (Z d.radical a')
      (Z d.radical (alpha d.radical)) (Z_normalized d.radical _) hZG
      (Z_le_stabilizer d.radical _) hmove hZmove
    exact hnorm (le_normalizer_iff_commutator_le_left.mpr (hh.trans le_sup_right))
  let := finite_Z d.radical c
  let : Finite H := Finite.of_injective (inclusion hHc) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot _).mpr hne
  have hupper := cube_backward_kernel_card_le_two s hc hb u hfull.le p hps hat hct hpbad hnorm
  have hcard : Nat.card H=2 := by change Nat.card H ≤ 2 at hupper; omega
  refine ⟨hcard,hHcentral,?_⟩
  intro hother
  have hHN : Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hHcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hbound : ⁅U d.radical c,A ⊔ A'⁆ ≤ H := by
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal (Q d.radical t) A A' (U d.radical c) H hHN
      (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat))
      (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat))
    · rw [commutator_comm]
      exact commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl
    · rw [commutator_comm]
      exact (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl).trans hother
  have hlarge := cube_paired_trapped_joint_movement_gt_two s hc hb u hfull p q hps hqs
    hat hct hgen hpbad hqbad hindex
  have hle : Nat.card (⁅U d.radical c,A ⊔ A'⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 :=
    (card_le_of_le hbound).trans_eq hcard
  exact (Nat.not_le_of_gt hlarge) hle

include e hz hn in
/-- The strict source slice on the original nonsylow replacement either
produces a backward critical path or separates the two actual reverse-kernel
commutators. The same cubic, neighbor conjugator, generating pair and both
entire critical walks are retained. No centrality in a vertex stabilizer is
inferred from the order of the selected line. -/
theorem nonsylow_strict_small_backward_separated_obstruction_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            let c := act d.radical g delta
            let P := Z d.radical c ⊔ Z d.radical (alpha d.radical)
            let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆
            let H' := ⁅Z d.radical c,Z d.radical (act d.radical x a') ⊓ Q d.radical (alpha d.radical)⁆
            (¬ Z d.radical a' ≤ normalizer (P : Set (FreeAmalgam d.radical)) ∨
              ¬ Z d.radical (act d.radical x a') ≤ normalizer (P : Set (FreeAmalgam d.radical))) ∧
            ((∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (p.walk.getVert (p.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i) ∨
              (∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (q.walk.getVert (q.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ q.walk.length-2, v.walk.getVert (i+2)=q.walk.getVert i) ∨
              (Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
                Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) ∧
                ((¬ Z d.radical a' ≤ normalizer (P : Set (FreeAmalgam d.radical)) ∧
                    Nat.card H=2 ∧ H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧ ¬ H' ≤ H) ∨
                  (¬ Z d.radical (act d.radical x a') ≤ normalizer (P : Set (FreeAmalgam d.radical)) ∧
                    Nat.card H'=2 ∧ H' ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧ ¬ H ≤ H')))) := by
  have hb : 2 < replacementDistance h d := by omega
  have hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,q,hq,hqs,hgen,hnorm⟩ :=
    nonsylow_small_paired_seed_obstruction_knownSimple (e := e) (hz := hz) (hn := hn)
      hb4 hns p hsmall hdelta hel
  let c := act d.radical g delta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  refine ⟨t,hat,g,hg,hgt,hct,hstrict,x,hx,hxN,hx3,q,hq,hqs,hgen,hnorm,?_⟩
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change color d.radical c ≠ color d.radical t at h2
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hpath {z : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
      (hescape : ¬ Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2))) :
      ∃ v : CriticalPath d.radical (replacementGeometry h d) c (r.walk.getVert (r.walk.length-2)),
        v.walk.getVert 1=t ∧ ∀ i ≤ r.walk.length-2, v.walk.getVert (i+2)=r.walk.getVert i := by
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length=2 := rfl
    let v := r.prepend_two (Nat.le_of_lt hb) hcol w hw hescape
    have hvt : v.walk.getVert 1=t := by
      simp only [v,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact ⟨v,hvt,fun i hi => r.prepend_two_overlap _ _ _ _ _ hi⟩
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · by_cases hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))
    · refine Or.inr (Or.inr ⟨hpbad,hqbad,?_⟩)
      let s := fullSymmetricAction_knownSimple h e hz hn d hb
      have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
      obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
        (e := e) (hz := hz) (hn := hn) hb4 hns
      have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
        rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
      rcases hnorm with hnp | hnq
      · exact Or.inl ⟨hnp,cube_paired_trapped_kernels_separate s hc hb u hfull p q hsmall hqs
          hat hct hgen hpbad hqbad hstrict hnp⟩
      · have hgen' : Q d.radical t ⊔ Z d.radical (act d.radical x a') ⊔ Z d.radical a' =
            stabilizer d.radical (alpha d.radical) := by
          calc
            _ = Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') := by ac_rfl
            _ = _ := hgen
        exact Or.inr ⟨hnq,cube_paired_trapped_kernels_separate s hc hb u hfull q p hqs hsmall
          hat hct hgen' hqbad hpbad hstrict hnq⟩
    · exact Or.inr (Or.inl (hpath q hqbad))
  · exact Or.inl (hpath p hpbad)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
