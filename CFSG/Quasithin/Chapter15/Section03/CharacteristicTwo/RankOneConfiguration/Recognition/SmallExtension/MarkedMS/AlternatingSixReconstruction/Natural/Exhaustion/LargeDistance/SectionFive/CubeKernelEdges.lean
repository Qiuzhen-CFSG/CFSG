module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallKernel

/-!
# Edge confinement of the three-pair reverse kernel

The three disjoint transpositions act quadratically on the binary
augmentation cover. The proof uses only their pairwise coordinate action;
the natural quotient inherits the same identity. Equivariant transport
therefore puts the full incident seed's commutator with the edge kernel in
the edge seed, retaining both moved-cover orders and the central attachment.
Generating over the radius-two ball gives the whole-radius estimate
[V_a,Q_a] ≤ Z_a; this is not inferred from a selected-span estimate.

For a backward candidate in the second predecessor core, its commutator
with the full reverse critical kernel lies in both end-edge seeds. Hence it
also lies in the starting seed and the second predecessor seed. The actual
nonsylow application retains the same generating pair, cubic, conjugator,
non-normalization witness and every shared vertex from CubeSmallKernel.
It derives the three-pair image and central layer internally.

The surviving commutator still has order two or four. These containments do
not exclude that alternative or prove the small-image shift, strict slices,
MS93 (5.10)--(5.12), or unconditional distance two. The remaining local chain
and both terminal outcomes stay with the large-distance assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2)(ii)--(iii) and the kernel-normalization argument in
(5.7), printed pp.866--867,914--915,919. All graph subgroups and quotient maps
are those of the original minimum characteristic replacement.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeKernelEdges
local notation "ρ" => coreRepresentation (Fin 6)
private def mate (i : Fin 6) : Fin 6 := ![1,0,3,2,5,4] i
private theorem pair_action (j : Fin 8) (i : Fin 6) :
    ((initialWords 3 j).symm i=i ∧ (initialWords 3 j).symm (mate i)=mate i) ∨
    ((initialWords 3 j).symm i=mate i ∧ (initialWords 3 j).symm (mate i)=i) := by
  have h : ∀ j : Fin 8, ∀ i : Fin 6,
    ((initialWords 3 j).symm i=i ∧ (initialWords 3 j).symm (mate i)=mate i) ∨
    ((initialWords 3 j).symm i=mate i ∧ (initialWords 3 j).symm (mate i)=i) := by decide +kernel
  exact h j i

private theorem core_quadratic (g k : S) (hg : g ∈ D 6) (hk : k ∈ D 6) (v : C) :
    ρ k (ρ g v-v)=ρ g v-v := by
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).mp hg
  obtain ⟨l,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) k).mp hk
  apply Subtype.ext
  funext i
  change v.val ((initialWords 3 j).symm ((initialWords 3 l).symm i)) -
    v.val ((initialWords 3 l).symm i) = v.val ((initialWords 3 j).symm i)-v.val i
  rcases pair_action l i with ⟨h1,_⟩ | ⟨h1,_⟩
  · rw [h1]
  · rw [h1]
    rcases pair_action j i with ⟨h2,h3⟩ | ⟨h2,h3⟩
    · rw [h2,h3,sub_self,sub_self]
    · rw [h2,h3,CharTwo.sub_eq_add,CharTwo.sub_eq_add,add_comm]

private theorem natural_quadratic (g k : S) (hg : g ∈ D 6) (hk : k ∈ D 6)
    (v : natural (Fin 6)) :
    naturalRepresentation (Fin 6) k (naturalRepresentation (Fin 6) g v-v)=
      naturalRepresentation (Fin 6) g v-v := by
  obtain ⟨w,rfl⟩ := coreToNatural_surjective v
  have hh := congrArg (coreToNatural (Fin 6)) (core_quadratic g k hg hk w)
  simpa only [map_sub,coreToNatural_equivariant] using hh

private theorem model_quadratic {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y) (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u g k : S) (hg : g ∈ (D 6).map (MulAut.conj u).toMonoidHom)
    (hk : k ∈ (D 6).map (MulAut.conj u).toMonoidHom) (v : Y) :
    σ k (σ g v-v)=σ g v-v := by
  have hbase (a b : S) (ha : a ∈ D 6) (hb : b ∈ D 6) (w : Y) :
      σ b (σ a w-w)=σ a w-w := by
    rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
    · apply E.injective
      simpa only [hE,map_sub,MonoidHom.id_apply] using natural_quadratic a b ha hb (E w)
    · apply E.injective
      simpa only [hE,map_sub,MonoidHom.id_apply] using core_quadratic a b ha hb (E w)
  obtain ⟨a,ha,rfl⟩ := hg
  obtain ⟨b,hb,rfl⟩ := hk
  have hh := congrArg (σ u) (hbase a b ha hb (σ u⁻¹ v))
  change σ (u*b*u⁻¹) (σ (u*a*u⁻¹) v-v)=σ (u*a*u⁻¹) v-v
  simpa only [MulAut.conj_apply,map_mul,Module.End.mul_apply,map_sub,
    (σ).self_inv_apply,(σ).inv_self_apply] using hh

end CubeKernelEdges

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

include s in
private theorem cube_cover_commutator_fixed (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom) :
    ⁅replacementMoved d,d.radical⁆ ≤ centralizer (d.radical : Set d.overgroup) := by
  let := replacementMoved_normal h d
  apply commutator_le.mpr
  intro v hv r hr k hk
  have hm : ⁅v,r⁆ ∈ replacementMoved d :=
    (commutator_le_left (replacementMoved d) d.radical) (commutator_mem_commutator hv hr)
  let w : Additive (replacementMoved d) := Additive.ofMul ⟨⁅v,r⁆,hm⟩
  have he : coverAction s (s.projection k) w=w := by
    dsimp only [w]
    rw [NormalElementaryQuotient.vector_commutator (replacementMoved d)
      s.projection s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)
      ⟨v,hv⟩ r]
    have hh := CubeKernelEdges.model_quadratic (coverAction s) (cover_model s)
      u (s.projection r) (s.projection k)
      (hR (mem_map_of_mem _ hr)) (hR (mem_map_of_mem _ hk)) (Additive.ofMul ⟨v,hv⟩)
    change coverAction s (s.projection k)
      (Additive.ofMul ⟨v,hv⟩-coverAction s (s.projection r) (Additive.ofMul ⟨v,hv⟩)) =
      Additive.ofMul ⟨v,hv⟩-coverAction s (s.projection r) (Additive.ofMul ⟨v,hv⟩)
    simpa only [map_sub,neg_sub] using congrArg Neg.neg hh
  have he' := congrArg (fun a : Additive (replacementMoved d) => (a.toMul : d.overgroup)) he
  rw [coverAction_conjugate] at he'
  exact mul_inv_eq_iff_eq_mul.mp he'

include s in
/-- The three-pair radical fixes every commutator with the full incident
vertex seed. The central attachment in the order-32 cover is retained. -/
theorem cube_edge_seed_commutator_le (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ⁅Z d.radical a,Q d.radical t⁆ ≤ Z d.radical t := by
  have hm : ⁅U d.radical a,Q d.radical t⁆ ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    have hb : ⁅U d.radical (alpha d.radical),Q d.radical (beta d.radical)⁆ ≤
        centralizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) := by
      rw [hc.U_eq_moved,Q_beta,←map_commutator]
      exact (map_mono (cube_cover_commutator_fixed s u hR)).trans
        (map_centralizer_le_centralizer_image _ _)
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
    · rcases hg with ⟨rfl,rfl⟩
      have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hb).trans
        (map_centralizer_le_centralizer_image _ _)
      change (⁅U d.radical (alpha d.radical),Q d.radical (beta d.radical)⁆ :
        Subgroup (FreeAmalgam d.radical)).map (MulAut.conj g⁻¹).toMonoidHom ≤
        centralizer ((Q d.radical (beta d.radical)).map
          (MulAut.conj g⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
      rw [map_commutator,←U_act,←Q_act] at hh
      simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
    · rw [hg.1] at ha
      cases ha
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hZQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ ha)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ ha]
    exact replacementDistance_pos h d
  have hZt : Z d.radical a ≤ Q d.radical t := hZQ.trans (Q_le_adjacent_h d.radical ht hat)
  have hfix : ⁅Z d.radical a,Q d.radical t⁆ ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat]
    apply commutator_sup_le_of_relative_normal (Q d.radical t)
    · exact (Q d.radical t).le_normalizer.trans (normalizer_le_normalizer_centralizer _)
    · exact (DistanceEight.U_le_Z d.radical a).trans hZt
    · exact (adjacent_Z_le d.radical ha hat).trans hZt
    · exact hm
    · exact (commutator_eq_bot_iff_le_centralizer.mpr hseed).le.trans bot_le
  have hle : ⁅Z d.radical a,Q d.radical t⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q d.radical t ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical a))
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a ha
  intro x hx
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr
    ⟨hZt (hle hx),elemPow_eq_one_of_isElementaryAbelian x (hle hx),hfix hx⟩

include s in
/-- A backward candidate remaining in the second predecessor core has its
full reverse-kernel commutator in both literal end-edge seeds. -/
theorem cube_backward_kernel_le_edge_seeds
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical a⁆
    H ≤ Z d.radical t ⊓ Z d.radical (p.walk.getVert (p.walk.length-1)) ∧
      H ≤ Z d.radical a ⊓ Z d.radical (p.walk.getVert (p.walk.length-2)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hfirst : ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical a⁆ ≤ Z d.radical t :=
    (commutator_mono le_rfl (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat))).trans
      (cube_edge_seed_commutator_le s hc u hR hcol hct)
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hlast : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have hpt : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hpre : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    have hh := adjacent_color_ne d.radical hpt
    rw [hlast] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-2)) <;> simp_all
  have hend : ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical a⁆ ≤
      Z d.radical (p.walk.getVert (p.walk.length-1)) := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left
      (hbad.trans (Q_le_adjacent_h d.radical hlast hpt))).trans
        (cube_edge_seed_commutator_le s hc u hR p.end_color het)
  exact ⟨le_inf hfirst hend,le_inf (hfirst.trans (adjacent_Z_le d.radical p.start_color hat))
    (hend.trans (adjacent_Z_le d.radical hpre hpt))⟩

include s in
/-- In the three-pair branch the whole radius, and not just a selected span,
has its commutator with the starting core in the starting seed. -/
theorem cube_radius_core_commutator_le_seed
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (a : Vertex d.radical) (ha : color d.radical a = false) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ Z d.radical a := by
  have hlocal (c : Vertex d.radical) (hd : (cosetGraph d.radical).dist c a ≤ 2) :
      Z d.radical c ≤ stabilizer d.radical a :=
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hd)).trans
      ((replacementGeometry h d).V_local a ha
        (by rw [(replacementGeometry h d).distance_constant a ha]; exact hb))
  have hbound (c : Vertex d.radical) (hd : (cosetGraph d.radical).dist c a ≤ 2) :
      ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a := by
    have hcases : (cosetGraph d.radical).dist c a=0 ∨
        (cosetGraph d.radical).dist c a=1 ∨ (cosetGraph d.radical).dist c a=2 := by omega
    rcases hcases with h0 | h1 | h2
    · have he := (cosetGraph_connected d.radical).dist_eq_zero_iff.mp h0
      subst c
      exact (Z_centralizes_Q d.radical a ha).le.trans bot_le
    · have hca : Adjacent d.radical c a :=
        (cosetGraph_adj d.radical _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      exact (commutator_mono (adjacent_Z_le d.radical ha (adjacent_symm d.radical hca)) le_rfl).trans
        ((Z_centralizes_Q d.radical a ha).le.trans bot_le)
    · obtain ⟨t,hct,hat⟩ := exists_common_neighbor_of_dist_two d.radical c a h2
      have hcol : color d.radical c=false :=
        (color_eq_of_dist_even d.radical c a (by rw [h2]; decide)).trans ha
      have ht : color d.radical t=true := by
        have hh := adjacent_color_ne d.radical hat
        rw [ha] at hh
        cases he : color d.radical t <;> simp_all
      exact ((commutator_mono le_rfl (Q_le_adjacent_h d.radical ht hat)).trans
        (cube_edge_seed_commutator_le s hc u hR hcol hct)).trans
          (adjacent_Z_le d.radical ha hat)
  change ⁅⨆ c, ⨆ (_ : (cosetGraph d.radical).dist c a ≤ 2), Z d.radical c,Q d.radical a⁆ ≤ _
  apply commutator_iSup_le_of_relative_normal (stabilizer d.radical a)
  · exact Z_normalized d.radical a
  · intro c
    exact iSup_le (hlocal c)
  · intro c
    exact commutator_iSup_le_of_relative_normal (stabilizer d.radical a)
      (Q d.radical a) (Z d.radical a) (fun _ => Z d.radical c)
      (Z_normalized d.radical a) (hlocal c) (hbound c)

include e hz hn in
/-- The actual nonsylow replacement supplies the three-pair image internally;
the entire radius-core commutator lies in its seed at every component vertex. -/
theorem nonsylow_four_lt_radius_core_commutator_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    (a : Vertex d.radical) (ha : color d.radical a=false) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ Z d.radical a := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  exact cube_radius_core_commutator_le_seed s hc hb u hR a ha

include e hz hn in
/-- On the actual nonsylow minimum replacement, retain the selected cubic,
neighbor transporter and overlapping walk. Its remaining kernel obstruction
lies in both end-edge seeds and both intervening component seeds. -/
theorem nonsylow_small_backward_edge_obstruction_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
            stabilizer d.radical (alpha d.radical) ∧
          ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
            ((z=a' ∧ ∀ i, q.walk.getVert i=p.walk.getVert i) ∨
              (z=act d.radical x a' ∧ ∀ i, q.walk.getVert i=act d.radical x (p.walk.getVert i))) ∧
            (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            (¬ Z d.radical z ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
              Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∧
            ((∃ v : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
                (q.walk.getVert (q.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ q.walk.length-2, v.walk.getVert (i+2)=q.walk.getVert i) ∨
              (Z d.radical (act d.radical g delta) ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) ∧
                let H := ⁅Z d.radical (act d.radical g delta),Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆
                (Nat.card H=2 ∨ Nat.card H=4) ∧
                H ≤ Z d.radical (act d.radical g delta) ⊓ Z d.radical z ∧
                H ≤ Z d.radical t ⊓ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧
                H ≤ Z d.radical (alpha d.radical) ⊓ Z d.radical (q.walk.getVert (q.walk.length-2)) ∧
                H ≤ centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
                ¬ H ≤ centralizer (stabilizer d.radical (act d.radical g delta) : Set (FreeAmalgam d.radical)))) := by
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,hgen,z,q,hq,hqs,hnorm,hcases⟩ :=
    nonsylow_small_backward_bounded_obstruction_knownSimple (e := e) (hz := hz) (hn := hn)
      hb4 hns p hsmall hdelta hel
  refine ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,hgen,z,q,hq,hqs,hnorm,?_⟩
  rcases hcases with hpath | ⟨hbad,hcard,hseed,hcent,hncent⟩
  · exact Or.inl hpath
  · have hb : 2 < replacementDistance h d := by omega
    let s := fullSymmetricAction_knownSimple h e hz hn d hb
    have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
    obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hns
    have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
      rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
    have he := cube_backward_kernel_le_edge_seeds s hc hb u hR q hat hct hbad
    exact Or.inr ⟨hbad,hcard,hseed,he.1,he.2,hcent,hncent⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
