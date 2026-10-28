module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCommonKernel
public import Theory.Representation.BinaryPermutation.SixCoreSylowLower
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent

/-!
# Exact movement of the common critical kernel

In the order-sixteen radical-image branch above distance four, an unequal
neighboring small mover has fixed index exactly eight on the opposite full
moved cover. The strict lower bound is already proved in `SylowAdjacent`.
For the upper bound, every two-subgroup of S₆ fixes at least four vectors
in the augmentation core; the marked-cover comparison retains both the
order-sixteen and order-thirty-two possibilities.

Suppose the first edge core moves the small critical line. The common full
critical kernel has index four in the starting seed and edge displacement
of order at most two. An unequal mover cannot centralize that kernel:
otherwise its fixed index on the moved cover would be at most four. Hence
its displacement is exactly the entire edge displacement, of order two,
contained in the edge seed and fixed by the whole edge core.

For the mover at the second vertex, the transported critical path preserves
the first three vertices. Its two full kernels intersect in precisely the
orbit-fixed kernel above. The final application uses the literal restricted
original radical and its original embedding. No new Sylow assumption is
imposed, and no kernel is replaced by its intersection in a statement about
that individual kernel.

These are local estimates for the non-elementary source branch, retaining
the unequal-mover and critical-line-movement branch hypotheses. They do not
supply backward critical selection or either terminal distance exclusion.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.4)--(5.5), printed pp.915--917, and the small-kernel comparisons
in (5.7)--(5.9), printed pp.919--921.
-/

public noncomputable section
open Theory.GroupTheory
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

private theorem cover_two_group_fixed_bound (s : FullSymmetricAction h e hz hn d)
    (A : Subgroup d.overgroup) (hA : IsPGroup 2 A) :
    fixedCodim (coverAction s) (A.map s.projection) ≤ 3 := by
  have hc := SixCoreSylow.four_le_card_fixed_of_twoGroup
    (A.map s.projection) (hA.map s.projection)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  have hd : 2 ≤ Module.finrank (ZMod 2)
      (fixedSpace (coreRepresentation (Fin 6)) (A.map s.projection)) := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show Module.finrank (ZMod 2)
        (fixedSpace (coreRepresentation (Fin 6)) (A.map s.projection)) ≤ 1 by omega)
    omega
  have hh := (cover_model s).fixedCodim_bounds (A.map s.projection)
  simp only [Subgroup.map_id] at hh
  apply hh.2.trans
  have he := fixedCodim_add_finrank (coreRepresentation (Fin 6)) (A.map s.projection)
  rw [finrank_core] at he
  simp only [Fintype.card_fin] at he
  omega

private theorem cover_two_group_fixed_index_eight
    (s : FullSymmetricAction h e hz hn d)
    (A : Subgroup d.overgroup) (hA : IsPGroup 2 A)
    (hlarge : 4 < (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d)) :
    (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) = 8 := by
  let := replacementMoved_normal h d
  have hi := NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (replacementMoved d) s.projection s.surjective
    (s.projection_kernel.trans (moved_centralizer s).symm) A
  change (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) =
    2 ^ fixedCodim (coverAction s) (A.map s.projection) at hi
  have hbound := cover_two_group_fixed_bound s A hA
  have hgt : 2 < fixedCodim (coverAction s) (A.map s.projection) := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh
    rw [hi] at hlarge
    omega
  rw [hi,show fixedCodim (coverAction s) (A.map s.projection) = 3 by omega]
  norm_num

include e hz hn in
/-- The strict fixed-index comparison for unequal neighboring movers is
exact: each fixes an index-eight subgroup of the opposite full moved cover. -/
theorem sixteen_unequal_neighbor_fixed_index_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  have hET : E ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hES : E ≤ stabilizer d.radical a := hET.trans
    (fun _ hx => hx.2 a (adjacent_symm d.radical hat))
  have hm : (E.comap i).map i = E := map_comap_eq_self (hES.trans_eq hir.symm)
  have hER : E.comap i ≤ d.radical := by
    have hh := comap_mono (f := i) hET
    rwa [←hiR,comap_map_eq_self_of_injective hinj] at hh
  have hidx := SmallMover.centralizer_index_map i hinj (replacementMoved d) (E.comap i)
  rw [hiU,hm] at hidx
  have hlarge := (SylowAdjacent.sixteen_unequal_neighbor_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat hct hne).2
  dsimp only
  rw [hidx]
  exact cover_two_group_fixed_index_eight s _
    ((replacement_radical_isPGroup h d).of_injective (inclusion hER)
      (inclusion_injective hER)) (by rwa [←hidx])

include e hz hn in
/-- An unequal neighboring mover realizes the entire nontrivial displacement
of the common full critical kernel under the first edge core. -/
theorem sixteen_unequal_common_kernel_displacement_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hct : Adjacent d.radical c (p.walk.getVert 1))
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let E := SmallMover.join (U d.radical c) (Q d.radical c) T 4
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    ⁅F,E⁆ = ⁅F,T⁆ ∧ Nat.card (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅F,E⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
      ⁅F,E⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  let T := Q d.radical (p.walk.getVert 1)
  let E := SmallMover.join (U d.radical c) (Q d.radical c) T 4
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  have hcontrol := SylowCommonKernel.moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall (hT.symm ▸ hmove)
  dsimp only at hcontrol
  rw [hT] at hcontrol
  change F = _ ∧ F.relIndex (Z d.radical a) = 4 ∧
    Nat.card (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
    ⁅F,T⁆ ≤ Z d.radical (p.walk.getVert 1) ∧ ⁅F,T⁆ ≤ centralizer (T : Set _) at hcontrol
  have hidx := (SylowAdjacent.sixteen_unequal_neighbor_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hne).2
  have hET : E ≤ T := SmallMover.join_le _ _ _ _
  have hle : ⁅F,E⁆ ≤ ⁅F,T⁆ := commutator_mono le_rfl hET
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hcontrol.2.2.2.1) (inclusion_injective _)
  let : Finite (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hle) (inclusion_injective _)
  have hne' : ⁅F,E⁆ ≠ ⊥ := by
    intro hzFE
    have hFC : F ≤ centralizer (E : Set _) := commutator_eq_bot_iff_le_centralizer.mp hzFE
    have hbound := (relIndex_le_of_le_left hFC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)
    exact (not_lt_of_ge (hbound.trans_eq hcontrol.2.1)) hidx
  have hpos := (one_lt_card_iff_ne_bot (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical))).mpr hne'
  have hcardE := (card_le_of_le hle).trans hcontrol.2.2.1
  have hcardEq : Nat.card (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by omega
  have heq : ⁅F,E⁆ = ⁅F,T⁆ := eq_of_le_of_card_ge hle (by omega)
  exact ⟨heq,hcardEq,hle.trans hcontrol.2.2.2.1,hle.trans hcontrol.2.2.2.2⟩

include e hz hn in
/-- The full common kernel of the two selected paths has nontrivial
order-two displacement under the second mover. Both original kernels and
all three initial vertices are retained. -/
theorem sixteen_second_mover_kernel_displacement_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hne : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
      (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let E := SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2)) T 4
    ∃ x ∈ E, x ∈ T ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x⁻¹ a'),
        (∀ i, q.walk.getVert i = act d.radical x⁻¹ (p.walk.getVert i)) ∧
        q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = p.walk.getVert 2 ∧
        let K := Z d.radical a ⊓ Q d.radical a'
        let K' := Z d.radical a ⊓ Q d.radical (act d.radical x⁻¹ a')
        let F := K ⊓ K'
        K ⊔ K' = Z d.radical a ∧ F.relIndex (Z d.radical a) = 4 ∧
          F = Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _) ∧
          T ≤ normalizer (F : Set (FreeAmalgam d.radical)) ∧
          ⁅F,E⁆ = ⁅F,T⁆ ∧ Nat.card (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
          ⁅F,E⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
          ⁅F,E⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  let T := Q d.radical (p.walk.getVert 1)
  let E := SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2)) T 4
  let F₀ := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt,q,hq,hq1,hq2,_,hjoin,hindex,hnorm,_⟩ :=
    SylowAdjacent.sixteen_second_mover_critical_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hne hmove
  let K := Z d.radical a ⊓ Q d.radical a'
  let K' := Z d.radical a ⊓ Q d.radical (act d.radical x⁻¹ a')
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  have hcontrol := SylowCommonKernel.moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall (hT.symm ▸ hmove)
  dsimp only at hcontrol
  rw [hT] at hcontrol
  have hF : F₀ = ⨅ t : T, K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom := hcontrol.1
  have hFK : F₀ ≤ K := by
    rw [hF]
    have hh := iInf_le (fun t : T => K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom) 1
    have he : (MulAut.conj ((1 : T) : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro y
      change (1 : FreeAmalgam d.radical) * y * (1 : FreeAmalgam d.radical)⁻¹ = y
      simp only [one_mul,inv_one,mul_one]
    rwa [he,Subgroup.map_id] at hh
  have hFK' : F₀ ≤ K' := by
    rw [hF]
    have hh := iInf_le (fun t : T => K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom) ⟨x,hxt⟩
    have hxZ : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp
        (Z_normalized d.radical a (hxt.2 a (adjacent_symm d.radical hat)))
    have hkm : K.map (MulAut.conj x).toMonoidHom = K' := by
      dsimp only [K,K']
      rw [map_inf _ _ _ (MulAut.conj x).injective,hxZ,Q_act,inv_inv]
    exact hh.trans_eq hkm
  have hFpair : F₀ = K ⊓ K' := by
    have hle : F₀ ≤ K ⊓ K' := le_inf hFK hFK'
    have hi := relIndex_mul_relIndex F₀ (K ⊓ K') (Z d.radical a) hle
      (inf_le_left.trans (show K ≤ Z d.radical a from inf_le_left))
    rw [hindex,hcontrol.2.1] at hi
    exact le_antisymm hle (relIndex_eq_one.mp (by omega))
  have hd := sixteen_unequal_common_kernel_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hct hne hmove
  change ⁅F₀,E⁆ = ⁅F₀,T⁆ ∧ Nat.card (⁅F₀,E⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ⁅F₀,E⁆ ≤ Z d.radical (p.walk.getVert 1) ∧ ⁅F₀,E⁆ ≤ centralizer (T : Set _) at hd
  rw [hFpair] at hd
  exact ⟨x,hx,hxt,q,hq,hq1,hq2,hjoin,hindex,hFpair.symm,hnorm,hd⟩

include e hz hn in
/-- Application to the literal restricted original radical and its embedding.
In this order-sixteen branch the two full path kernels have a nontrivial
common displacement, and the second mover has fixed index eight on either
permitted moved cover. No Sylow hypothesis on the original input is added. -/
theorem original_sylow_second_mover_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hne : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
        (((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)) 4)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let E := SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2)) T 4
    (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical (alpha d.radical)) = 8 ∧
      ∃ x ∈ E, x ∈ T ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) (act d.radical x⁻¹ a'),
          (∀ i, q.walk.getVert i = act d.radical x⁻¹ (p.walk.getVert i)) ∧
          q.walk.getVert 1 = beta d.radical ∧ q.walk.getVert 2 = p.walk.getVert 2 ∧
          let K := Z d.radical (alpha d.radical) ⊓ Q d.radical a'
          let K' := Z d.radical (alpha d.radical) ⊓ Q d.radical (act d.radical x⁻¹ a')
          let F := K ⊓ K'
          K ⊔ K' = Z d.radical (alpha d.radical) ∧ F.relIndex (Z d.radical (alpha d.radical)) = 4 ∧
            F = Z d.radical (alpha d.radical) ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _) ∧
            T ≤ normalizer (F : Set (FreeAmalgam d.radical)) ∧
            ⁅F,E⁆ = ⁅F,T⁆ ∧ Nat.card (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
            ⁅F,E⁆ ≤ Z d.radical (beta d.radical) ∧
            ⁅F,E⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  rw [hfirst,SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hT
  have hne' : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
      (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4 := by rwa [hfirst,←hT]
  have hm : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hfirst,←hT]
  have hi := sixteen_unequal_neighbor_fixed_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hne'
  have hp := sixteen_second_mover_kernel_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hne' hm
  dsimp only at hi hp ⊢
  rw [hfirst,←hT] at hi hp
  exact ⟨hi,hp⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelMovement
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
