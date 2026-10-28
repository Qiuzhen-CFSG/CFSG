module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedResidual


/-!
# Mixed-plane backward shifts and radius escape

The unique transposition in a mixed four-group controls a family of actors:
if each actor has fixed index at most two on the full moved cover, so does
their generated subgroup. Edge coordinates give the same statement for the
literal replacement graph, including the order-thirty-two central cover.

For a small critical pair, suppose the relative-normalizer orbit of a
backward seed lies in the predecessor core. The conjugates of the reverse
kernel then have commutators of order at most two on that seed. Their common
fixer has index at most two. Its orbit span centralizes the reverse kernel,
and the source small-critical estimate makes it normal modulo the starting
seed. The radius action theorem places it in the Baumann subgroup. Thus a
strict slice cannot have its whole orbit trapped. Holomorph realization gives
a backward critical walk with its slice index and every common vertex retained.
The starting and edge-stabilizer transporters are kept separate.

If the whole starting radius were trapped, this argument would bound every
slice on the original graph by two. The established residual rotation of the
nonzero-kernel alternative constructs a large critical image, whereas the
small predecessor slice forces that same image to have order two. This proves
radius escape without a critical-image or slice premise. The universal escape
contract is applied to extend every critical path and establish forward and
reciprocal slice eligibility.

These are the mixed-plane source (5.7)--(5.8) steps. The strict forward-slice
and terminal distance exclusions, larger Sylow images, and the distance-four
residual-core estimates still require proof before LargeDistanceInput and
unconditional replacement distance two can be asserted. The original radical,
minimum characteristic replacement, graph, quotient maps and both covers are
unchanged.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.7)--(5.8), printed pp.866--867 and 919--920. The common
fixed-space calculation uses the existing marked six-point action; the final
escape consumer is the literal source-(2.2)(v) graph interface.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement Pointwise
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEscape
local notation "S" => Equiv.Perm (Fin 6)

private theorem mixed_swap_unique (a b : S) (ha : a ∈ plus) (hb : b ∈ plus)
    (hsa : a.IsSwap) (hsb : b.IsSwap) : a = b := by
  have h : ∀ i : Fin 4, (planeWords 0 i).cycleType = {2} → planeWords 0 i = swap45 := by
    decide +kernel
  obtain ⟨i, rfl⟩ := (mem_plus_iff a).mp ha
  obtain ⟨j, rfl⟩ := (mem_plus_iff b).mp hb
  exact (h i (Equiv.Perm.isSwap_iff_cycleType.mp hsa)).trans
    (h j (Equiv.Perm.isSwap_iff_cycleType.mp hsb)).symm

private theorem conjugate_mixed_swap_unique (u a b : S)
    (ha : a ∈ plus.map (MulAut.conj u).toMonoidHom)
    (hb : b ∈ plus.map (MulAut.conj u).toMonoidHom)
    (hsa : a.IsSwap) (hsb : b.IsSwap) : a = b := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  have hs (x : S) (hx : ((MulAut.conj u) x).IsSwap) : x.IsSwap := by
    obtain ⟨i, j, hij, he⟩ := hx
    have hh := congrArg (MulAut.conj u⁻¹) he
    have hi : (MulAut.conj u⁻¹) ((MulAut.conj u) x) = x := by
      change u⁻¹*(u*x*u⁻¹)*(u⁻¹)⁻¹=x
      group
    rw [hi] at hh
    change x = u⁻¹*Equiv.swap i j*(u⁻¹)⁻¹ at hh
    rw [←Equiv.swap_apply_apply] at hh
    exact ⟨_, _, u.symm.injective.ne hij, hh⟩
  exact congrArg (MulAut.conj u) (mixed_swap_unique a b ha hb (hs a hsa) (hs b hsb))

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem cover_small_actor_sup_index
    (s : FullSymmetricAction h e hz hn d) (u : S)
    (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {I : Sort*} (A : I → Subgroup d.overgroup)
    (hA : ∀ i, A i ≤ d.radical)
    (hsmall : ∀ i, (centralizer (A i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    (centralizer ((⨆ i, A i : Subgroup d.overgroup) : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
  let := replacementMoved_normal h d
  have hc (i : I) : fixedCodim (coverAction s) ((A i).map s.projection) ≤ 1 := by
    have hi := hsmall i
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hi
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hi
  have hn (i : I) : fixedCodim (naturalRepresentation (Fin 6)) ((A i).map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) ((A i).map s.projection)).trans (hc i)
  have hm (i : I) : (A i).map s.projection ≤ plus.map (MulAut.conj u).toMonoidHom :=
    (map_mono (hA i)).trans_eq him
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (replacementMoved d) s.projection s.surjective
    (s.projection_kernel.trans (moved_centralizer s).symm), Subgroup.map_iSup]
  change 2 ^ fixedCodim (coverAction s) (⨆ i, (A i).map s.projection) ≤ 2
  by_cases hall : ∀ i, (A i).map s.projection = ⊥
  · simp only [hall, iSup_bot]
    rw [(fixedCodim_eq_zero_iff (coverAction s) ⊥).mpr (fixedSpace_bot (coverAction s))]
    decide
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨x,hx,hsx,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers _ hi (hn i)
    have hle : ∀ j, (A j).map s.projection ≤ (A i).map s.projection := by
      intro j
      by_cases hj : (A j).map s.projection = ⊥
      · rw [hj]; exact bot_le
      obtain ⟨y,hy,hsy,he'⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers _ hj (hn j)
      have hxy := conjugate_mixed_swap_unique u x y (hm i hx) (hm j hy) hsx hsy
      rw [he,he',hxy]
    have heq : (⨆ j, (A j).map s.projection) = (A i).map s.projection :=
      le_antisymm (iSup_le hle) (le_iSup (fun j : I => (A j).map s.projection) i)
    rw [heq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (hc i)

private theorem mixed_small_actor_sup_index
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d) (u : S)
    (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    {J : Sort*} (A : J → Subgroup (FreeAmalgam d.radical))
    (hA : ∀ j, A j ≤ Q d.radical t)
    (hsmall : ∀ j, (centralizer (A j : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2) :
    (centralizer ((⨆ j, A j : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_⟩
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hiR,hiQ,hiU⟩ := hcoords

  have hmA (j : J) : ((A j).comap i).map i = A j :=
    map_comap_eq_self ((hA j).trans (hiR ▸ map_le_range i _))
  have hAr (j : J) : (A j).comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hmA,hiR]
    exact hA j
  have hidx (j : J) : (centralizer ((A j).comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    have hh := hsmall j
    rw [←hiU,←hmA j,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hh
    exact hh
  have hh := cover_small_actor_sup_index s u him (fun j => (A j).comap i) hAr hidx
  have hm : (⨆ j, (A j).comap i).map i = ⨆ j, A j := by rw [Subgroup.map_iSup]; simp only [hmA]
  rw [←hiU,←hm,←inf_relIndex_right,inf_comm,
    map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
    inf_relIndex_left]
  exact hh

private theorem trapped_slice_bound
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (htrapped : conjugateSpanBy (Z d.radical c)
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical)) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2 := by
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical (alpha d.radical)
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let H := conjugateSpanBy K N
  let C := Z d.radical c ⊓ centralizer (H : Set (FreeAmalgam d.radical))
  let E := conjugateSpanBy C N
  let Y := E ⊔ Z d.radical (alpha d.radical)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases ht : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hc : color d.radical c <;> simp_all
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hZV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    le_iSup_of_le c (le_iSup_of_le hdist le_rfl)
  have hEV : E ≤ V d.radical (alpha d.radical) := conjugateSpanBy_le
    (inf_le_left.trans hZV) (inf_le_right.trans (DistanceEight.V_normalized d.radical _))
  have hEQ : E ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    (conjugateSpanBy_mono (show C ≤ Z d.radical c from inf_le_left) le_rfl).trans htrapped
  have hHK : K ≤ H := le_conjugateSpanBy K N
  have hNH : N ≤ normalizer (H : Set (FreeAmalgam d.radical)) :=
    le_normalizer_conjugateSpanBy K N
  have hEH : E ≤ centralizer (H : Set (FreeAmalgam d.radical)) :=
    conjugateSpanBy_le inf_le_right (hNH.trans (normalizer_le_normalizer_centralizer _))
  have hEK : E ≤ centralizer (K : Set (FreeAmalgam d.radical)) := hEH.trans (centralizer_le hHK)
  have hmove : ⁅E,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    small_critical_predecessor_commutator s hc hb p hp E hEQ hEK
  have hYV : Y ≤ V d.radical (alpha d.radical) := sup_le hEV (Z_le_VBall d.radical _ 2)
  have hYmove : ⁅Y,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      E (Z d.radical (alpha d.radical)) (Z d.radical a') (Z d.radical (alpha d.radical))
      (Z_normalized d.radical _) (hEV.trans ((replacementGeometry h d).V_local _ rfl hb))
      (Z_le_stabilizer d.radical _) hmove
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _))
  have hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le
      ((le_inf (le_normalizer_conjugateSpanBy C N)
        (inf_le_right.trans (Z_normalized d.radical _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _))
      (le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right))
  have hCB : C ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    (le_conjugateSpanBy C N).trans (le_sup_left.trans
      (normalized_radius_le_slice_of_critical_commutator s hc hb p Y hYV hYN hYmove))
  have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [him]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  let D := ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
  have hbound : Nat.card D ≤ 2 := small_critical_kernel_predecessor_card s hc hb u hR p hp
  have hlast : D ≤ Z d.radical (p.walk.getVert (p.walk.length-1)) :=
    small_critical_predecessor_commutator_le_last_seed s hc hb u hR p hp
  let := finite_Z d.radical (p.walk.getVert (p.walk.length-1))
  let : Finite D := Finite.of_injective (inclusion hlast) (inclusion_injective _)
  have hQN : N ≤ normalizer (Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (Q_normalized d.radical _)
  have hKt : ∀ g : N, K.map (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom ≤ Q d.radical t := by
    intro g
    apply le_trans _ (Q_le_adjacent_h d.radical ht hat)
    exact (map_mono (show K ≤ Q d.radical (alpha d.radical) from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hQN g.property))
  have hidx : (centralizer (H : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 := by
    dsimp only [H]
    rw [conjugateSpanBy_eq_iSup_conj]
    apply mixed_small_actor_sup_index s hc u him hcol hct _ hKt
    intro g
    let A := K.map (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom
    have hAg : A ≤ stabilizer d.radical c :=
      (hKt g).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
    apply moving_small_commutator_fixed_index s hc hcol A hAg
    have hZg : Z d.radical (act d.radical (g : FreeAmalgam d.radical) c) ≤
        Q d.radical (p.walk.getVert (p.walk.length-2)) := by
      apply le_trans _ htrapped
      rw [Z_act,conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun k : N => (Z d.radical c).map
        (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) g⁻¹
    have hcard : Nat.card (⁅K,Z d.radical (act d.radical (g : FreeAmalgam d.radical) c)⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2 :=
      (card_le_of_le (commutator_mono le_rfl hZg)).trans hbound
    have hZm : (Z d.radical (act d.radical (g : FreeAmalgam d.radical) c)).map
        (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom = Z d.radical c := by
      rw [←inv_inv (g : FreeAmalgam d.radical),←Z_act,inv_inv,←act_mul,mul_inv_cancel,act_one]
    rw [←card_map_of_injective (f := (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom)
      (MulAut.conj (g : FreeAmalgam d.radical)).injective,map_commutator,hZm] at hcard
    change Nat.card (⁅A,Z d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 at hcard
    let := finite_Z d.radical c
    let : Finite (⁅A,Z d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion (le_normalizer_iff_commutator_le_right.mp
        (hAg.trans (Z_normalized d.radical c)))) (inclusion_injective _)
    rw [commutator_comm]
    exact (card_le_of_le (commutator_mono le_rfl (DistanceEight.U_le_Z d.radical c))).trans hcard
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hUB : U d.radical c ⊓ centralizer (H : Set (FreeAmalgam d.radical)) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    (inf_le_inf_right _ (DistanceEight.U_le_Z d.radical c)).trans hCB
  have hh := relIndex_le_of_le_left (L := U d.radical c) hUB index_ne_zero_of_finite
  rw [inf_relIndex_left] at hh
  exact hh.trans hidx

private theorem relative_small_backward_shift
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ∃ k ∈ stabilizer d.radical t,
      ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical k c)
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k c)) =
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  have hex : ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical),
      ¬ (Z d.radical c).map (MulAut.conj g).toMonoidHom ≤
        Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    by_contra! hall
    have htrap : conjugateSpanBy (Z d.radical c)
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
      rw [conjugateSpanBy_eq_iSup_conj]
      exact iSup_le (fun g => hall g g.property)
    exact (not_lt_of_ge (trapped_slice_bound s hc hb u him p hp htrap hat hct hgen)) hindex
  obtain ⟨g,hg,hout⟩ := hex
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical c ≤ Q d.radical t :=
    ((Z_le_VBall d.radical c 2).trans ((replacementGeometry h d).V_le_Q hb c hcol)).trans
      (Q_le_adjacent_h d.radical ht hct)
  obtain ⟨j,hj,he⟩ := Escape.Propagation.Backward.Products.holomorph_realizes t c hcol hct g hg.1
  have hZ : Z d.radical (act d.radical j⁻¹ c) =
      (Z d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [Z_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree hZt he
  have hU : U d.radical (act d.radical j⁻¹ c) =
      (U d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [U_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree
      ((DistanceEight.U_le_Z d.radical c).trans hZt) he
  have hct' : Adjacent d.radical (act d.radical j⁻¹ c) t := by
    have hfix : act d.radical j⁻¹ t = t := (stabilizer d.radical t).inv_mem hj
    simpa only [hfix] using (adjacent_act_iff d.radical j⁻¹ c t).mpr hct
  let w : (cosetGraph d.radical).Walk (act d.radical j⁻¹ c) (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct')
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hbad : ¬ Z d.radical (act d.radical j⁻¹ c) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2)) := by rwa [hZ]
  have hcolor : color d.radical (act d.radical j⁻¹ c) = false := by
    rw [action_preserves_color,hcol]
  let q := p.prepend_two (Nat.le_of_lt hb) hcolor w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨j⁻¹,(stabilizer d.radical t).inv_mem hj,q,hqt,
    fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,?_⟩
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hg.2)
  rw [hU,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hB]

/-- Every strict moving-cover slice supplies a backward critical shift in
the mixed-plane branch. The relative generating edge is constructed from the
original Sylow witness. The two actual transporters are kept separate: one
belongs to the starting stabilizer and the other to the selected edge stabilizer. -/
theorem mixed_strict_backward_path_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        act d.radical x (p.walk.getVert 1) = t ∧
        ∃ k ∈ stabilizer d.radical t,
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (act d.radical k (act d.radical x delta)) (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (act d.radical k (act d.radical x delta))) =
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical delta) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨T,hT⟩ := large_distance_mixed_original_sylow_knownSimple hb u him
  obtain ⟨t,hat,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb T hT p
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hfirst hat
  have hct : Adjacent d.radical (act d.radical x delta) t := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdelta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl
      ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x delta)) =
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,hB]
  refine ⟨t,hat,hgen,x,hx,hxt,?_⟩
  have hout : ∃ k ∈ stabilizer d.radical t,
      ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical k (act d.radical x delta))
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k (act d.radical x delta))) =
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical x delta)) := by
    by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
    · have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
        rw [hf]
        exact map_mono (plus_le_exceptional.trans
          CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
      apply SylowNormalizer.relative_large_backward_shift s hc hb u hR p hlarge hat hct hgen
      intro he
      have hh := relIndex_eq_one.mpr he
      rw [hi] at hh
      omega
    · apply relative_small_backward_shift s hc hb u hf p (by omega) hat hct hgen
      rwa [hi]
  obtain ⟨k,hk,q,hq1,hover,hqi⟩ := hout
  exact ⟨k,hk,q,hq1,hover,hqi.trans hi⟩

/-- A trapped radius forces every moving-cover slice on the original graph
into index at most two in the mixed-plane branch. The relative-normalizer
orbit of the reverse kernel is controlled by its unique transposition image. -/
theorem mixed_trapped_all_slices_le_two_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (htrapped : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    by_contra! hlarge
    obtain ⟨v,hav,hgen,c,hcv,q,hq1,hover,hel⟩ :=
      SylowNormalizer.mixed_large_backward_shift_knownSimple hb u him p hlarge
    have hq2 : q.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
    have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
      have hl : 2 ≤ q.walk.length := q.length_eq_b ▸ hb.le
      exact (hq2 ▸ q.dist_start hl).le
    exact q.critical.2 (((Z_le_localZSpan d.radical c (alpha d.radical)).trans
      (localZSpan_le_V d.radical hdist)).trans htrapped)
  obtain ⟨T,hT⟩ := large_distance_mixed_original_sylow_knownSimple hb u him
  obtain ⟨t₀,hat₀,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb T hT p
  have hbase {v w : Vertex d.radical}
      (hav : Adjacent d.radical (alpha d.radical) v) (hwv : Adjacent d.radical w v) :
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical w) ≤ 2 := by
    obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hav hat₀
    have hw : Adjacent d.radical (act d.radical x w) t₀ := by
      rw [←hxt]
      exact (adjacent_act_iff d.radical x w v).mpr hwv
    have hwdist : (cosetGraph d.radical).dist (act d.radical x w) (alpha d.radical) ≤ 2 := by
      have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hw)
      have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat₀))
      have hh := (cosetGraph_connected d.radical).dist_triangle
        (u := act d.radical x w) (v := t₀) (w := alpha d.radical)
      omega
    have horbit : conjugateSpanBy (Z d.radical (act d.radical x w))
        (normalizer (Q d.radical t₀ : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
      (conjugateSpanBy_le
        ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hwdist))
        (inf_le_right.trans (DistanceEight.V_normalized d.radical _))).trans htrapped
    have hh := trapped_slice_bound s hc hb u hf p hp horbit hat₀ hw hgen
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl
        ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hh
    exact hh
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical ha
  have hga' : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have hat' : Adjacent d.radical (alpha d.radical) (act d.radical g⁻¹ t) := by
    rw [←hga']
    exact (adjacent_act_iff d.radical g⁻¹ a t).mpr hat
  have hct' : Adjacent d.radical (act d.radical g⁻¹ c) (act d.radical g⁻¹ t) :=
    (adjacent_act_iff d.radical g⁻¹ c t).mpr hct
  have hh := hbase hat' hct'
  rw [←hga',Escape.PairingControl.FirstPairing.B_act hb g⁻¹ a ha,
    U_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hh
  exact hh

/-- Mixed-plane radii escape the actual predecessor core. In the only
nonzero-kernel alternative, residual rotation constructs a large critical
image, contradicting the global small-slice bound forced by trapping. -/
theorem mixed_radius_not_le_predecessor_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ¬ V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  intro htrapped
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hslices {v w : Vertex d.radical}
      (q : CriticalPath d.radical (replacementGeometry h d) v w) :
      (B d.radical (q.walk.getVert (q.walk.length-2))
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical w) ≤ 2 := by
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
      apply (q.vertex_color (Nat.sub_le _ _)).mpr
      have he := replacementDistance_even h d
      rw [Nat.even_iff] at he ⊢
      omega
    have hct : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
        (q.walk.getVert (q.walk.length-1)) := by
      have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
      rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
      exact (cosetGraph_adj d.radical _ _).mp hh
    have hwt : Adjacent d.radical w (q.walk.getVert (q.walk.length-1)) := by
      have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
      rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
      exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
    exact mixed_trapped_all_slices_le_two_knownSimple hb u him p htrapped hcol hct hwt
  rcases MixedResidual.mixed_backward_or_predecessor_growth_knownSimple hb u him p with hlarge | hout
  · exact (not_lt_of_ge (hslices p)) hlarge
  obtain ⟨t,hat,hgen,c,hct,hel,hout⟩ := hout
  rcases hout with ⟨q,hq1,hover⟩ | ⟨k,hk,hkt,q,hlarge,hgrowth,hq1,hover,hcomm⟩
  · have hq2 : q.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
    have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
      have hl : 2 ≤ q.walk.length := q.length_eq_b ▸ hb.le
      exact (hq2 ▸ q.dist_start hl).le
    exact q.critical.2 (((Z_le_localZSpan d.radical c (alpha d.radical)).trans
      (localZSpan_le_V d.radical hdist)).trans htrapped)
  · have hi := (critical_predecessor_slice_eq_kernel s hc hb q (hslices q)).2.1
    omega
private theorem mixed_escape_base
    (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (hcrit : CriticalPair d.radical (alpha d.radical) a'
      ((replacementGeometry h d).exists_critical _ rfl))
    (c : Vertex d.radical) (hce : (cosetGraph d.radical).dist c a' = 2)
    (hpath : (cosetGraph d.radical).dist (alpha d.radical) c + 2 =
      (cosetGraph d.radical).dist (alpha d.radical) a') :
    ¬ V d.radical (alpha d.radical) ≤ Q d.radical c := by
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist (alpha d.radical) c
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a'
  let p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a' :=
    ⟨rfl,w.append v,by rw [SimpleGraph.Walk.length_append,hw,hv,hce,hpath],hcrit⟩
  have heq : p.walk.getVert (p.walk.length-2) = c := by
    change (w.append v).getVert ((w.append v).length-2) = c
    rw [SimpleGraph.Walk.length_append,hv,hce,Nat.add_sub_cancel]
    simp only [SimpleGraph.Walk.getVert_append,lt_self_iff_false,ite_false,
      Nat.sub_self,SimpleGraph.Walk.getVert_zero]
  simpa only [heq] using mixed_radius_not_le_predecessor_knownSimple hb u him p

/-- The mixed-plane replacement satisfies the universal radius-escape premise
of MS93 2.2(v). Transport preserves the original graph and both covers. -/
theorem mixed_criticalEscape_knownSimple
    (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom) :
    Factorization.CriticalEscape d.radical (replacementGeometry h d) := by
  intro a ha a' hcrit c hce hpath
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hbase : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have ha' : color d.radical (act d.radical g⁻¹ (mVertex d.radical g)) = false := by
    rw [hbase]
    rfl
  have hcrit' := (criticalPair_act_iff d.radical g⁻¹ (mVertex d.radical g) a'
    ((replacementGeometry h d).exists_critical _ ha)
    ((replacementGeometry h d).exists_critical _ ha')).mpr hcrit
  have hcritbase : CriticalPair d.radical (alpha d.radical) (act d.radical g⁻¹ a')
      ((replacementGeometry h d).exists_critical _ rfl) := by
    simpa only [hbase] using hcrit'
  have hce' : (cosetGraph d.radical).dist (act d.radical g⁻¹ c) (act d.radical g⁻¹ a') = 2 := by
    rw [dist_act]
    exact hce
  have hpath' : (cosetGraph d.radical).dist (alpha d.radical) (act d.radical g⁻¹ c) + 2 =
      (cosetGraph d.radical).dist (alpha d.radical) (act d.radical g⁻¹ a') := by
    rw [←hbase,dist_act,dist_act]
    exact hpath
  have hn := mixed_escape_base hb u him hcritbase (act d.radical g⁻¹ c) hce' hpath'
  intro hV
  apply hn
  have hh := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hV
  rw [←V_act,←Q_act,hbase] at hh
  exact hh

/-- Source (5.8) for the literal mixed-plane replacement: every critical
path has eligible forward and reciprocal slices, and extends by two edges
with every shared vertex retained. Both full central covers are allowed. -/
theorem mixed_forward_path_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      2 ≤ (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a) ∧
      ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
        (cosetGraph d.radical).dist a' z = 2 ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
        q.walk.getVert (q.walk.length-2) = a' := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hesc := mixed_criticalEscape_knownSimple hb u him
  exact ⟨critical_forward_slice_index_two_le_of_escape s hc hb hesc p,
    critical_start_slice_index_two_le s hc hb p,
    critical_forward_extension_of_escape s hc hb hesc p⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEscape
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
