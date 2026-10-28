module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed

/-!
# The small-slice branch of the distance-four critical-image argument

Let P be the orbit span of the midpoint seed under the starting stabilizer
of an actual critical path of length four. If P is nonabelian and its
forward Baumann slice has index at most two, both critical seed images have
order two. This does not require any particular radical image, a Sylow
hypothesis, or a split moving cover.

For a putative large critical image, the full-cover radius calculation
supplies a controlled reverse subactor containing an even involution in the
literal symmetric quotient. Its commutator with the midpoint-core
intersection of P lies in the starting seed, hence in the center of P.
The small slice therefore gives fixed index at most two on P/Z(P). The
faithful symmetric-six action on that quotient contradicts the displacement
bound for even involutions. In particular, the argument uses the restricted
actor itself; it does not enlarge its commutator estimate to the full
endpoint seed.

Combining this exclusion with the full-seed forward-line calculation bounds
P' by two and fixes it under the entire starting stabilizer. The abelian
case is included, and literal conjugation gives the result at every
component vertex. The terminal application discharges the critical-index,
selected-index and derived-fixedness premises for this branch. Nonabelian
span and slice selection, endpoint control, the whole opposite residual-core
bounds, and the remaining distance-four branches still belong to this
source theorem's assembly; this is not DistanceFourInput.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.2)(i)--(iii), printed pp.913--915, and the small-slice part of
(5.12)(2), printed pp.925--926. The fixed-index calculation adapts
SelectedSpan.selected_span_endpoint_fixed_index to the actual controlled
subactor. The even-involution calculation follows SelectedFour.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
private abbrev S := Equiv.Perm (Fin 6)
private theorem linearized_cyclic_codim_eq_one
    {Y : Type*} [Group Y] [Finite Y] [IsElementaryAbelian 2 Y]
    {D : Type*} [Group D] (ρ : D→*MulAut Y) (hf : Function.Injective ρ)
    (a : D) (ha : a≠1) (hi : (ρ a).fixedSubgroup.index≤2) :
    fixedCodim (Offenders.linearize ρ) (zpowers a)=1 := by
  let σ := Offenders.linearize ρ
  change fixedCodim σ (zpowers a)=1
  let e : fixedSpace σ (zpowers a) ≃ (ρ a).fixedSubgroup := {
    toFun := fun v => ⟨v.val.toMul, (MulAut.mem_fixedSubgroup _ _).mpr
      (congrArg Additive.toMul ((mem_fixedSpace_zpowers_iff σ a v.val).mp v.property))⟩
    invFun := fun v => ⟨Additive.ofMul v.val,(mem_fixedSpace_zpowers_iff σ a _).mpr
      (congrArg Additive.ofMul ((MulAut.mem_fixedSubgroup _ _).mp v.property))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card Y≤Nat.card ((ρ a).fixedSubgroup)*2 := by
    rw [←(ρ a).fixedSubgroup.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  rw [←Nat.card_congr e] at hcard
  change Nat.card (Additive Y)≤_ at hcard
  have hV := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive Y)
  have hF := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=fixedSpace σ (zpowers a))
  rw [Nat.card_zmod] at hV hF
  rw [hV,hF] at hcard
  have hd : Module.finrank (ZMod 2) (Additive Y)≤
      Module.finrank (ZMod 2) (fixedSpace σ (zpowers a))+1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [pow_succ] using hcard
  have hne : zpowers a≠⊥ := fun he => ha (mem_bot.mp (he ▸ mem_zpowers a))
  have hp := fixedCodim_pos_of_faithful σ (Offenders.linearize_injective ρ hf) hne
  have hs := fixedCodim_add_finrank σ (zpowers a)
  omega


private theorem even_actor_not_small_fixed
    {Y : Type*} [Group Y] [Finite Y] [IsElementaryAbelian 2 Y]
    (ρ : S →* MulAut Y) (hf : Function.Injective ρ) (a : S)
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) :
    ¬ (ρ a).fixedSubgroup.index ≤ 2 := by
  intro hi
  have hne : a ≠ 1 := by intro he; rw [he,orderOf_one] at ha; omega
  have hup := linearized_cyclic_codim_eq_one ρ hf a hne hi
  let σ := Offenders.linearize ρ
  change fixedCodim σ (zpowers a) = 1 at hup
  have hinj := Offenders.linearize_injective ρ hf
  have hevenne : σ a ≠ 1 := by
    intro he
    apply hne
    exact hinj (he.trans σ.map_one.symm)
  have hlo := Representation.AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_even_involution_mem
    σ ⟨⟨a,heven⟩,hevenne⟩ a ha heven (mem_zpowers a)
  omega


variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem selected_restricted_actor_fixed_index
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2)
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (W : Subgroup (FreeAmalgam d.radical))
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2), W⁆ ≤ Z d.radical (alpha d.radical))
    (m : d.overgroup) (hm : embedM d.radical m ∈ W) :
    (selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd (s.projection m)).fixedSubgroup.index ≤ 2 := by
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  let C := Q d.radical (p.walk.getVert 2)
  let q : P →* P ⧸ center P := QuotientGroup.mk' (center P)
  have hPQ : P ≤ Q d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical hd).trans
      (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb)
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) := hPQ.trans (by intro x hx; exact hx.1)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hZaC : Z d.radical (alpha d.radical) ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical _ rfl)).trans
      (centralizer_le hPQ)
  have hfix : (C.subgroupOf P).map q ≤
      (selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd (s.projection m)).fixedSubgroup := by
    rintro _ ⟨x,hx,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [selectedSpanSymmetricAction_projection,forwardSpanCentralAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hz : ⁅embedM d.radical m,(x:FreeAmalgam d.radical)⁆ ∈ Z d.radical (alpha d.radical) := by
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator hm ⟨x.property,hx⟩
    change (y:FreeAmalgam d.radical)*(embedM d.radical m*(x:FreeAmalgam d.radical)*(embedM d.radical m)⁻¹/(x:FreeAmalgam d.radical)) =
      (embedM d.radical m*(x:FreeAmalgam d.radical)*(embedM d.radical m)⁻¹/(x:FreeAmalgam d.radical))*(y:FreeAmalgam d.radical)
    simpa only [div_eq_mul_inv,commutatorElement_def] using hZaC hz y y.property
  have hi : ((C.subgroupOf P).map q).index ≤ C.relIndex P := Nat.le_of_dvd
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    ((C.subgroupOf P).index_map_dvd (QuotientGroup.mk'_surjective (center P)))
  exact (index_antitone hfix).trans (hi.trans hindex)

include s in
/-- A nonabelian selected span with a small forward slice excludes a large
critical image, with no condition on the radical image or cover order. -/
theorem large_critical_image_false_of_small_slice
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical hd).trans ((replacementGeometry h d).V_local _ rfl hb2)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let := selected_span_central_quotient_elementary s hc hb2 (p.walk.getVert 2) hd
  let ρ := selectedSpanSymmetricAction s hc hb2 (p.walk.getVert 2) hd
  have hρ : Function.Injective ρ := selected_span_symmetric_action_injective s hb2 p hnon ρ
    (selectedSpanSymmetricAction_projection s hc hb2 (p.walk.getVert 2) hd)
  obtain ⟨W,_,hcomm,a,haW,ha,heven⟩ := critical_radius_even_actor s hc hb2 p hlarge
  obtain ⟨m,hm,rfl⟩ := haW
  have hcommP : ⁅P ⊓ Q d.radical (p.walk.getVert 2),W⁆ ≤ Z d.radical (alpha d.radical) := by
    rw [hl] at hcomm
    exact (commutator_mono (inf_le_inf_right _ (localZSpan_le_V d.radical hd)) le_rfl).trans hcomm
  have hi := (selected_span_index_of_forward_slice s hc hb2 p hslice).2
  exact even_actor_not_small_fixed ρ hρ (s.projection m) ha heven
    (selected_restricted_actor_fixed_index s hc hb2 p hd hi W hcommP m hm)

include s in
/-- The literal seed indices, rather than a quotient-image classification,
are forced to be two on a nonabelian small-slice path. -/
theorem critical_indices_two_of_small_slice
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) = 2 ∧
      (Q d.radical (alpha d.radical)).relIndex (Z d.radical a') = 2 := by
  apply small_critical_indices s hc p
  by_contra! hlarge
  exact large_critical_image_false_of_small_slice s hc hb p hnon hslice hlarge

/-- Every small-slice selected span at distance four has derived subgroup
of order at most two, fixed by the whole starting stabilizer. This includes
the abelian spans and all radical images. -/
theorem small_slice_span_derived_bound_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  by_cases hzero : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ = ⊥
  · dsimp only
    rw [hzero,card_bot]
    exact ⟨by decide,bot_le⟩
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := (critical_indices_two_of_small_slice s hc hb p hzero hslice).1
  have hd := small_selected_span_derived_knownSimple (e := e) (hz := hz) (hn := hn)
    hb2 p (by omega) hslice hzero
  exact ⟨hd.2.1.le,hd.2.2⟩

/-- The same bound at every component vertex, retaining the original walk
and transporting its slice by the same conjugation as its selected span. -/
theorem small_slice_span_derived_bound_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hslice : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let P := localZSpan d.radical (p.walk.getVert 2) a
    Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := small_slice_span_derived_bound_knownSimple
    (e := e) (hz := hz) (hn := hn) hb (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hslice' : (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act g⁻¹).walk.getVert 2)) ≤ 2 := by
    change (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)) ≤ 2
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act
      (by omega : 2 < replacementDistance h d) _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hslice
  have hd := base (p.act g⁻¹) hslice'
  change Nat.card (⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
      (act d.radical g⁻¹ a),localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
      (act d.radical g⁻¹ a)⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
    ⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) (act d.radical g⁻¹ a),
      localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) (act d.radical g⁻¹ a)⁆ ≤
        centralizer (stabilizer d.radical (act d.radical g⁻¹ a) : Set (FreeAmalgam d.radical)) at hd
  have hrestore (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hcard := hd.1
  rw [actWalk_getVert,LocalCommutator.CriticalCase.localZSpan_act,←map_commutator,
    card_map_of_injective (MulAut.conj (g⁻¹)⁻¹).injective] at hcard
  have hm := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hd.2).trans
    (map_centralizer_le_centralizer_image _ _)
  change (⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) (act d.radical g⁻¹ a),
      localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) (act d.radical g⁻¹ a)⁆ :
        Subgroup (FreeAmalgam d.radical)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer ((stabilizer d.radical (act d.radical g⁻¹ a)).map (MulAut.conj g⁻¹).toMonoidHom :
        Set (FreeAmalgam d.radical)) at hm
  rw [actWalk_getVert,map_commutator,←LocalCommutator.CriticalCase.localZSpan_act,
    ←stabilizer_act,hrestore,hrestore] at hm
  exact ⟨hcard,hm⟩

/-- Application to the literal replacement terminal argument. The small
slice now discharges critical smallness, the selected index and derived
fixedness for every radical image. Selection, the endpoint commutator and
the two whole opposite-core estimates remain source obligations. -/
theorem small_slice_terminal_false_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hcross : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
        ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := (critical_indices_two_of_small_slice s hc hb p hnon hslice).1
  have hd := small_slice_span_derived_bound_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice
  exact selected_natural_terminal_false_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hnon (by omega)
    (hd.2.trans (centralizer_le (Ltilde_le_stabilizer _)))
    (selected_span_index_of_forward_slice s hc hb2 p hslice).2 hcomm hCcard hcross

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
