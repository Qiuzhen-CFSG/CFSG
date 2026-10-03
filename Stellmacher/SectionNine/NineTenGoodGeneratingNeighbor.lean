module
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupAction.ComplementaryFourPlaneSylowSelector
public import Stellmacher.SectionNine.NineFiveCanonicalPair
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove
public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Stellmacher.SectionNine.NineTenTwoStepClassification
public import Theory.GroupAction.SubgroupQuotientSupportLift
public import Stellmacher.SectionNine.NineTenPrescribedFirstTransvection






/-!
# A generating neighbor with the triple-intersection property in (9.10)

At literal critical length five, retain the terminal module of order
thirty-two, its SL₂(2) wreath C₂ core quotient, and its order-eight backward
intersection. For the original terminal neighbor and its supplied actor,
assume the actual first-module coatom has index two and the actor escapes
the first core. There is a neighbor lambda of the first vertex whose edge
stabilizer and the original neighbor center generate the first stabilizer.
Every other neighbor rho of lambda then satisfies
V_rho ∩ V_first ∩ V_third = Z_first.

The same two-arc transport gives the first/third order-eight intersection and
its full second-stabilizer normalization. Its image in the literal first
quotient V/Z is a plane of order four invariant under a Sylow subgroup in
the first/second edge image. The supplied actor induces a transvection;
canonical Section One supports identify the faithful action with the natural
wreath action. The simultaneous plane/Sylow selector gives one conjugator
whose quotient planes are disjoint and whose edge conjugate generates with
the retained actor. Lift through the unchanged center and two-core kernels.
Cubic two-arc transitivity and full intersection normalization then give the
triple-intersection equality for every permitted rho.

Source: Stellmacher (9.10), printed p.58, statement (**), with Lambda as defined
on printed p.57 of `refs/files/stellmacher-n-group.pdf`. This proves the literal
generating-family condition, and uses no new extraction or replacement path.
The neighborhood commutator bound in (9) is a separate subsequent result.
-/

namespace Stellmacher.SectionNine
open SectionOne
universe u

private theorem canonical_four_support_frame
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (hK : Nat.card K = 72) (hV : Nat.card V = 16)
    (D : Subgroup K) (hD : IsOneSevenFactor (V:=V) D) (S : Sylow 2 K) :
    ∃ first second : Subgroup V,
      IsCompl first second ∧ Nat.card first = 4 ∧ Nat.card second = 4 ∧
      ∀ k : K,
        (first.map (MulDistribMulAction.toMulAut K V k).toMonoidHom = first ∧
          second.map (MulDistribMulAction.toMulAut K V k).toMonoidHom = second) ∨
        (first.map (MulDistribMulAction.toMulAut K V k).toMonoidHom = second ∧
          second.map (MulDistribMulAction.toMulAut K V k).toMonoidHom = first) := by
  have hS : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity,hK]
    decide +kernel
  obtain ⟨c,hmove,hspan⟩ := oneSevenFactor_exists_complementary_two_group_conjugate
    hyp D (S : Subgroup K) hD S.isPGroup' hV (by rw [hS]; decide)
  let E := D.conjBy (c:K)
  let first := commutatorAction D V
  let second := commutatorAction E V
  have hE : IsOneSevenFactor (V:=V) E := hD.conjBy D c
  have hmap : first.map (MulDistribMulAction.toMulAut K V (c:K)).toMonoidHom = second :=
    RankOneThreeGroupAssembly.commutatorAction_conjBy D c
  have hDE : D ≠ E := by
    intro heq
    apply hmove
    rw [hmap,show second = first from congrArg (fun X : Subgroup K => commutatorAction X V) heq.symm]
  have hspan' : first ⊔ second = ⊤ := by rwa [hmap] at hspan
  have hpair := nine_five_canonical_pair_of_support_span hyp D E hD hE hDE hspan'
  have hcompl : IsCompl first second :=
    ⟨oneSevenFactor_support_disjoint_of_ne hyp D E hD hE hDE, codisjoint_iff.mpr hspan'⟩
  refine ⟨first,second,hcompl,hD.2.2.1,hE.2.2.1,?_⟩
  intro k
  dsimp only [first,second]
  rw [RankOneThreeGroupAssembly.commutatorAction_conjBy,
    RankOneThreeGroupAssembly.commutatorAction_conjBy]
  rcases hpair.2.2.2.1 k with ⟨hfirst,hsecond⟩ | ⟨hfirst,hsecond⟩
  · exact Or.inl ⟨congrArg (fun X : Subgroup K => commutatorAction X V) hfirst,
      congrArg (fun X : Subgroup K => commutatorAction X V) hsecond⟩
  · exact Or.inr ⟨congrArg (fun X : Subgroup K => commutatorAction X V) hfirst,
      congrArg (fun X : Subgroup K => commutatorAction X V) hsecond⟩

end Stellmacher.SectionNine


namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem first_quotient_edge_sylow
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (second : ctx.Γ.Vertex)
    (hsecond : second ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (I : Subgroup G)
    (hInormal : GAt ctx.Γ second ≤ Subgroup.normalizer (I : Set G))
    [hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal]
    (action : GAt ctx.Γ ctx.criticalPath.firstStep →* MulAut
      (VAt ctx.Γ ctx.criticalPath.firstStep ⧸
        (ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
          (VAt ctx.Γ ctx.criticalPath.firstStep)))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.firstStep,
      ∀ point : VAt ctx.Γ ctx.criticalPath.firstStep,
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
          (VAt ctx.Γ ctx.criticalPath.firstStep)) point) =
        QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
            (VAt ctx.Γ ctx.criticalPath.firstStep))
          ⟨(mover:G) * (point:G) * (mover:G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep mover.property)
              point).mp point.property⟩) :
    ∃ sylow : Sylow 2 action.range,
      (sylow : Subgroup action.range) ≤
        ((GAt ctx.Γ second).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep)).map
          action.rangeRestrict ∧
      ∀ actor : sylow, ∀ point,
        point ∈ ((I.subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep)).map
          (QuotientGroup.mk'
            ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
              (VAt ctx.Γ ctx.criticalPath.firstStep)))) →
        actor • point ∈ ((I.subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep)).map
          (QuotientGroup.mk'
            ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
              (VAt ctx.Γ ctx.criticalPath.firstStep)))) := by
  let Γ := ctx.Γ
  let first := ctx.criticalPath.firstStep
  let P := GAt Γ first
  let U := VAt Γ first
  let Z := ZAt Γ first
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let edge := GAt Γ second ⊓ P
  let edgeSylow : Sylow 2 edge := default
  have hfirst : first ∈ Neighborhood Γ second :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hsecond))
  obtain ⟨_, native, hnative⟩ :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core second first hfirst edgeSylow).2.1
  have hnativeMiddle : (native : Subgroup P) ≤ (GAt Γ second).subgroupOf P := by
    intro actor hactor
    have hmem : (actor:G) ∈ sylowTwoAmbient edge edgeSylow :=
      hnative ▸ Subgroup.mem_map_of_mem P.subtype hactor
    exact ((Subgroup.map_subtype_le (edgeSylow : Subgroup edge)) hmem).1
  let sylow := native.mapSurjective action.rangeRestrict_surjective
  have hsylow : (sylow : Subgroup action.range) =
      (native : Subgroup P).map action.rangeRestrict :=
    Sylow.coe_mapSurjective action.rangeRestrict_surjective native
  refine ⟨sylow, ?_, ?_⟩
  · rw [hsylow]
    exact Subgroup.map_mono hnativeMiddle
  · intro actor point hpoint
    have hactorImage : (actor:action.range) ∈ (native : Subgroup P).map action.rangeRestrict :=
      hsylow ▸ actor.property
    obtain ⟨mover, hmover, heq⟩ := hactorImage
    obtain ⟨vector, hvector, rfl⟩ := hpoint
    have hmoverMiddle : (mover:G) ∈ GAt Γ second := hnativeMiddle hmover
    change (actor:action.range).val (q vector) ∈ (I.subgroupOf U).map q
    rw [← heq]
    change action mover (q vector) ∈ (I.subgroupOf U).map q
    rw [hformula]
    exact Subgroup.mem_map_of_mem q
      ((Subgroup.mem_normalizer_iff.mp (hInormal hmoverMiddle) (vector:G)).mp hvector)

end Stellmacher.SectionNine


namespace Stellmacher.SectionNine

private theorem quotient_disjoint_intersection_lift
    {G : Type*} [Group G] (P U Z I : Subgroup G)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hIU : I ≤ U) (hZI : Z ≤ I)
    [hN : (Z.subgroupOf U).Normal]
    (action : P →* MulAut (U ⧸ Z.subgroupOf U))
    (hformula : ∀ mover : P, ∀ point : U,
      action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(mover:G) * (point:G) * (mover:G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩)
    (mover : P)
    (hdisjoint : Disjoint
      ((I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)))
      (((I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))).map
        (action mover).toMonoidHom)) :
    I ⊓ I.conjBy (mover:G) = Z := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let J := (I.subgroupOf U).map q
  have hker : q.ker ≤ I.subgroupOf U := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.subgroupOf_mono U hZI
  have hlift : (J.comap q).map U.subtype = I := by
    dsimp only [J]
    rw [Subgroup.comap_map_eq_self hker, Subgroup.map_subgroupOf_eq_of_le hIU]
  have hmoved : I.conjBy (mover:G) =
      ((J.map (action mover).toMonoidHom).comap q).map U.subtype := by
    change I.map (MulAut.conj (mover:G)).toMonoidHom = _
    rw [← hlift]
    exact Subgroup.lift_support_conjugate P U Z hPU action hformula J mover
  rw [hmoved, ← hlift, ← Subgroup.map_inf _ _ _ U.subtype_injective,
    ← Subgroup.comap_inf, hdisjoint.eq_bot]
  change q.ker.map U.subtype = Z
  rw [QuotientGroup.ker_mk', Subgroup.map_subgroupOf_eq_of_le (hZI.trans hIU)]

private theorem map_conj_subgroup
    {G K : Type*} [Group G] [Group K]
    (f : G →* K) (A : Subgroup G) (g : G) :
    (A.conjBy g).map f = (A.map f).conjBy (f g) := by
  rw [Subgroup.conjBy, Subgroup.conjBy, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

private theorem quotient_conjugate_edge_generates
    {G K : Type*} [Group G] [Group K]
    (P : Subgroup G) (edge : Subgroup P) (actor mover : P)
    (f : P →* K)
    (hker : f.ker ≤ edge)
    (hgenerate : (edge.map f).conjBy (f mover) ⊔ Subgroup.zpowers (f actor) = ⊤) :
    (edge.map P.subtype).conjBy (mover:G) ⊔ Subgroup.zpowers (actor:G) = P := by
  let joined := edge.conjBy mover ⊔ Subgroup.zpowers actor
  have hkerJoined : f.ker ≤ joined := by
    intro x hx
    apply Subgroup.mem_sup_left
    refine ⟨mover⁻¹ * x * mover, hker ?_, ?_⟩
    · simpa only [inv_inv] using (inferInstance : f.ker.Normal).conj_mem x hx mover⁻¹
    · simp [MulAut.conj_apply, mul_assoc]
  have hmap : joined.map f = ⊤ := by
    dsimp only [joined]
    rw [Subgroup.map_sup, map_conj_subgroup, MonoidHom.map_zpowers]
    exact hgenerate
  have hjoined : joined = ⊤ := by
    rw [← Subgroup.comap_map_eq_self hkerJoined, hmap, Subgroup.comap_top]
  have hbig := congrArg (Subgroup.map P.subtype) hjoined
  dsimp only [joined] at hbig
  rw [Subgroup.map_sup, map_conj_subgroup, MonoidHom.map_zpowers,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hbig
  exact hbig

end Stellmacher.SectionNine


namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem pair_intersection_eq_of_middle_normalized
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    {left middle right other : ctx.Γ.Vertex}
    (hmiddle : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle)
    (hleft : ctx.Γ.adjacent middle left)
    (hright : ctx.Γ.adjacent middle right)
    (hne : left ≠ right)
    (hother : ctx.Γ.adjacent middle other)
    (hneOther : left ≠ other)
    (hnormal : GAt ctx.Γ middle ≤ Subgroup.normalizer
      ((VAt ctx.Γ left ⊓ VAt ctx.Γ right : Subgroup G) : Set G)) :
    VAt ctx.Γ left ⊓ VAt ctx.Γ right = VAt ctx.Γ left ⊓ VAt ctx.Γ other := by
  let Γ := ctx.Γ
  obtain ⟨actor, hfixLeft, hfixMiddle, hmove⟩ := nine_seven_two_arc_transport ctx.sectionSeven
    Γ hleft hright hne hleft hother hneOther ⟨1, Γ.act_one middle⟩
      (lemma_nine_three_ambient ctx hb middle hmiddle).1
  have hactor : actor ∈ GAt Γ middle :=
    (Set.ext_iff.mp (Γ.stabilizer_def middle) actor).mpr hfixMiddle
  have hmap : (VAt Γ left ⊓ VAt Γ right : Subgroup G).map
      (MulAut.conj actor⁻¹).toMonoidHom = VAt Γ left ⊓ VAt Γ right :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormal ((GAt Γ middle).inv_mem hactor))
  rw [Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective, ← v_act, ← v_act,
    hfixLeft, hmove] at hmap
  exact hmap.symm

private theorem good_generating_neighbor_of_conjugate_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    {second third : ctx.Γ.Vertex}
    (hsecond : IsConjugateVertex ctx.Γ ctx.criticalPath.a second)
    (hfirstAdj : ctx.Γ.adjacent second ctx.criticalPath.firstStep)
    (hthirdAdj : ctx.Γ.adjacent second third)
    (hne : ctx.criticalPath.firstStep ≠ third)
    (hnormal : GAt ctx.Γ second ≤ Subgroup.normalizer
      ((VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third : Subgroup G) : Set G))
    (actors : Subgroup G) (mover : G)
    (hmover : mover ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hintersection :
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) ⊓
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third).conjBy mover =
          ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ second ⊓ GAt ctx.Γ ctx.criticalPath.firstStep).conjBy mover ⊔
      actors = GAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ neighbor, neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep ∧
      (GAt ctx.Γ neighbor ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) ⊔ actors =
        GAt ctx.Γ ctx.criticalPath.firstStep ∧
      ∀ other, other ∈ Neighborhood ctx.Γ neighbor → other ≠ ctx.criticalPath.firstStep →
        VAt ctx.Γ other ⊓ VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third =
          ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let first := ctx.criticalPath.firstStep
  let I := VAt Γ first ⊓ VAt Γ third
  let neighbor := Γ.act mover⁻¹ second
  let reference := Γ.act mover⁻¹ third
  let equiv := MulAut.conj mover
  have hfix : Γ.act mover first = first :=
    (Set.ext_iff.mp (Γ.stabilizer_def first) mover).mp hmover
  have hfixInv : Γ.act mover⁻¹ first = first :=
    (Set.ext_iff.mp (Γ.stabilizer_def first) mover⁻¹).mp
      ((GAt Γ first).inv_mem hmover)
  have hleft : Γ.adjacent neighbor first := by
    have h := adjacent_act Γ mover⁻¹ hfirstAdj
    rwa [hfixInv] at h
  have hright : Γ.adjacent neighbor reference := adjacent_act Γ mover⁻¹ hthirdAdj
  have hdistinct : first ≠ reference := by
    intro heq
    have h := congrArg (Γ.act mover) heq
    change Γ.act mover first = Γ.act mover (Γ.act mover⁻¹ third) at h
    rw [hfix, ← Γ.act_mul, inv_mul_cancel, Γ.act_one] at h
    exact hne h
  have hG : (GAt Γ second).map equiv.toMonoidHom = GAt Γ neighbor := by
    change conjugateBy (stabilizer Γ second) mover = stabilizer Γ (Γ.act mover⁻¹ second)
    simpa only [inv_inv] using (stabilizer_act Γ mover⁻¹ second).symm
  have hP : (GAt Γ first).map equiv.toMonoidHom = GAt Γ first :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((GAt Γ first).le_normalizer hmover)
  have hV : (VAt Γ first).map equiv.toMonoidHom = VAt Γ first :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (stabilizer_le_normalizer_v Γ first hmover)
  have hT : (VAt Γ third).map equiv.toMonoidHom = VAt Γ reference := by
    simpa only [inv_inv] using (v_act Γ mover⁻¹ third).symm
  have hI : I.conjBy mover = VAt Γ first ⊓ VAt Γ reference := by
    change I.map equiv.toMonoidHom = _
    dsimp only [I]
    rw [Subgroup.map_inf _ _ _ equiv.injective, hV, hT]
  have hneighborNormal : GAt Γ neighbor ≤ Subgroup.normalizer
      ((VAt Γ first ⊓ VAt Γ reference : Subgroup G) : Set G) := by
    rw [← hG, ← hI]
    exact (Subgroup.map_mono hnormal).trans (Subgroup.le_normalizer_map equiv.toMonoidHom)
  have hneighborOrbit : IsConjugateVertex Γ ctx.criticalPath.a neighbor := by
    obtain ⟨start, hstart⟩ := hsecond
    refine ⟨start * mover⁻¹, ?_⟩
    rw [Γ.act_mul, hstart]
  refine ⟨neighbor, (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft), ?_, ?_⟩
  · have hmap : (GAt Γ second ⊓ GAt Γ first).conjBy mover = GAt Γ neighbor ⊓ GAt Γ first := by
      change (GAt Γ second ⊓ GAt Γ first).map equiv.toMonoidHom = _
      rw [Subgroup.map_inf _ _ _ equiv.injective, hG, hP]
    rwa [hmap] at hgenerate
  · intro other hother hotherNe
    have heq := pair_intersection_eq_of_middle_normalized ctx hb hneighborOrbit
      hleft hright hdistinct ((mem_neighborhood_iff_adjacent Γ).mp hother)
      hotherNe.symm hneighborNormal
    have hnew : VAt Γ first ⊓ VAt Γ other = I.conjBy mover := heq.symm.trans hI.symm
    calc
      VAt Γ other ⊓ VAt Γ first ⊓ VAt Γ third =
          (VAt Γ first ⊓ VAt Γ other) ⊓ I := by
        dsimp only [I]
        ext x
        simp only [Subgroup.mem_inf]
        tauto
      _ = I.conjBy mover ⊓ I := by rw [hnew]
      _ = ZAt Γ first := by rw [inf_comm]; exact hintersection

end Stellmacher.SectionNine

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

set_option maxHeartbeats 1600000 in
public theorem nine_ten_exists_good_generating_neighbor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a')
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hcoatom : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ neighbor) 2)
    (actor : G) (hactor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorNot : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep) :
    let third := ctx.criticalPath.path ⟨3, by omega⟩
    ∃ lambda, lambda ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep ∧
      (GAt ctx.Γ lambda ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) ⊔ ZAt ctx.Γ neighbor =
        GAt ctx.Γ ctx.criticalPath.firstStep ∧
      ∀ rho, rho ∈ Neighborhood ctx.Γ lambda → rho ≠ ctx.criticalPath.firstStep →
        VAt ctx.Γ rho ⊓ VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third =
          ZAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length = 5 := hb
  have hshort : 1 < cp.length := by omega
  let second := cp.path ⟨2,by omega⟩
  let third := cp.path ⟨3,by omega⟩
  let P := GAt Γ cp.firstStep
  let U := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let I := U ⊓ VAt Γ third
  have hleft : Γ.adjacent second cp.firstStep := by
    have hedge := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) second at hedge
    rw [cp.path_first] at hedge
    exact Γ.adjacent_symm hedge
  have hright : Γ.adjacent second third := cp.path_adj ⟨2,by omega⟩
  have hdistinct : cp.firstStep ≠ third := by
    have hh := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
    rwa [cp.path_first] at hh
  obtain ⟨alignment,halign⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft))
  have hsecond : IsConjugateVertex Γ cp.a second := ⟨alignment,halign⟩
  obtain ⟨hUcard,hUmodel,hIcard,hZsecondI,_hIcore,hInormal⟩ :=
    nine_ten_two_step_wreath_classification ctx (by omega) hcard hmodel hinter
      hsecond hleft hright hdistinct
  change Nat.card U=2^5 at hUcard
  change Nat.card I=2^3 at hIcard
  have hZI : Z ≤ I :=
    ((nine_seven_center_join ctx second hsecond).2 cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr hleft)).2.trans hZsecondI
  have hZU : Z ≤ U := hZI.trans inf_le_left
  have hZcard : Nat.card Z = 2 :=
    (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext
      (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
      cp.firstStep ⟨1,Γ.act_one _⟩).1
  have hneighborP : ZAt Γ neighbor ≤ P :=
    (nine_seven_neighbor_center_le_module Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)).trans
      (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  let a : P := ⟨actor,hneighborP hactor⟩
  have hindex := (nine_ten_prescribed_actor_first_transvection ctx hshort hterminalNot
    neighbor hneighbor hcoatom actor hactor hactorNot).2
  obtain ⟨hN,hW,action,hformula,hkernel,hinvolution,_haCard,hrank,hyp,hfactor⟩ :=
    nine_next_transvection_factor ctx hshort cp.firstStep ⟨1,Γ.act_one _⟩ a hindex
  let _ := hN
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  let q : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  let J := (I.subgroupOf U).map q
  let f := action.rangeRestrict
  let edge := (GAt Γ second).subgroupOf P
  let factor := ⁅SectionOne.oddCore action.range,Subgroup.zpowers (f a)⁆ ⊔ Subgroup.zpowers (f a)
  have hQ : (QAt Γ cp.firstStep).subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  obtain ⟨projection,hprojection,hmodelKernel⟩ := hUmodel
  have hsame : f.ker = projection.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
    exact hQ.symm.trans hmodelKernel.symm
  let equiv : action.range ≃* SL2TwoWreathC2 :=
    (QuotientGroup.quotientKerEquivOfSurjective f action.rangeRestrict_surjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hsame).trans
        (QuotientGroup.quotientKerEquivOfSurjective projection hprojection))
  have hKcard : Nat.card action.range = 72 := by
    rw [Nat.card_congr equiv.toEquiv,RegularWreathProduct.card]
    have hsl : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
    rw [hsl]
    norm_num [Nat.card_eq_fintype_card]
  have hWcard : Nat.card W=16 := by
    have hcount := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hZcard,hUcard] at hcount
    change Nat.card W*2=2^5 at hcount
    omega
  have hJcard : Nat.card J=4 := by
    have hcount := (Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hIcard] at hcount
    change Z.relIndex I*2=2^3 at hcount
    have hrel := Subgroup.relIndex_ker (I.subgroupOf U) q
    rw [QuotientGroup.ker_mk',Subgroup.relIndex_subgroupOf (show I≤U from inf_le_left)] at hrel
    change Z.relIndex I=Nat.card J at hrel
    omega
  obtain ⟨sylow,hsylow,hJinvariant⟩ := first_quotient_edge_sylow (hN := hN) ctx.toLocalContext second
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft)) I hInormal action hformula
  obtain ⟨firstSupport,secondSupport,hcompl,hfirstCard,hsecondCard,hperm⟩ :=
    canonical_four_support_frame hyp hKcard hWcard factor hfactor sylow
  have haInvolution : (f a)^2 = 1 := Subtype.ext hinvolution.2
  have harank : Nat.card (commutatorAction (Subgroup.zpowers (f a)) W) = 2 := by
    rw [← commutatorAction_map_actor_subtype action.range (Subgroup.zpowers (f a)),
      MonoidHom.map_zpowers]
    exact hrank
  obtain ⟨selected,hdisjoint,hgenerate⟩ := ComplementaryFourWreathAction.exists_complementary_plane_generating_sylow
    firstSupport secondSupport hcompl hfirstCard hsecondCard hyp.action_faithful hKcard
      hperm sylow (f a) haInvolution harank J hJcard hJinvariant
  obtain ⟨mover,hmover⟩ := action.rangeRestrict_surjective selected
  have hintersection : I ⊓ I.conjBy (mover:G) = Z := by
    apply quotient_disjoint_intersection_lift P U Z I
      (stabilizer_le_normalizer_v Γ cp.firstStep) inf_le_left hZI action hformula mover
    change Disjoint J (J.map (action mover).toMonoidHom)
    rw [← hmover] at hdisjoint
    exact hdisjoint
  have hbigGenerate : (edge.map f).conjBy (f mover) ⊔ Subgroup.zpowers (f a) = ⊤ := by
    apply top_unique
    rw [← hgenerate,← hmover]
    exact sup_le_sup (Subgroup.map_mono hsylow) le_rfl
  have hkerEdge : f.ker ≤ edge := by
    rw [MonoidHom.ker_rangeRestrict,hkernel,← hQ]
    exact Subgroup.subgroupOf_mono P
      (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep second
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft)) default).2.2)
  have hedgeMap : edge.map P.subtype = GAt Γ second ⊓ P := Subgroup.subgroupOf_map_subtype _ _
  have hfullGenerate : (GAt Γ second ⊓ P).conjBy (mover:G) ⊔ Subgroup.zpowers actor = P := by
    rw [← hedgeMap]
    exact quotient_conjugate_edge_generates P edge a mover f hkerEdge hbigGenerate
  have hactorsGenerate : (GAt Γ second ⊓ P).conjBy (mover:G) ⊔ ZAt Γ neighbor = P := by
    apply le_antisymm
    · refine sup_le ?_ hneighborP
      exact (le_sup_left : (GAt Γ second ⊓ P).conjBy (mover:G) ≤
        (GAt Γ second ⊓ P).conjBy (mover:G) ⊔ Subgroup.zpowers actor).trans
          (le_of_eq hfullGenerate)
    · calc
        P = (GAt Γ second ⊓ P).conjBy (mover:G) ⊔ Subgroup.zpowers actor := hfullGenerate.symm
        _ ≤ (GAt Γ second ⊓ P).conjBy (mover:G) ⊔ ZAt Γ neighbor :=
          sup_le_sup le_rfl (Subgroup.zpowers_le.mpr hactor)
  exact good_generating_neighbor_of_conjugate_intersection ctx hshort hsecond hleft hright
    hdistinct hInormal (ZAt Γ neighbor) mover mover.property hintersection hactorsGenerate

end Stellmacher.SectionNine
