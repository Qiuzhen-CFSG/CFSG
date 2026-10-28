module
public import Stellmacher.SectionNine.NineFivePreviousCommutation
public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Theory.GroupAction.ComplementaryFourSupportFixed
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineFiveConjugatorAlgebra
public import Theory.GroupAction.SubgroupQuotientSupportLift
public import Stellmacher.SectionOne.OneSevenConjugateCommonFixed

/-!
# The neighboring intersection in the distinct-support case of (9.5)

The actual lifted canonical transvection support and its penultimate-core
conjugate span the terminal module. When they are distinct, the intersection
of that module with the module at path offset b−2 has order eight. The
literal quotient action, its canonical factor, and the lifted support image
remain explicit, so this theorem applies directly to the support producer.

Earlier-module commutation places the intersection in the actor's fixed
subgroup. The penultimate-core conjugator fixes both neighboring vertices
and hence preserves their module intersection. Conjugating therefore gives
the second fixed-subgroup bound and a second contained displacement. The
canonical factor supports become complementary four-element subgroups in
the terminal quotient. Their two actors have common fixed subgroup equal
to the join of their displacements, of order four. The quotient image of
the geometric intersection is squeezed between these equal subgroups.
Its kernel is the terminal center of order two, giving the asserted eight.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.5)(b), printed
pp.52–53/PDF pp.42–43 of `refs/files/stellmacher-n-group.pdf`. This fills the
neighboring-intersection assertion in the source's final “then (b) holds”
step, using the genuine factor and path rather than an assumed cardinality.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem quotient_intersection_card
    {G : Type u} [Group G] [Finite G]
    (P U Z I : Subgroup G)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hIU : I ≤ U) (hZI : Z ≤ I) (hZcard : Nat.card Z = 2)
    (a b : P)
    (hCa : I ≤ Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G))
    (hCb : I ≤ Subgroup.centralizer (Subgroup.zpowers (b : G) : Set G))
    (hDa : ⁅U, Subgroup.zpowers (a : G)⁆ ≤ I)
    (hDb : ⁅U, Subgroup.zpowers (b : G)⁆ ≤ I)
    (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    ∀ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩) →
      (FixedPoints.subgroup (Subgroup.zpowers (action a)) (U ⧸ Z.subgroupOf U) ⊓
        FixedPoints.subgroup (Subgroup.zpowers (action b)) (U ⧸ Z.subgroupOf U) =
          commutatorAction (Subgroup.zpowers (action a)) (U ⧸ Z.subgroupOf U) ⊔
          commutatorAction (Subgroup.zpowers (action b)) (U ⧸ Z.subgroupOf U)) →
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers (action a)) (U ⧸ Z.subgroupOf U) ⊓
        FixedPoints.subgroup (Subgroup.zpowers (action b)) (U ⧸ Z.subgroupOf U) :
          Subgroup (U ⧸ Z.subgroupOf U)) = 4 →
      Nat.card I = 8 := by
  let _ := hN
  dsimp only
  intro action haction heq hcard
  let W := U ⧸ Z.subgroupOf U
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let J := (I.subgroupOf U).map q
  have hfixed (actor : P)
      (hc : I ≤ Subgroup.centralizer (Subgroup.zpowers (actor : G) : Set G)) :
      J ≤ FixedPoints.subgroup (Subgroup.zpowers (action actor)) W := by
    rintro point ⟨lift, hlift, rfl⟩
    have hcomm : (actor : G) * (lift : G) = (lift : G) * (actor : G) :=
      Subgroup.mem_centralizer_iff.mp (hc hlift) (actor : G) (Subgroup.mem_zpowers _)
    have hfix : action actor (q lift) = q lift := by
      rw [haction]
      apply congrArg q
      apply Subtype.ext
      change (actor : G) * (lift : G) * (actor : G)⁻¹ = (lift : G)
      rw [hcomm, mul_inv_cancel_right]
    intro mover
    exact smul_eq_self_of_mem_zpowers mover.property hfix
  have hdisplacement (actor : P)
      (hd : ⁅U, Subgroup.zpowers (actor : G)⁆ ≤ I) :
      commutatorAction (Subgroup.zpowers (action actor)) W ≤ J := by
    have hAP : Subgroup.zpowers (actor : G) ≤ P := Subgroup.zpowers_le.mpr actor.property
    have hnative : (Subgroup.zpowers (actor : G)).subgroupOf P =
        Subgroup.zpowers actor := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hAP, MonoidHom.map_zpowers]
      rfl
    have himage := Subgroup.quotient_conjugation_commutatorAction_eq_image
      P U Z (Subgroup.zpowers (actor : G)) hPU hAP hN action haction
    rw [hnative, MonoidHom.map_zpowers] at himage
    rw [himage]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono U hd)
  have hJ : J = FixedPoints.subgroup (Subgroup.zpowers (action a)) W ⊓
      FixedPoints.subgroup (Subgroup.zpowers (action b)) W := by
    refine le_antisymm (le_inf (hfixed a hCa) (hfixed b hCb)) ?_
    rw [heq]
    exact sup_le (hdisplacement a hDa) (hdisplacement b hDb)
  have hJcard : Nat.card J = 4 := hJ ▸ hcard
  have hrelative : Z.relIndex I = 4 := by
    have hrel := Subgroup.relIndex_ker (I.subgroupOf U) q
    rw [QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hIU] at hrel
    exact hrel.trans hJcard
  have hprod := (Z.subgroupOf I).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv, hZcard] at hprod
  change Z.relIndex I * 2 = Nat.card I at hprod
  rw [hrelative] at hprod
  exact hprod.symm

private theorem nine_five_neighbor_intersection_geometric_transfer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor conjugator : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hconjugator : (conjugator : G) ∈ twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)))
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ≤
      VAt ctx.Γ prev)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let U := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    let W := U ⧸ Z.subgroupOf U
    ∀ action : P →* MulAut W,
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                  point).mp point.property⟩) →
      (FixedPoints.subgroup (Subgroup.zpowers (action actor)) W ⊓
        FixedPoints.subgroup (Subgroup.zpowers (action (conjugator⁻¹ * actor * conjugator))) W =
          commutatorAction (Subgroup.zpowers (action actor)) W ⊔
          commutatorAction (Subgroup.zpowers (action (conjugator⁻¹ * actor * conjugator))) W) →
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers (action actor)) W ⊓
        FixedPoints.subgroup (Subgroup.zpowers (action (conjugator⁻¹ * actor * conjugator))) W :
          Subgroup W) = 4 →
      Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ prev : Subgroup G) = 8 := by
  let _ := hN
  dsimp only
  intro action haction hfixed hfixedcard
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let U := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let I := U ⊓ VAt ctx.Γ prev
  let twist := (MulAut.conj (conjugator : G)⁻¹).toMonoidHom
  let second := conjugator⁻¹ * actor * conjugator
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    stabilizer_le_normalizer_v ctx.Γ _
  obtain ⟨hCa, hInormal⟩ := nine_five_neighbor_intersection_actor_control
    ctx.toLocalContext hb prev hpath actor conjugator hactor hconjugator
  change I ≤ Subgroup.centralizer (Subgroup.zpowers (actor : G) : Set G) at hCa
  change (conjugator : G) ∈ Subgroup.normalizer (I : Set G) at hInormal
  have hImap : I.map twist = I :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (I : Set G)).inv_mem hInormal)
  have hUmap : U.map twist = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (U : Set G)).inv_mem (hPU conjugator.property))
  have htwist : twist (actor : G) = (second : G) := by
    simp [twist, second]
  have hCimage := (Subgroup.map_mono (f := twist) hCa).trans
    (Subgroup.map_centralizer_le_centralizer_image _ _)
  change I.map twist ≤ Subgroup.centralizer
    ((Subgroup.zpowers (actor : G)).map twist : Set G) at hCimage
  have hCb : I ≤ Subgroup.centralizer (Subgroup.zpowers (second : G) : Set G) := by
    rw [hImap] at hCimage
    simpa only [MonoidHom.map_zpowers, htwist] using hCimage
  have hDa : ⁅U, Subgroup.zpowers (actor : G)⁆ ≤ I :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr actor.property).trans hPU)) hcontain
  have hDb := Subgroup.map_mono (f := twist) hDa
  rw [Subgroup.map_commutator, hUmap, MonoidHom.map_zpowers, hImap, htwist] at hDb
  have hfour := (lemma_nine_three_ambient ctx hb ctx.criticalPath.a
    ⟨1, ctx.Γ.act_one _⟩).2
  have hZmiddle := (nine_five_penultimate_center_layer_of_initial_four
    ctx.toLocalContext hfour).1
  have hZI : Z ≤ I := hZmiddle.trans (le_inf
    (nine_seven_neighbor_center_le_module ctx.Γ
      (ctx.Γ.adjacent_symm (nine_five_penultimate_adjacent ctx.toLocalContext)))
    (nine_seven_neighbor_center_le_module ctx.Γ
      (nine_five_previous_adjacent_penultimate ctx.toLocalContext hb prev hpath)))
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hZcard := (nine_next_center_commutator_and_kernel ctx hb ctx.criticalPath.a'
    ⟨mover, hmover⟩).1
  exact quotient_intersection_card P U Z I hPU inf_le_left hZI hZcard actor second
    hCa hCb hDa hDb hN action haction hfixed hfixedcard

private theorem quotient_support_pair
    {G : Type u} [Group G] (P U Z support : Subgroup G)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hSU : support ≤ U) (hZS : Z ≤ support)
    [hN : (Z.subgroupOf U).Normal]
    (action : P →* MulAut (U ⧸ Z.subgroupOf U))
    (haction : ∀ mover : P, ∀ point : U,
      action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩)
    (supportBar : Subgroup (U ⧸ Z.subgroupOf U))
    (himage : (support.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) = supportBar)
    (conjugator : P)
    (hspan : U = support ⊔ support.map (MulAut.conj (conjugator : G)).toMonoidHom)
    (hne : support ≠ support.map (MulAut.conj (conjugator : G)).toMonoidHom) :
    supportBar ⊔ supportBar.map (action conjugator).toMonoidHom = ⊤ ∧
      supportBar ≠ supportBar.map (action conjugator).toMonoidHom := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let movedBar := supportBar.map (action conjugator).toMonoidHom
  let moved := support.map (MulAut.conj (conjugator : G)).toMonoidHom
  have hZU : Z ≤ U := hZS.trans hSU
  have hkernel : q.ker ≤ support.subgroupOf U := by
    rw [show q.ker = Z.subgroupOf U from QuotientGroup.ker_mk' _]
    exact Subgroup.subgroupOf_mono U hZS
  have hlift : (supportBar.comap q).map U.subtype = support := by
    rw [← himage, Subgroup.comap_map_eq_self hkernel,
      Subgroup.map_subgroupOf_eq_of_le hSU]
  have hmoved : moved = (movedBar.comap q).map U.subtype := by
    dsimp only [moved]
    rw [← hlift]
    exact Subgroup.lift_support_conjugate P U Z hPU action haction supportBar conjugator
  have hmovedU : moved ≤ U := hmoved ▸ Subgroup.map_subtype_le _
  have himageMoved : (moved.subgroupOf U).map q = movedBar := by
    rw [hmoved]
    exact (Subgroup.lift_support_basic U Z hZU movedBar).2.2.2
  change U = support ⊔ moved at hspan
  constructor
  · change supportBar ⊔ movedBar = ⊤
    rw [← himageMoved, ← himage, ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup hSU hmovedU, ← hspan, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  · intro heq
    apply hne
    rw [show support.map (MulAut.conj (conjugator : G)).toMonoidHom = moved from rfl,
      hmoved, ← hlift, heq]

/-- Distinct canonical supports force the neighboring intersection to have order eight. -/
public theorem nine_five_neighbor_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ≤
      VAt ctx.Γ prev)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let U := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    let W := U ⧸ Z.subgroupOf U
    ∀ hW : IsElementaryAbelian 2 W,
    let _ := hW
    ∀ action : P →* MulAut W,
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                  point).mp point.property⟩) →
      SectionOne.Hypotheses action.range W →
    ∀ factor : Subgroup action.range,
      SectionOne.IsOneSevenFactor (V := W) factor →
      action.rangeRestrict actor ∈ factor →
      Nat.card (commutatorAction (Subgroup.zpowers (action actor)) W) = 2 →
    ∀ support : Subgroup G, support ≤ U → Z ≤ support →
      (support.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
        commutatorAction factor W →
    ∀ conjugator : G, conjugator ∈ twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) →
      U = support ⊔ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
      support ≠ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
      Nat.card (U ⊓ VAt ctx.Γ prev : Subgroup G) = 2 ^ 3 := by
  let _ := hN
  dsimp only
  intro hW
  let _ := hW
  intro action haction hyp factor hfactor hfactorActor hrank support hSU hZS himage
    conjugator hconjugator hspan hne
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let U := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let W := U ⧸ Z.subgroupOf U
  let mover : P := ⟨conjugator,
    nine_five_penultimate_core_le_terminal ctx.toLocalContext hconjugator⟩
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    stabilizer_le_normalizer_v ctx.Γ _
  obtain ⟨hbarspan, hbarne⟩ := quotient_support_pair P U Z support hPU hSU hZS
    action haction (commutatorAction factor W) himage mover⁻¹ hspan hne
  have hpair := SectionOne.oneSevenFactor_conjugate_common_fixed action.range hyp
    factor hfactor (action.rangeRestrict actor) (action.rangeRestrict mover⁻¹)
    hfactorActor hrank hbarne hbarspan
  have hsecond : ((action.rangeRestrict mover⁻¹ * action.rangeRestrict actor *
      (action.rangeRestrict mover⁻¹)⁻¹ : action.range) : MulAut W) =
      action (mover⁻¹ * actor * mover) := by
    simp
  change FixedPoints.subgroup (Subgroup.zpowers (action actor)) W ⊓
      FixedPoints.subgroup (Subgroup.zpowers
        ((action.rangeRestrict mover⁻¹ * action.rangeRestrict actor *
          (action.rangeRestrict mover⁻¹)⁻¹ : action.range) : MulAut W)) W = _ ∧ _ at hpair
  rw [hsecond] at hpair
  exact nine_five_neighbor_intersection_geometric_transfer ctx hb prev hpath actor mover
    hactor hconjugator hcontain hN action haction hpair.1 hpair.2.1

end Stellmacher.SectionNine
