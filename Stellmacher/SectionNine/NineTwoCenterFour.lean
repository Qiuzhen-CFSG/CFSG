module

public import Stellmacher.SectionNine.NineTwoCenterFour.LocalAction
public import Stellmacher.SectionNine.NineTwoLocalIndex
public import Stellmacher.SectionOne.TransvectionFixedSylowFactor
public import Stellmacher.SectionOne.SL2FamilySylowCard
public import Stellmacher.SectionThree.NormalClosureResidualJoin
public import Stellmacher.SectionEight.LocalQuotientOddCoreSupplement

/-!
# The whole initial center has order four in Stellmacher (9.2)

For the normalized ambient Section Nine configuration, the intersection of
the neighboring cores has full fixed index two on the initial center. The
explicit commutator-center premise and (7.5) make its commutator Sylow-fixed.
The proved factor and support decomposition of the original (1.7), through
`oneSeven_factor_of_fixed_index_two`, selects a four-element support whose
factor is normalized by the Sylow. The local odd-core supplement makes this
factor normal in the entire faithful center-action quotient.

The support is the whole center, not merely one summand. The factor's Sylow
intersection has order two, is Sylow-normal, and cannot lift into the local
two-core by (7.4). The normal-closure consequence of (3.4) therefore puts
the initial residual inside the factor. The derived C3 splits the center
into its support and a complementary fixed space, which the full factor
fixes. The residual-centralizer equality in (7.5) kills that complement.
The resulting entire center consequently has order four.

The exact witness action is retained in every construction. Hypothesis Two
stays on H; no such hypothesis is asserted on the graph group G. The
commutator-center premise is supplied explicitly, without (6.4). The
generation premise is retained in the public normalized interface, although
its role has already been absorbed into that explicit containment premise.
The previous public local-action inputs are re-exported from `LocalAction`.

Source: Stellmacher (9.2), printed p.48 / PDF p.38 of
`refs/files/stellmacher-n-group.pdf`, using the proved original (1.7)
factor infrastructure, (3.3)--(3.4), and (7.3)--(7.5).
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem factor_normal_of_odd_core_sup
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [MulDistribMulAction K V]
    (sylowImage D : Subgroup K)
    (hD : SectionOne.IsOneSevenFactor (V := V) D)
    (hnormalizer : sylowImage ≤ Subgroup.normalizer (D : Set K))
    (hgenerate : SectionOne.oddCore K ⊔ sylowImage = ⊤) : D.Normal := by
  have hodd : SectionOne.oddCore K ≤ Subgroup.normalizer (D : Set K) :=
    le_sup_left.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp hD.2.2.2)
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgenerate]
  exact sup_le hodd hnormalizer

private theorem nine_two_center_card_four_of_residual_le_factor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ∀ D : Subgroup w.X,
      SectionOne.IsOneSevenFactor (V := ZAt ctx.Γ ctx.criticalPath.a) D →
      (((EAt ctx.Γ ctx.criticalPath.a).subgroupOf
        (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) ≤ D →
      Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  dsimp only
  intro D hD hresidual
  let V := ZAt ctx.Γ ctx.criticalPath.a
  have hfirst : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  let := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hfirst
  let derived := (commutator D).map D.subtype
  have hfixed : FixedPoints.subgroup derived V = ⊥ := by
    apply le_bot_iff.mp
    rw [← nine_two_residual_fixed_eq_bot ctx w]
    intro vector hvector actor
    exact SectionOne.oneSevenFactor_fixes_derived_fixedPoints D hD actor
      (hresidual actor.property) vector hvector
  have hcoprime : Nat.Coprime (Nat.card derived) (Nat.card V) := by
    obtain ⟨exponent, hcard⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [show Nat.card derived = 3 from hD.2.1.2.1, hcard]
    exact (show Nat.Coprime 3 2 by decide).pow_right exponent
  have hsplit :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := derived)
      (Group.isSolvable_of_comm fun left right =>
        (IsMulCommutative.is_comm (M := V)).comm left right) hcoprime
      (inferInstance : IsMulCommutative V)
  have htop : commutatorAction D V = ⊤ := by
    rw [SectionOne.oneSevenFactor_full_commutator_eq_derived D hD]
    simpa only [hfixed, bot_sup_eq] using hsplit.sup_eq_top
  have hcard : Nat.card (commutatorAction D V) = 4 := hD.2.2.1
  rw [htop, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv] at hcard
  exact hcard

private theorem nine_two_center_card_four_of_normal_factor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ∀ D : Subgroup w.X,
      SectionOne.IsOneSevenFactor (V := ZAt ctx.Γ ctx.criticalPath.a) D →
      D.Normal → Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  dsimp only
  intro D hD hnormal
  let := hnormal
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let sylowImage := (T.subgroupOf P).map w.projection
  let coordinate := sylowImage ⊓ D
  have hTP : T ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hlocal := (SevenSix.edge_local_data ctx.sectionSeven Γ cp).1
  obtain ⟨_, sylow, hsylow⟩ := hlocal.1.1.2.1
  have hnative : (sylow : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hsylow
  let quotientSylow := sylow.mapSurjective w.surjective
  have himage : (quotientSylow : Subgroup w.X) = sylowImage := by
    change (sylow : Subgroup P).map w.projection = _
    rw [hnative]
  have hcoordinate : Nat.card coordinate = 2 := by
    rw [show coordinate = (quotientSylow : Subgroup w.X) ⊓ D from
      congrArg (fun subgroup => subgroup ⊓ D) himage.symm]
    exact SectionOne.natCard_inf_sylow_normal_card_six quotientSylow D
      (SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hD.1)
  have hcoordinateNormal : (coordinate.subgroupOf sylowImage).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor element helement
    exact ⟨sylowImage.mul_mem (sylowImage.mul_mem hactor helement.1)
      (sylowImage.inv_mem hactor), hnormal.conj_mem element helement.2 actor⟩
  have hnot : ¬ T ⊓ (coordinate.comap w.projection).map P.subtype ≤
      twoCoreAmbient P := by
    intro hcontained
    have hbot : coordinate = ⊥ := by
      apply le_bot_iff.mp
      intro element helement
      obtain ⟨lift, hlift, heq⟩ := helement.1
      have hliftCoordinate : lift ∈ coordinate.comap w.projection := by
        change w.projection lift ∈ coordinate
        simpa only [heq] using helement
      have hcore : (lift : G) ∈ q Γ cp.a := by
        rw [q, Γ.twoCoreAt_def]
        exact hcontained ⟨hlift, Subgroup.mem_map_of_mem P.subtype hliftCoordinate⟩
      rw [← (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer] at hcore
      have hkernel : lift ∈ w.projection.ker := by
        rw [w.kernel_eq]
        exact ⟨lift.property, hcore.2⟩
      exact heq.symm.trans hkernel
    have hcardOne := (Subgroup.eq_bot_iff_card coordinate).mp hbot
    omega
  have hclosure := SectionThree.normalClosure_eq_residual_sup_of_normal_sylow_image
    T (SevenSix.sectionThreeHypotheses ctx.sectionSeven) P
    ((pFamily_iff_pSet (⊤ : Subgroup G) T P).mp hlocal.1) hlocal.2
    w.projection w.surjective coordinate inf_le_left hcoordinateNormal hnot
  apply nine_two_center_card_four_of_residual_le_factor ctx w D hD
  have hresidual : Γ.e cp.a = twoResidualAmbient P := Γ.twoResidualAt_def cp.a
  rw [show EAt Γ cp.a = twoResidualAmbient P from hresidual]
  exact (le_sup_left.trans_eq hclosure.symm).trans
    (Subgroup.normalClosure_le_normal (show coordinate ≤ D from inf_le_right))

public theorem nine_two_center_card_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (m : ctx.Γ.Vertex)
    (hm : m ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq (ZAt ctx.Γ ctx.criticalPath.a)
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ ZAt ctx.Γ m) 2)
    (_hgenerate : QAt ctx.Γ m ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep)
    (hnot : ¬ QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅ZAt ctx.Γ ctx.criticalPath.a,
      QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let V := z Γ cp.a
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hcenter : V ≤ P :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core
      cp.a cp.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((Subgroup.map_subtype_le _).trans (by
          change q Γ cp.a ≤ stabilizer Γ cp.a
          rw [q, Γ.twoCoreAt_def]
          exact Subgroup.map_subtype_le _)))
  obtain ⟨w⟩ := exists_quotientModuleWitness P V hcenter
    (stabilizer_le_normalizer_z Γ cp.a)
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom V w.action
  let sylowImage := (T.subgroupOf P).map w.projection
  let actor := ((q Γ cp.firstStep ⊓ q Γ m).subgroupOf P).map w.projection
  have hTP : T ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  obtain ⟨_, sylow, hsylow⟩ := (SevenSix.edge_local_data ctx.sectionSeven Γ cp).1.1.1.2.1
  have hnative : (sylow : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hsylow
  let quotientSylow := sylow.mapSurjective w.surjective
  have himage : (quotientSylow : Subgroup w.X) = sylowImage := by
    change (sylow : Subgroup P).map w.projection = _
    rw [hnative]
  obtain ⟨hactorT, _, _, hfixed⟩ :=
    nine_two_fixed_index ctx.sectionSeven Γ cp m hm hindex hnot
  have hactorP := hactorT.trans hTP
  have hactorSylow : actor ≤ (quotientSylow : Subgroup w.X) := by
    rw [himage]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P hactorT)
  have hfixedIndex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup actor V) := by
    rw [w.fixedPoints_card _ hactorP]
    exact hfixed
  have hfixedSylow : commutatorAction actor V ≤
      FixedPoints.subgroup (quotientSylow : Subgroup w.X) V := by
    rw [himage]
    exact nine_two_commutator_fixed_by_sylow ctx.toLocalContext m hcomm w
  have hlocal := nine_two_quotient_hypotheses ctx.sectionSeven Γ cp m hnot w
  obtain ⟨D, hD, hnormalizer⟩ := SectionOne.oneSeven_factor_of_fixed_index_two
    hlocal quotientSylow actor hactorSylow hfixedIndex hfixedSylow
  rw [himage] at hnormalizer
  have hnormal := factor_normal_of_odd_core_sup sylowImage D hD hnormalizer
    (SectionEight.local_quotient_oddCore_sup_sylow ctx.sectionSeven Γ cp w)
  exact nine_two_center_card_four_of_normal_factor ctx.toLocalContext w D hD hnormal

end Stellmacher.SectionNine
