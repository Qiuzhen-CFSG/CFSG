module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ResidualCore
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ExtraspecialReduction
public import Theory.GroupTheory.PPerfectHom
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Survival through the scalar kernel of the first Janko centralizer

The cubic scalar moves the whole extraspecial two-core. A non-two subgroup
of its full preimage, normalized by that core, is therefore the full preimage.
Its ambient normalizer is the first involution centralizer, since the center
of its characteristic two-core is the marked involution.

Consequently a two-perfect seed normalized by a full-Sylow parabolic outside
that centralizer cannot have two-group image in M22. This retains the cubic
kernel in the actual projection. Once a solvable normal closure has an image
divisible by three, the native M22 Sylow-overgroup theorem bounds its actor's
order by 2^21 times 9. The original marked application is in
NaturalSource/Local/Normalizers/JankoMax2.

Source: Aschbacher–Smith, 12.5.4, printed p.819/PDF p.836. Native scalar
and extraspecial certificates retain the attribution of the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.InvolutionCentralizers.First.QuotientExtension
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

theorem scalar_preimage_of_normalized_non_two (U : Subgroup centralizer)
    (hUR : U ≤ R) (hU : ¬ IsPGroup 2 U)
    (hn : Q ≤ normalizer (U : Set centralizer)) : U = R := by
  let f : U →* scalarSubgroup :=
    (centralizerExtension.rightHom.comp U.subtype).codRestrict scalarSubgroup
      (fun u => hUR u.property)
  have hk : IsPGroup 2 f.ker := by
    let j : f.ker →* Q := {
      toFun u := ⟨u.val.val, by
        rw [← centralizerProjection_ker]
        exact congrArg scalarSubgroup.subtype u.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact pCore_isPGroup.of_injective j (fun x y he =>
      Subtype.ext (Subtype.ext (congrArg Q.subtype he)))
  have hsur : Function.Surjective f := by
    let : Fact (Nat.card scalarSubgroup).Prime := ⟨scalarSubgroup_card ▸ Nat.prime_three⟩
    apply MonoidHom.range_eq_top.mp
    apply f.range.eq_bot_or_eq_top_of_prime_card.resolve_left
    intro he
    have hker : f.ker = ⊤ := by
      apply top_unique
      intro u _
      exact mem_bot.mp (he ▸ (show f u ∈ f.range from ⟨u,rfl⟩))
    apply hU
    exact (hker ▸ hk).of_equiv topEquiv
  obtain ⟨x, hx⟩ := hsur scalarGenerator
  have hxs : centralizerExtension.rightHom (x : centralizer) = scalarElement :=
    congrArg scalarSubgroup.subtype hx
  have hxQ : (x : centralizer)^3 ∈ Q := by
    rw [←centralizerProjection_ker, MonoidHom.mem_ker, map_pow, hxs]
    exact scalarElement_order ▸ pow_orderOf_eq_one scalarElement
  have hxpow : (x : centralizer)^(3 * 2^13) = 1 := by
    have he := congrArg Q.subtype (pow_card_eq_one' (x := (⟨(x : centralizer)^3,hxQ⟩ : Q)))
    simpa only [map_pow, map_one, coe_subtype, centralizer_twoCore_card, ←pow_mul] using he
  let y : centralizer := (x : centralizer)^(2^14)
  have hys : centralizerExtension.rightHom y = scalarElement := by
    rw [show y = (x : centralizer)^(2^14) from rfl, map_pow, hxs,
      pow_eq_pow_mod _ (scalarElement_order ▸ pow_orderOf_eq_one scalarElement)]
    norm_num
  have hy3 : y^3 = 1 := by
    rw [show y = (x : centralizer)^(2^14) from rfl, ←pow_mul,
      show 2^14 * 3 = (3 * 2^13) * 2 by norm_num, pow_mul, hxpow, one_pow]
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 (by
    intro he
    have hh : scalarElement = 1 := hys.symm.trans (he ▸ map_one _)
    have ho := scalarElement_order
    rw [hh, orderOf_one] at ho
    contradiction)
  have hyU : y ∈ U := U.pow_mem x.property _
  have hQU : Q ≤ U := by
    change pCore 2 centralizer ≤ U
    rw [← scalar_lift_moves_entire_core y hyo hys, commutator_comm]
    exact (commutator_mono (zpowers_le.mpr hyU) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hn)
  apply le_antisymm hUR
  intro r hr
  obtain ⟨u, hu⟩ := hsur ⟨centralizerExtension.rightHom r,hr⟩
  have hu' : centralizerExtension.rightHom (u : centralizer) =
      centralizerExtension.rightHom r := congrArg scalarSubgroup.subtype hu
  have hdiff : r * (u : centralizer)⁻¹ ∈ Q := by
    rw [←centralizerProjection_ker, MonoidHom.mem_ker, map_mul, map_inv, hu', mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using U.mul_mem (hQU hdiff) u.property

theorem scalar_preimage_normalizer :
    normalizer (R.map centralizer.subtype : Set Model) = centralizer := by
  have hcore : (R.map centralizer.subtype).pCoreIn 2 = centralizer.pCoreIn 2 := by
    rw [←map_pCoreIn_of_injective 2 R centralizer.subtype centralizer.subtype_injective]
    rw [←pCore_eq_map_of_normal_of_le 2 R Q_le_R]
    rfl
  apply le_antisymm
  · have hn := normalizer_le_normalizer_characteristic_image
      (R.map centralizer.subtype) (pCore 2 (R.map centralizer.subtype))
    change normalizer (R.map centralizer.subtype : Set Model) ≤
      normalizer ((R.map centralizer.subtype).pCoreIn 2 : Set Model) at hn
    rw [hcore, LocalStructure.ElementaryNormalizerCover.normalizer_firstCore] at hn
    exact hn
  · have hh := R.le_normalizer_map centralizer.subtype
    rw [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] at hh
    exact hh

theorem non_two_mathieu_image_of_external_normalizer
    (S : Sylow 2 Model) (hSC : (S : Subgroup Model) ≤ centralizer)
    (P : Subgroup Model) (hSP : (S : Subgroup Model) ≤ P)
    (hPC : ¬ P ≤ centralizer) (U : Subgroup H)
    (hp : IsPPerfect 2 U) (hU : ¬ IsPGroup 2 U)
    (hn : P ≤ normalizer (U.map (centralizer.subtype.comp H.subtype) : Set Model)) :
    ¬ IsPGroup 2 (U.map mathieuProjection) := by
  intro ht
  have hz : U.map mathieuProjection = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨u,hu,rfl⟩
    have he := DFunLike.congr_fun
      (hp.hom_eq_one_of_isPGroup ht (mathieuProjection.subgroupMap U)) ⟨u,hu⟩
    exact congrArg (U.map mathieuProjection).subtype he
  have hUR : U ≤ R.subgroupOf H := by
    rw [←mathieuProjection_ker]
    exact (Subgroup.map_eq_bot_iff _).mp hz
  let W := U.map H.subtype
  have hWR : W ≤ R := by
    rintro _ ⟨u,hu,rfl⟩
    exact hUR hu
  have hW : ¬ IsPGroup 2 W := fun ht => hU
    (ht.of_equiv (U.equivMapOfInjective H.subtype H.subtype_injective).symm)
  have hQW : Q ≤ normalizer (W : Set centralizer) := by
    have hQ : Q.map centralizer.subtype ≤ P :=
      (map_le_iff_le_comap.mpr (pCore_isPGroup.le_sylow_of_normal
        (S.subtype hSC))).trans hSP
    have hw := (W.map centralizer.subtype).le_normalizer_comap centralizer.subtype
    rw [comap_map_eq_self_of_injective centralizer.subtype_injective] at hw
    apply (map_le_iff_le_comap.mp (hQ.trans ?_)).trans hw
    simpa only [W, map_map] using hn
  have he : W = R := scalar_preimage_of_normalized_non_two W hWR hW hQW
  have hh : U.map (centralizer.subtype.comp H.subtype) = R.map centralizer.subtype := by
    rw [←map_map]
    exact congrArg (map centralizer.subtype) he
  rw [hh, scalar_preimage_normalizer] at hn
  exact hPC hn

theorem mathieu_kernel_card : Nat.card mathieuProjection.ker = 2 ^ 13 * 3 := by
  rw [mathieuProjection_ker, Nat.card_congr (subgroupOfEquivOfLe R_le_H).toEquiv]
  have hc := (Q.subgroupOf R).card_mul_index
  have hQ : Nat.card (Q.subgroupOf R) = 2 ^ 13 :=
    (Nat.card_congr (subgroupOfEquivOfLe Q_le_R).toEquiv).trans centralizer_twoCore_card
  have hi : (Q.subgroupOf R).index = 3 := by
    rw [index_eq_card, Nat.card_congr RQuotientEquivC3.toEquiv]
    simp
  rw [hQ, hi] at hc
  exact hc.symm

theorem actor_card_dvd_of_solvable_normal_three
    (S : Sylow 2 centralizer) (A N : Subgroup centralizer)
    (hSA : (S : Subgroup centralizer) ≤ A) (hNA : N ≤ A)
    (hn : A ≤ normalizer (N : Set centralizer)) (hs : Group.IsSolvable N)
    (h3 : 3 ∣ Nat.card ((N.subgroupOf H).map mathieuProjection)) :
    Nat.card A ∣ 2^21 * 9 := by
  let D := A.subgroupOf H
  let V := N.subgroupOf H
  let X := D.map mathieuProjection
  let W := V.map mathieuProjection
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal H
  let P := T.mapSurjective mathieuProjection_surjective
  have hPX : (P : Subgroup Sporadic.Mathieu.M22) ≤ X := by
    apply map_mono
    rw [hT]
    exact comap_mono hSA
  have hVX : W ≤ X := map_mono (comap_mono hNA)
  have hnorm : (W.subgroupOf X).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hVX).mpr
    have hnD : D ≤ normalizer (V : Set H) := by
      intro d hd v
      exact hn hd (v : centralizer)
    exact (map_mono hnD).trans (V.le_normalizer_map mathieuProjection)
  let j : V →* N := H.subtype.subgroupComap N
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg N.subtype he))
  let : Group.IsSolvable N := hs
  let : Group.IsSolvable V := Group.isSolvable_of_isSolvable_injective (f := j) hj
  have hsol : Group.IsSolvable W := Group.isSolvable_of_surjective
    (mathieuProjection.subgroupMap_surjective V)
  have hX : Nat.card X = 384 :=
    Sporadic.Mathieu.M22SolvableSylow.card_eq_384_of_solvable_normal_three
      X W hVX hnorm hsol h3 ⟨P,hPX⟩
  let f := mathieuProjection.comp D.subtype
  have hk : Nat.card f.ker ∣ 2^13 * 3 := by
    let j : f.ker →* mathieuProjection.ker := {
      toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    rw [←mathieu_kernel_card]
    exact card_dvd_of_injective j (fun x y he =>
      Subtype.ext (Subtype.ext (congrArg (fun z : mathieuProjection.ker => (z : H)) he)))
  have hD : Nat.card D ∣ (2^13 * 3) * 384 := by
    have hc := f.ker.card_mul_index
    rw [index_ker, show f.range = X from by simp [f, X, MonoidHom.range_comp], hX] at hc
    rw [←hc]
    exact Nat.mul_dvd_mul hk (dvd_refl 384)
  let d : D ≃* H.subgroupOf A := {
    toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hidx : (H.subgroupOf A).index ∣ 2 := by
    have hHi : H.index = 2 := by
      rw [index_eq_card, Nat.card_congr centralizerQuotientEquivC2.toEquiv]
      simp
    exact hHi ▸ H.relIndex_dvd_index_of_normal A
  have hc := (H.subgroupOf A).card_mul_index
  rw [←Nat.card_congr d.toEquiv] at hc
  have hd := Nat.mul_dvd_mul hD hidx
  rw [hc] at hd
  exact hd

end Janko4.InvolutionCentralizers.First.QuotientExtension
