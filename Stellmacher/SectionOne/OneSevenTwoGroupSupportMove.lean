module
public import Stellmacher.SectionOne.OneSevenFactorConjugation
public import Stellmacher.SectionOne.OneSevenTransvectionSupportSelection
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A two-group moves a canonical support in a module of order sixteen

For a faithful Section One action on an elementary module of order sixteen,
any supplied two-subgroup of order greater than four moves a selected canonical
factor's support to a distinct complementary support. No Sylow conjugacy or
transitivity premise is needed.

If the two-group normalized the factor, it would preserve its four-element
support and its coprime fixed complement, also of order four. Each restricted
action has a nonidentity fixed point and hence image of order at most two.
Faithfulness on the complementary product bounds the two-group order by four,
a contradiction. Distinct canonical factors have disjoint four-element
supports; their join therefore exhausts the sixteen-element module.

This supplies the actual exchanging actor in the center-containment argument
following Stellmacher (9.9)(3), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne
open scoped IsMulCommutative
universe u

private theorem two_group_four_action_image_bound
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [MulDistribMulAction K V]
    (hK : IsPGroup 2 K) (hV : Nat.card V = 4) :
    Nat.card (MulDistribMulAction.toMulAut K V).range ≤ 2 := by
  have hone : (1 : V) ∈ MulAction.fixedPoints K V := by
    rw [MulAction.mem_fixedPoints]
    exact fun k => smul_one k
  obtain ⟨point,hpoint,hne⟩ := hK.exists_fixed_point_of_prime_dvd_card_of_fixed_point V
    (by rw [hV]; decide) hone
  apply card_mulAut_subgroup_le_two_of_fixed_point hV point hne.symm
  rintro actor ⟨k,rfl⟩
  exact hpoint k

private theorem two_group_normalizing_factor_card_le_four
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (D S : Subgroup K)
    (hD : IsOneSevenFactor (V := V) D) (hS : IsPGroup 2 S)
    (hV : Nat.card V = 16) (hnorm : S ≤ Subgroup.normalizer (D : Set K)) :
    Nat.card S ≤ 4 := by
  let F := (commutator D).map D.subtype
  let U := commutatorAction F V
  let C := FixedPoints.subgroup F V
  have hFU : Nat.card U = 4 := hD.2.1.2.2
  have hSF : S ≤ Subgroup.normalizer (F : Set K) := by
    intro s hs
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change F.map (MulAut.conj s).toMonoidHom = F
    dsimp only [F]
    rw [Subgroup.map_subtype_commutator,Subgroup.map_commutator]
    have hmap : D.map (MulAut.conj s).toMonoidHom = D :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm hs)
    rw [hmap]
  let _ : IsInvariant S V U := commutatorAction_isInvariant_of_normalizing_actor S F hSF
  let _ : IsInvariant S V C := fixedPoints_isInvariant_of_normalizing_actor S F hSF
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    rw [show Nat.card F = 3 from hD.2.1.2.1,hV]
    decide
  have hcompl : IsCompl C U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop inferInstance
  have hC : Nat.card C = 4 := by
    have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes C U
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    rw [hcompl.inf_eq_bot,hcompl.sup_eq_top,Subgroup.card_bot,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv,hFU,hV] at hcard
    omega
  let actionU := MulDistribMulAction.toMulAut S U
  let actionC := MulDistribMulAction.toMulAut S C
  let combined : S →* actionU.range × actionC.range :=
    actionU.rangeRestrict.prod actionC.rangeRestrict
  have hinj : Function.Injective combined := by
    apply (MonoidHom.ker_eq_bot_iff combined).mp
    apply le_bot_iff.mp
    intro s hs
    have hU : actionU s = 1 := congrArg Subtype.val (congrArg Prod.fst hs)
    have hC : actionC s = 1 := congrArg Subtype.val (congrArg Prod.snd hs)
    have hfixed : (s : K) ∈ fixingSubgroup K (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro point _
      have hmem : point∈C⊔U := hcompl.sup_eq_top.symm ▸ Subgroup.mem_top point
      let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
      obtain ⟨c,hc,u,hu,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
      have hcfix : (s:K) • c=c :=
        congrArg Subtype.val (MulEquiv.congr_fun hC (⟨c,hc⟩ : C))
      have hufix : (s:K) • u=u :=
        congrArg Subtype.val (MulEquiv.congr_fun hU (⟨u,hu⟩ : U))
      rw [smul_mul',hcfix,hufix]
    rw [hyp.action_faithful] at hfixed
    exact Subtype.ext hfixed
  have hcard := Nat.card_le_card_of_injective combined hinj
  rw [Nat.card_prod] at hcard
  have hUbound := two_group_four_action_image_bound (K := S) hS hFU
  have hCbound := two_group_four_action_image_bound (K := S) hS hC
  exact hcard.trans ((Nat.mul_le_mul hUbound hCbound).trans (by decide))

public theorem oneSevenFactor_exists_complementary_two_group_conjugate
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (D S : Subgroup K)
    (hD : IsOneSevenFactor (V := V) D) (hS : IsPGroup 2 S)
    (hV : Nat.card V = 16) (hlarge : 4 < Nat.card S) :
    ∃ actor : S,
      commutatorAction D V ≠ (commutatorAction D V).map
        (MulDistribMulAction.toMulAut K V (actor : K)).toMonoidHom ∧
      commutatorAction D V ⊔ (commutatorAction D V).map
        (MulDistribMulAction.toMulAut K V (actor : K)).toMonoidHom = ⊤ := by
  have hnot : ¬ S ≤ Subgroup.normalizer (D : Set K) := by
    intro hnorm
    have hbound := two_group_normalizing_factor_card_le_four hyp D S hD hS hV hnorm
    omega
  obtain ⟨actor,hactor,hnotactor⟩ := SetLike.not_le_iff_exists.mp hnot
  have hne : D ≠ D.conjBy actor := by
    intro heq
    exact hnotactor (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm)
  have hconj := hD.conjBy D actor
  have hdisj := oneSevenFactor_support_disjoint_of_ne hyp D (D.conjBy actor) hD hconj hne
  have hsupportNe : commutatorAction D V ≠ commutatorAction (D.conjBy actor) V := by
    intro heq
    have hbot := hdisj.eq_bot
    rw [← heq,inf_idem] at hbot
    have hcard := Subgroup.card_eq_one.mpr hbot
    rw [hD.2.2.1] at hcard
    omega
  have hspan : commutatorAction D V ⊔ commutatorAction (D.conjBy actor) V = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
      (commutatorAction D V) (commutatorAction (D.conjBy actor) V)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    rw [hdisj.eq_bot,Subgroup.card_bot,hD.2.2.1,hconj.2.2.1,one_mul] at hcard
    rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv,hV]
    omega
  refine ⟨⟨actor,hactor⟩,?_,?_⟩
  · rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy] at hsupportNe
    exact hsupportNe
  · rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy] at hspan
    exact hspan

end Stellmacher.SectionOne
