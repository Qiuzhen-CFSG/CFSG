module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.AmbientSylow
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.HeldActor
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Held
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The original ambient Held component in E.6.18

The actual U-action on J is transported through a Held equivalence. Its
trivial intersection with the inner automorphisms gives U ∩ J = 1, hence
|V ∩ J| ≤ |V:U| ≤ 4. The ambient Sylow promotion theorem identifies the
original Q as Sylow in JQ. Its intersection with J is an actual Sylow
subgroup fixed by U, so the checked Held pointwise-fixer result makes the
U-action trivial. Component restriction then lifts the original L.

For a quasisimple J specified by J/Z(J) ≃ He, the proved odd-primary bound
makes its center a two-group. An odd-center input therefore gives the Held
equivalence. That genuine two-primary cover input remains explicit here;
this module does not claim the completed source classification.

Source: Aschbacher–Smith, E.6.18, printed p.252, with the ambient hypotheses
retained to avoid the false unrestricted Held inspection.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
variable {G : Type*} [Group G] [Finite G] {V M A U J L : Subgroup G}

/-- The actual Held branch of the original component-product argument. -/
theorem held_component_centralizes_of_equiv
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hm : 2 < localM V)
    (hAU : A ≤ U) (hUV : U ≤ V) (hA : A ≠ ⊥)
    (hc : subgroupCorank V U ≤ 2)
    (hJA : J ≤ centralizer (A : Set G))
    (hJN : centralizer (A : Set G) ≤ normalizer (J : Set G))
    (hLJ : L ≤ J) (hLU : L ≤ centralizer (U : Set G)) (hs : IsSeven L)
    (e : J ≃* Held.He) : J ≤ centralizer (U : Set G) := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQA : Q ≤ centralizer (A : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (hAU.trans hUV))
  have hUN : U ≤ normalizer (J : Set G) :=
    (hUV.trans (V.le_centralizer.trans (Subgroup.centralizer_le (hAU.trans hUV)))).trans hJN
  let r : U →* MulAut J := J.normalizerMonoidHom.comp (inclusion hUN)
  let f : U →* MulAut Held.He := (MulAut.congr e).toMonoidHom.comp r
  have f_apply (u : U) (j : J) : f u (e j) = e (r u j) := by
    change e (r u (e.symm (e j))) = e (r u j)
    rw [e.symm_apply_apply]
  let P := f.range
  let D := (L.subgroupOf J).map e.toMonoidHom
  have hp : IsPGroup 2 P := ((IsElementaryAbelian.isPGroup 2 V).to_le hUV).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  have hsD : IsSeven D := hs.of_equiv
    ((subgroupOfEquivOfLe hLJ).symm.trans (e.subgroupMap (L.subgroupOf J)))
  have hDF : D ≤ FixedPoints.subgroup P Held.He := by
    rintro _ ⟨j,hj,rfl⟩ a
    obtain ⟨u,hu⟩ := a.property
    change a.val (e j) = e j
    rw [← hu]
    rw [f_apply]
    apply congrArg e
    apply Subtype.ext
    change (u : G) * (j : G) * (u : G)⁻¹ = (j : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hLU hj u u.property)
  have hinner := HeldInspection.inner_intersection_eq_bot P hp D hDF hsD
  have hUJ : U ⊓ J = ⊥ := by
    apply le_antisymm _ bot_le
    intro u hu
    let uj : J := ⟨u,hu.2⟩
    let uu : U := ⟨u,hu.1⟩
    have hfe : f uu = MulAut.conj (e uj) := by
      apply MulEquiv.ext
      intro z
      obtain ⟨j,rfl⟩ := e.surjective z
      rw [f_apply]
      change e (r uu j) = e uj * e j * (e uj)⁻¹
      rw [← map_inv,← map_mul,← map_mul]
      rfl
    have hfbot : f uu = 1 := by
      apply mem_bot.mp
      rw [← hinner]
      exact ⟨⟨uu,rfl⟩,⟨e uj,hfe.symm⟩⟩
    have hconj : MulAut.conj (e uj) = MulAut.conj 1 := by
      rw [← hfe,hfbot,map_one]
    have heu : e uj = 1 :=
      (conj_injective_of_center_eq_bot Held.LocalPairs.center_eq_bot) hconj
    exact congrArg Subtype.val (e.map_eq_one_iff.mp heu)
  have hVJcard : Nat.card (V ⊓ J : Subgroup G) ≤ 4 := by
    have hi : U ⊓ (V ⊓ J) = ⊥ := by
      rw [← inf_assoc,inf_eq_left.mpr hUV,hUJ]
    have hb : Nat.card (V ⊓ J : Subgroup G) = U.relIndex (V ⊓ J) := by
      rw [← inf_relIndex_right,hi,relIndex_bot_left]
    have hpow : U.relIndex V = 2 ^ subgroupCorank V U := by
      rw [subgroupCorank_eq_quotient_finrank]
      exact Subgroup.relIndex_eq_two_pow_quotient_finrank V U
    rw [hb]
    apply (relIndex_le_of_le_right (H := U) inf_le_left (by rw [hpow]; positivity)).trans
    rw [hpow]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hc
  obtain ⟨S,hS⟩ := h.sylow_component_product_of_small_intersection hm
    (hAU.trans hUV) hA hJA (hQA.trans hJN) hVJcard
  let B := J ⊔ Q
  let JB := J.subgroupOf B
  let : JB.Normal := (normal_subgroupOf_iff_le_normalizer (show J ≤ B from le_sup_left)).mpr
    (sup_le J.le_normalizer (hQA.trans hJN))
  obtain ⟨SJ,hSJ⟩ := S.exists_subgroupOf_eq_of_normal JB
  let ej : JB ≃* J := subgroupOfEquivOfLe (show J ≤ B from le_sup_left)
  let SJ' : Sylow 2 J := SJ.mapSurjective (f := ej.toMonoidHom) ej.surjective
  have hSJQ : ∀ j ∈ (SJ' : Subgroup J), (j : G) ∈ Q := by
    rintro _ ⟨j,hj,rfl⟩
    rw [hSJ] at hj
    have hh := mem_map_of_mem B.subtype hj
    rw [hS] at hh
    exact hh
  let SH : Sylow 2 Held.He := SJ'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hfix : ∀ a ∈ P, ∀ s ∈ (SH : Subgroup Held.He), a s = s := by
    rintro _ ⟨u,rfl⟩ _ ⟨j,hj,rfl⟩
    change f u (e j) = e j
    rw [f_apply]
    apply congrArg e
    apply Subtype.ext
    change (u : G) * (j : G) * (u : G)⁻¹ = (j : G)
    exact mul_inv_eq_iff_eq_mul.mpr ((hSJQ j hj).2 u (hUV u.property))
  have hP := HeldInspection.eq_bot_of_fixes_sylow P hp D hDF hsD SH hfix
  intro j hj u hu
  have hf : f ⟨u,hu⟩ = 1 := mem_bot.mp (hP ▸ (show f ⟨u,hu⟩ ∈ P from ⟨⟨u,hu⟩,rfl⟩))
  have hh := congrArg (fun a : MulAut Held.He => a (e ⟨j,hj⟩)) hf
  rw [f_apply] at hh
  change e (r ⟨u,hu⟩ ⟨j,hj⟩) = e ⟨j,hj⟩ at hh
  have hconj := congrArg Subtype.val (e.injective hh)
  change u * j * u⁻¹ = j at hconj
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- The literal central quotient yields an actual Held equivalence once its
odd center is known; the independent odd-primary calculation kills that center. -/
private theorem held_equiv_of_odd_center
    [IsQuasisimple J] (e : (J ⧸ center J) ≃* Held.He)
    (hodd : Odd (Nat.card (center J))) : Nonempty (J ≃* Held.He) := by
  have hz : center J = ⊥ := card_eq_one.mp
    ((Held.OddPrimary.source_center_isPGroup ⟨e⟩).card_eq_or_dvd.resolve_right
      hodd.not_two_dvd_nat)
  let q : J →* Held.He := e.toMonoidHom.comp (QuotientGroup.mk' (center J))
  have hq : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',hz]
  exact ⟨MulEquiv.ofBijective q ⟨hq,e.surjective.comp (QuotientGroup.mk'_surjective _)⟩⟩

/-- The quasisimple Held cover branch retains only its genuine odd-center
input. All action, inner-centralizer and pointwise Sylow facts are constructed. -/
theorem held_component_centralizes_of_odd_center
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hm : 2 < localM V)
    (hAU : A ≤ U) (hUV : U ≤ V) (hA : A ≠ ⊥)
    (hc : subgroupCorank V U ≤ 2)
    (hJA : J ≤ centralizer (A : Set G))
    (hJN : centralizer (A : Set G) ≤ normalizer (J : Set G))
    (hLJ : L ≤ J) (hLU : L ≤ centralizer (U : Set G)) (hs : IsSeven L)
    [IsQuasisimple J] (e : (J ⧸ center J) ≃* Held.He)
    (hodd : Odd (Nat.card (center J))) : J ≤ centralizer (U : Set G) := by
  obtain ⟨ej⟩ := held_equiv_of_odd_center e hodd
  exact held_component_centralizes_of_equiv h hm hAU hUV hA hc hJA hJN hLJ hLU hs ej

/-- The actual containing-component consumer: a Held central quotient with
odd center lifts the original seven component from C_G(U) to C_G(A).
The earlier I.3.1 input supplies J, its normality and its component membership. -/
theorem held_component_lifts_of_odd_center
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    [IsElementaryAbelian 2 V] (hm : 2 < localM V)
    (hAU : A ≤ U) (hUV : U ≤ V) (hA : A ≠ ⊥)
    (hc : subgroupCorank V U ≤ 2)
    (hJ : IsComponentIn J (centralizer (A : Set G)))
    (hn : (J.subgroupOf (centralizer (A : Set G))).Normal)
    (hLJ : L ≤ J) (hL : CentralizerComponent U L) (hs : IsSeven L)
    (e : (J ⧸ center J) ≃* Held.He)
    (hodd : Odd (Nat.card (center J))) : CentralizerComponent A L := by
  let : IsQuasisimple J := hJ.quasisimple
  have hJU := held_component_centralizes_of_odd_center h hm hAU hUV hA hc hJ.1
    ((normal_subgroupOf_iff_le_normalizer hJ.1).mp hn) hLJ hL.1 hs e hodd
  have hJC := hJ.restrict hJU (Subgroup.centralizer_le hAU)
  have he := hL.2.eq_of_le hJC.2 (show L.subgroupOf (centralizer (U : Set G)) ≤
    J.subgroupOf (centralizer (U : Set G)) from fun _ hx => hLJ hx)
  have he' : L = J := by
    simpa only [map_subgroupOf_eq_of_le hL.1,map_subgroupOf_eq_of_le hJU] using
      congrArg (Subgroup.map (centralizer (U : Set G)).subtype) he
  rw [he']
  exact hJ

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
