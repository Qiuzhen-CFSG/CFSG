module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleSource
public import Theory.SpecificGroups.Triality.InvolutionFixedRank
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import Theory.GroupAction.CentralCoverTwoCentral
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Nonsolvable

/-!
# Paired-source exclusion in the actual triality and Rudvalis fixed groups

For the proper completion of 14.2.15, retain the original full residual
D=O²(H), its placement in the canonical L, and the actual conjugation by the
central involution z. A perfect D maps into the derived fixed subgroup in
triality, whose three-rank is at most one. In the Rudvalis row the marked
central cover transports z's two-central inner action to an actual model
involution. The two-core kernel preserves D's three-rank, so rank two
forces nine to divide its centralizer, contradicting the checked model fact.

The literal original-prefix consumer obtains the complete 1.1.5 marking
and perfectness of O²(H) from the nonsolvable minimal-parabolic theorem.
The earlier placement D≤L, paired three-rank, and intrinsic Rudvalis
centerlessness remain explicit source inputs; no unmarked carrier
recognition or containing-row classification is inferred.

Source: Aschbacher--Smith, 14.2.15, printed pp.985--986, using 1.1.5(3)
and the triality and Rudvalis centralizer exclusions of A.3.12.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem marked_action_order_two
    (L Mc : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hout : ¬L ≤ Mc) (hC : centralizer ({z} : Set G) ≤ Mc)
    (a : MulAut L) (ha : ∀ x : L, (a x : G) = z * (x : G) * z⁻¹) :
    orderOf a = 2 := by
  have hpow : a ^ 2 = 1 := by
    ext x
    change (a (a x) : G) = (x : G)
    rw [ha, ha]
    have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
    calc
      z * (z * (x : G) * z⁻¹) * z⁻¹ =
          (z * z) * (x : G) * (z⁻¹ * z⁻¹) := by group
      _ = (x : G) := by
        have hz' : z⁻¹ * z⁻¹ = 1 := by
          rw [←pow_two,inv_pow,hz2,inv_one]
        rw [←pow_two,hz2,hz',one_mul,mul_one]
  have hne : a ≠ 1 := by
    intro h
    apply hout
    intro x hx
    apply hC
    rw [mem_centralizer_singleton_iff]
    have hf : z * x * z⁻¹ = x := by
      simpa only [h, MulAut.one_apply] using (ha ⟨x,hx⟩).symm
    exact (mul_inv_eq_iff_eq_mul.mp hf).symm
  exact orderOf_eq_prime hpow hne

/-- The actual perfect subgroup in the triality fixed group cannot have three-rank two. -/
theorem proper_triality_marked_pair_false
    (L K : Subgroup G) (z : G) (a : MulAut L)
    (ha : ∀ x : L, (a x : G) = z * (x : G) * z⁻¹)
    (hao : orderOf a = 2) (hi : a ∈ (MulAut.conj (G := L)).range)
    {n : ℕ} (hn : 0 < n) (hm : Triality.Standard.IsTrialityGroupAt (2^n) L)
    (hKL : K ≤ L) (hKC : K ≤ centralizer ({z} : Set G))
    [Group.IsPerfect K] (hr : 2 ≤ primeRank 3 K) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff L n hn).mp hm
  let b := MulAut.congr e a
  have hbo : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans hao
  have hbi : b ∈ MulAut.innerSubgroup _ := by
    obtain ⟨x,hx⟩ := hi
    exact ⟨e x, by change MulAut.conj (e x) = MulAut.congr e a; rw [←MulAut.congr_conj,hx]⟩
  let f : K →* a.fixedSubgroup :=
    (inclusion hKL).codRestrict _ (fun x => by
      rw [MulAut.mem_fixedSubgroup]
      apply Subtype.ext
      rw [ha]
      change z * (x : G) * z⁻¹ = (x : G)
      have hc := mem_centralizer_singleton_iff.mp (hKC x.property)
      rw [←hc,mul_inv_cancel_right])
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun v : a.fixedSubgroup => ((v : L) : G)) h)
  let c := MulAut.fixedSubgroupCongr e a
  let g : K →* b.fixedSubgroup := c.toMonoidHom.comp f
  have hg : Function.Injective g := c.injective.comp hf
  have hder : (commutator K).map g ≤ commutator b.fixedSubgroup := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  have hmem (x : K) : g x ∈ commutator b.fixedSubgroup :=
    hder (mem_map_of_mem g Group.IsPerfect.mem_commutator)
  let d := g.codRestrict (commutator b.fixedSubgroup) hmem
  have hd : Function.Injective d := by
    intro x y h
    exact hg (congrArg Subtype.val h)
  have hr' := (Theory.GroupTheory.primeRank_le_of_injective 3 d hd).trans
    (Triality.Standard.InvolutionFixedRank.inner_fixed_derived_threeRank_le_one n hn b hbo hbi)
  omega

/-- Three-rank two forces a subgroup of order divisible by nine. -/
private theorem nine_dvd_of_threeRank_two {D : Type*} [Group D] [Finite D]
    (hr : 2 ≤ primeRank 3 D) : 9 ∣ Nat.card D := by
  obtain ⟨E,hE,hEc⟩ := exists_elementaryAbelian_card_primeRank (G := D) (p := 3)
  have hd : 3 ^ 2 ∣ Nat.card E := hEc ▸ Nat.pow_dvd_pow 3 hr
  exact hd.trans E.card_subgroup_dvd_card

/-- The actual Rudvalis fixed subgroup cannot contain the paired source three-rank. -/
theorem proper_rudvalis_marked_pair_false
    (L K : Subgroup G) (z : G) (a : MulAut L)
    (ha : ∀ x : L, (a x : G) = z * (x : G) * z⁻¹)
    (hao : orderOf a = 2) (hi : a ∈ (MulAut.conj (G := L)).range)
    [IsQuasisimple L] (P : Sylow 2 L) (hP : ∀ x : P, a (x : L) = x)
    (hz : center Rudvalis.Model = ⊥) (e : (L ⧸ pCore 2 L) ≃* Rudvalis.Model)
    (hKL : K ≤ L) (hKC : K ≤ centralizer ({z} : Set G))
    (hr : 2 ≤ primeRank 3 K) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hcentral : f.ker ≤ center L := by
    rw [hk]
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    exact (le_solvableRadical (pCore 2 L) inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  obtain ⟨t,ht,_,heq⟩ := MulAut.exists_twoCentral_model_of_central_cover f hf
    hcentral hz a hi hao P (fun x hx => hP ⟨x,hx⟩)
  let g : K →* Rudvalis.InvolutionCentralizers.Centralizer t :=
    (f.comp (inclusion hKL)).codRestrict _ (fun x => by
      change f (inclusion hKL x) ∈ centralizer ({t} : Set Rudvalis.Model)
      rw [←MulAut.fixedSubgroup_conj,MulAut.mem_fixedSubgroup,←heq]
      apply congrArg f
      apply Subtype.ext
      rw [ha]
      change z * (x : G) * z⁻¹ = (x : G)
      have hc := mem_centralizer_singleton_iff.mp (hKC x.property)
      rw [←hc,mul_inv_cancel_right])
  let j : g.ker →* f.ker := {
    toFun x := ⟨inclusion hKL x.val, congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun v : f.ker => ((v : L) : G)) h)
  have hgk : IsPGroup 2 g.ker :=
    (show IsPGroup 2 f.ker from hk ▸ pCore_isPGroup).of_injective j hj
  obtain ⟨m,hm⟩ := hgk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hr' : 2 ≤ primeRank 3 (Rudvalis.InvolutionCentralizers.Centralizer t) :=
    hr.trans (primeRank_le_of_coprime_ker 3 g hcop)
  exact Rudvalis.InvolutionCentralizers.centralizer_not_nine t ht
    (nine_dvd_of_threeRank_two hr')

/-- The literal original paired residual excludes the marked triality and Rudvalis rows.
The earlier-source placement of the full residual in L remains explicit. -/
theorem source_proper_quasisimple_pair_terminal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hZS : centralInvolutions T ≤ S)
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥)
    (hpair : (pResidual 2 H).map H.subtype ≤
      (solvableResidual (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G)).map
        (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G).subtype)
    (hr : 2 ≤ primeRank 3 ((pResidual 2 H).map H.subtype))
    (hRu : center Rudvalis.Model = ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple L → ¬ClassificationModels.IsBenderModel L ∧
      ∃ z : G, z ∈ centralInvolutions T ∧ orderOf z = 2 ∧
      L = ⁅L,zpowers z⁆ ∧ ¬L ≤ Mc ∧
      ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧
        ModelAction115 L α ∧
        (∀ n : ℕ, 0 < n → Triality.Standard.IsTrialityGroupAt (2^n) L →
          α ∉ (MulAut.conj (G := L)).range) ∧
        (∀ _f : (L ⧸ pCore 2 L) ≃* Rudvalis.Model, ¬TwoCentralInner α) := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  let D := (pResidual 2 H).map H.subtype
  change IsQuasisimple L → ¬ClassificationModels.IsBenderModel L ∧
    ∃ z : G, z ∈ centralInvolutions T ∧ orderOf z = 2 ∧
      L = ⁅L,zpowers z⁆ ∧ ¬L ≤ Mc ∧ ∃ α : MulAut L,
      (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧ ModelAction115 L α ∧
      (∀ n : ℕ, 0 < n → Triality.Standard.IsTrialityGroupAt (2^n) L →
        α ∉ (MulAut.conj (G := L)).range) ∧
      (∀ _f : (L ⧸ pCore 2 L) ≃* Rudvalis.Model, ¬TwoCentralInner α)
  intro hq
  let := hq
  have hKH : K ≤ H := le_sup_left.trans_eq hgen
  have hns : ¬Group.IsSolvable H := by
    intro hh
    let := hh
    exact Chapter1.mem_L_not_isSolvable hK
      (Group.isSolvable_of_isSolvable_injective (f := inclusion hKH)
        (inclusion_injective hKH))
  obtain ⟨_,hP,_,_,_,_⟩ := source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany
    hcard e H hH
  let : Group.IsPerfect (pResidual 2 H) :=
    ChapterB.minimalParabolic_nonsolvable_residual_perfect (T.subtype hH.1.1.2) hP hns
  let : Group.IsPerfect D := Group.IsPerfect.map H.subtype
  obtain ⟨hnb,z,hzZ,hz,hcomm,hout,a,ha,hm⟩ :=
    source_proper_quasisimple_catalogue_entry hG T hempty hM hu hmany hcard e
      H hH K S hST hi hN hplacement hgen hK hSN hZS hcore hq
  have hcZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hspan : zpowers z = centralInvolutions T :=
    eq_of_le_of_card_ge (zpowers_le.mpr hzZ) (by rw [Nat.card_zpowers,hz,hcZ])
  have hCz : centralizer ({z} : Set G) ≤ Mc := by
    rw [←centralizer_closure,←zpowers_eq_closure,hspan]
    exact (hu.symm ▸ Set.mem_singleton Mc).2
  have hao := marked_action_order_two L Mc z hz hout hCz a ha
  have hDC : D ≤ centralizer ({z} : Set G) :=
    ((map_subtype_le _).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hzZ))
  refine ⟨hnb,z,hzZ,hz,hcomm,hout,a,ha,hm,?_,?_⟩
  · intro n hn ht hinner
    exact proper_triality_marked_pair_false L D z a ha hao hinner hn ht hpair hDC hr
  · intro f htwo
    obtain ⟨hinner,ho,P,hP⟩ := htwo
    exact proper_rudvalis_marked_pair_false L D z a ha ho hinner P hP hRu f hpair hDC hr

end CFSG.Quasithin.Chapter14.Section02
