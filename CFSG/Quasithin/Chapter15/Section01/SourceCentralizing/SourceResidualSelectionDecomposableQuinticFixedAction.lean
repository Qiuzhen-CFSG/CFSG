module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticLocal
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.SubgroupConjugation.PairPermutation
public import Theory.Representation.BinaryPlaneCubic

/-!
# Actual fixed-module alternatives in the exchanged quintic row

The third local's module lies in the original pair of Thompson four-groups.
An invariant subgroup of order eight intersects each exchanged four-group
in a line. The actor permutes these two lines, so its squares centralize
their product. The quotient of the module by that product has order two;
therefore every fourth power centralizes the module. Source ordering would
make the actual third-local action a two-group, contrary to reducedness.
The surviving four-element module retains its actual symmetric-three action;
the sixteen-element alternative is the whole original fixed subgroup.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_square (B : Subgroup G) (g : G) :
    B.map (MulAut.conj (g^2)).toMonoidHom =
      (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext b
  simp [MulAut.conj_apply,pow_two,mul_assoc]

omit [Finite G] in
private theorem square_centralizes_permuted_lines
    (H U₁ U₂ : Subgroup G) (hc₁ : Nat.card U₁ = 2) (hc₂ : Nat.card U₂ = 2)
    (hp : ∀ g ∈ H,
      (U₁.map (MulAut.conj g).toMonoidHom = U₁ ∧ U₂.map (MulAut.conj g).toMonoidHom = U₂) ∨
      (U₁.map (MulAut.conj g).toMonoidHom = U₂ ∧ U₂.map (MulAut.conj g).toMonoidHom = U₁)) :
    ∀ g ∈ H, g^2 ∈ centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
  intro g hg
  have hn₁ : g^2 ∈ normalizer (U₁ : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change U₁.map (MulAut.conj (g^2)).toMonoidHom=U₁
    rw [map_conj_square]
    rcases hp g hg with hh | hh <;> simp only [hh.1,hh.2]
  have hn₂ : g^2 ∈ normalizer (U₂ : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change U₂.map (MulAut.conj (g^2)).toMonoidHom=U₂
    rw [map_conj_square]
    rcases hp g hg with hh | hh <;> simp only [hh.1,hh.2]
  have hc1 := normalizer_le_centralizer_of_card_two U₁ hc₁ hn₁
  have hc2 := normalizer_le_centralizer_of_card_two U₂ hc₂ hn₂
  have h₁ : zpowers (g^2) ≤ centralizer (U₁ : Set G) := zpowers_le.mpr hc1
  have h₂ : zpowers (g^2) ≤ centralizer (U₂ : Set G) := zpowers_le.mpr hc2
  exact (le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp h₁)
    (le_centralizer_iff.mp h₂))) (mem_zpowers _)

omit [Finite G] in
private theorem fourth_centralizes_of_index_two
    (H W Q : Subgroup G) [IsElementaryAbelian 2 W]
    (hQW : Q ≤ W) (hi : Q.relIndex W = 2)
    (hHW : H ≤ normalizer (W : Set G)) (hHQ : H ≤ normalizer (Q : Set G))
    (hsq : ∀ g ∈ H, g^2 ∈ centralizer (Q : Set G)) :
    ∀ g ∈ H, g^4 ∈ centralizer (W : Set G) := by
  have hcomm : ⁅H,W⁆ ≤ Q := by
    rw [commutator_comm]
    exact commutator_le_of_normalized_index_two W Q H hQW hi hHW hHQ
  intro g hg w hw
  let u := g^2
  let d := ⁅u,w⁆
  have hd : d ∈ Q := hcomm (commutator_mem_commutator (H.pow_mem hg 2) hw)
  have hd2 : d*d=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) d (hQW hd)
  have hud : u*d=d*u := (hsq g hg d hd).symm
  have hconj : u*w*u⁻¹=d*w := by dsimp [d]; simp [commutatorElement_def,mul_assoc]
  have hfour : g^4*w*(g^4)⁻¹=w := by
    calc
      _ = u*(u*w*u⁻¹)*u⁻¹ := by dsimp [u]; group
      _ = u*(d*w)*u⁻¹ := by rw [hconj]
      _ = (u*d*u⁻¹)*(u*w*u⁻¹) := by group
      _ = d*(d*w) := by rw [hud,mul_inv_cancel_right,hconj]
      _ = w := by rw [←mul_assoc,hd2,one_mul]
  exact (mul_inv_eq_iff_eq_mul.mp hfour).symm

private theorem eight_intersections
    (E Z₁ Z₂ W : Subgroup G) [IsElementaryAbelian 2 E]
    (he : E=Z₁⊔Z₂) (_hd : Disjoint Z₁ Z₂)
    (hc₁ : Nat.card Z₁=4) (hc₂ : Nat.card Z₂=4)
    (hcE : Nat.card E=16) (hWE : W≤E) (hcW : Nat.card W=8)
    (t : G) (htW : t∈normalizer (W : Set G))
    (htZ : Z₁.map (MulAut.conj t).toMonoidHom=Z₂) :
    Nat.card (W⊓Z₁ : Subgroup G)=2 ∧ Nat.card (W⊓Z₂ : Subgroup G)=2 := by
  have hZ₁E : Z₁≤E := he ▸ le_sup_left
  have hZ₂E : Z₂≤E := he ▸ le_sup_right
  have hcom : Z₁≤centralizer (W : Set G) := by
    intro z hz w hw
    exact congrArg Subtype.val (isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative E) ⟨w,hWE hw⟩ ⟨z,hZ₁E hz⟩)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes W Z₁
    (hcom.trans (Subgroup.centralizer_le_normalizer _))
  have hWmap : W.map (MulAut.conj t).toMonoidHom=W := mem_normalizer_iff_map_conj_eq.mp htW
  have hmap : (W⊓Z₁).map (MulAut.conj t).toMonoidHom=W⊓Z₂ := by
    rw [map_inf _ _ _ (MulAut.conj t).injective,
      hWmap,htZ]
  have hcards : Nat.card (W⊓Z₁ : Subgroup G)=Nat.card (W⊓Z₂ : Subgroup G) := by
    rw [←hmap,card_map_of_injective (MulAut.conj t).injective]
  have hdiv : Nat.card (W⊓Z₁ : Subgroup G) ∣ 4 :=
    hc₁ ▸ card_dvd_of_le (inf_le_right : W⊓Z₁≤Z₁)
  have hlo : 2≤Nat.card (W⊓Z₁ : Subgroup G) := by
    have hle := card_le_of_le (sup_le hWE hZ₁E)
    rw [hcE] at hle
    rw [hcW,hc₁] at hprod
    nlinarith
  have hne : Nat.card (W⊓Z₁ : Subgroup G)≠4 := by
    intro hh
    have h₁ : W⊓Z₁=Z₁ := eq_of_le_of_card_ge inf_le_right (by rw [hh,hc₁])
    have h₂ : W⊓Z₂=Z₂ := eq_of_le_of_card_ge inf_le_right (by rw [←hcards,hh,hc₂])
    have hEW : E≤W := by
      rw [he]
      exact sup_le (h₁ ▸ (inf_le_left : W⊓Z₁≤W)) (h₂ ▸ (inf_le_left : W⊓Z₂≤W))
    have hh := card_le_of_le hEW
    rw [hcE,hcW] at hh
    omega
  have hc : Nat.card (W⊓Z₁ : Subgroup G)=2 := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show Nat.divisors 4={1,2,4} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  exact ⟨hc,hcards.symm.trans hc⟩

private theorem maximal_local_action_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    pCore 2 (internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) = ⊥ := by
  let V := localModule T N
  let f := actionHom N V (le_normalizer_conjugateSpanBy (centralInvolutions T) N)
  have hred := localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  let := hred.normal
  have hk : f.ker = centralizer (V.subgroupOf N : Set N) := by
    rw [show f.ker = (centralizer (_ : Set G)).subgroupOf N from actionHom_ker N _ _]
    ext n
    constructor
    · intro hn v hv
      exact Subtype.ext (hn v hv)
    · intro hn v hv
      exact congrArg N.subtype (hn ⟨v,localModule_le T hN.2 hv⟩ hv)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  change pCore 2 f.range = ⊥
  rw [←pCore_map_iso 2 e,hred.quotient_pCore_eq_bot,Subgroup.map_bot]

private theorem maximal_local_action_not_twoGroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N Mc : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : N ≠ Mc) :
    ¬ IsPGroup 2 (internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) := by
  let f := (actionHom N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).rangeRestrict
  intro hp
  have hcore := maximal_local_action_twoCore hG T hN
  have ht : (⊤ : Subgroup (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N))) ≤ pCore 2 _ :=
    le_sSup ⟨inferInstance,hp.of_injective (⊤ : Subgroup _).subtype (Subgroup.subtype_injective _)⟩
  have hi (x : N) : f x = 1 := ht.trans hcore.le (mem_top _)
  have hle : N ≤ Mc := by
    intro x hx
    have hh : (⟨x,hx⟩ : N) ∈ (actionHom N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).ker := congrArg Subtype.val (hi ⟨x,hx⟩)
    have hc : (⟨x,hx⟩ : N) ∈ (centralizer (localModule T N : Set G)).subgroupOf N :=
      (actionHom_ker N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) ▸ hh
    exact localModule_centralizer_le_partner T N hu hc
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  exact hne (le_antisymm hle (hN.1.2 hMc.1.1 hle))

private theorem maximal_local_action_sylow_ne_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N Mc : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : N ≠ Mc)
    (P : Sylow 2 (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N))) :
    (P : Subgroup (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N))) ≠ ⊥ := by
  let V := localModule T N
  let hn : N ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy (centralInvolutions T) N
  let D := internalActionImage N V hn
  let f : N →* D := (actionHom N V hn).rangeRestrict
  let Q := (T.subtype hN.2).mapSurjective
    (f := f) (actionHom N V hn).rangeRestrict_surjective
  intro hP
  have hQc : Nat.card Q = 1 := by
    have hcP : Nat.card P = 1 := by
      rw [hP,card_bot]
    exact Q.card_eq_multiplicity.trans (P.card_eq_multiplicity.symm.trans hcP)
  have hQ : (Q : Subgroup D) = ⊥ := card_eq_one.mp hQc
  have hTV : (T : Subgroup G) ≤ centralizer (V : Set G) := by
    intro t ht
    have hf : f ⟨t,hN.2 ht⟩ = 1 := by
      have hh : f ⟨t,hN.2 ht⟩ ∈ (Q : Subgroup D) :=
        mem_map_of_mem f ht
      rw [hQ] at hh
      exact hh
    have hk : (⟨t,hN.2 ht⟩ : N) ∈ (actionHom N V hn).ker :=
      congrArg Subtype.val hf
    rwa [actionHom_ker] at hk
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  let U := V.subgroupOf N
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf (localModule_le T hN.2)
  have hUT := (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal (T.subtype hN.2)
  have hVN : V ≤ N := localModule_le T hN.2
  have hVT : V ≤ (T : Subgroup G) := by
    have hh := map_mono (f := N.subtype) hUT
    change (V.subgroupOf N).map N.subtype ≤ _ at hh
    simpa only [map_subgroupOf_eq_of_le hVN,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hN.2] using hh
  have hVZ : V ≤ centralInvolutions T := by
    intro v hv
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hVT hv,elemPow_eq_one_of_isElementaryAbelian v hv,
      fun t ht => (hTV ht v hv).symm⟩
  have he : V = centralInvolutions T := le_antisymm hVZ (le_conjugateSpanBy _ _)
  have hCN : centralizer (centralInvolutions T : Set G) ≤ N := by
    rw [←he,(maximal_local_normalizer_from_source hG T hN).2]
    exact Subgroup.centralizer_le_normalizer _
  exact hne (Set.mem_singleton_iff.mp (hu ▸
    (show N ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      ⟨hN.1,hCN⟩)))


private theorem local_four_action_symmetricThree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N Mc : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : N ≠ Mc) (hc : Nat.card (localModule T N)=4) :
    Nonempty (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃* Equiv.Perm (Fin 3)) := by
  let W := localModule T N
  let hn : N≤normalizer (W : Set G) := le_normalizer_conjugateSpanBy (centralInvolutions T) N
  let D := internalActionImage N W hn
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  have hd : Module.finrank (ZMod 2) (Additive W)=2 := by
    have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at hp
    have hh : 2^(Module.finrank (ZMod 2) (Additive W))=2^2 := hp.symm.trans hc
    exact Nat.pow_right_injective (by decide : 1<2) hh
  let ρ := imageRepresentation N W hn
  let f := Representation.BinaryPlane.symmetricThreeHom ρ hd
  have hf := Representation.BinaryPlane.symmetricThreeHom_injective ρ
    (imageRepresentation_injective N W hn) hd
  have hdiv : Nat.card D ∣ 6 := by
    have hh := card_dvd_of_injective f hf
    simpa only [Nat.card_perm,Nat.card_fin,show Nat.factorial 3=6 from rfl] using hh
  let P : Sylow 2 D := Classical.choice inferInstance
  have hP := maximal_local_action_sylow_ne_bot hG T hN hu hne P
  obtain ⟨p,hp,hp1⟩ := P.bot_or_exists_ne_one.resolve_left hP
  have ht : 2 ∣ Nat.card D :=
    (P.isPGroup'.dvd_orderOf (show (⟨p,hp⟩ : (P : Subgroup D))≠1 from
      fun he => hp1 (congrArg Subtype.val he))).trans
      ((orderOf_dvd_natCard (⟨p,hp⟩ : (P : Subgroup D))).trans
        (card_subgroup_dvd_card (P : Subgroup D)))
  have hn2 := maximal_local_action_not_twoGroup hG T hN hu hne
  have hcard : Nat.card D=6 := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show Nat.divisors 6={1,2,3,6} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh | hh
    · omega
    · exact (hn2 (IsPGroup.of_card (n:=1) hh)).elim
    · omega
    · exact hh
  refine ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,?_⟩)⟩
  change Nat.card D=Nat.card (Equiv.Perm (Fin 3))
  rw [hcard,Nat.card_perm,Nat.card_fin]
  rfl

private theorem local_action_two_of_fourth_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hfour : ∀ g ∈ M⊓N, g^4 ∈ centralizer (localModule T N : Set G)) :
    IsPGroup 2 (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) := by
  let W := localModule T N
  let hn : N≤normalizer (W : Set G) := le_normalizer_conjugateSpanBy (centralInvolutions T) N
  let f : N →* internalActionImage N W hn := (actionHom N W hn).rangeRestrict
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  intro d
  refine ⟨2,?_⟩
  obtain ⟨n,rfl⟩ := (actionHom N W hn).rangeRestrict_surjective d
  obtain ⟨a,ha,b,hb,he⟩ := hord n n.property
  have hb1 : f ⟨b,hb.1⟩=1 := by
    apply Subtype.ext
    change actionHom N W hn ⟨b,hb.1⟩=1
    exact (show (⟨b,hb.1⟩ : N)∈(actionHom N W hn).ker from
      (actionHom_ker N W hn).symm ▸ hb.2)
  have he' : n=(⟨a,ha.1⟩ : N)*⟨b,hb.1⟩ := Subtype.ext he.symm
  change (f n)^4=1
  rw [he',map_mul,hb1,mul_one,←f.map_pow]
  apply Subtype.ext
  change actionHom N W hn ((⟨a,ha.1⟩ : N)^4)=1
  exact (show ((⟨a,ha.1⟩ : N)^4)∈(actionHom N W hn).ker from
    (actionHom_ker N W hn).symm ▸ hfour a ⟨ha.2,ha.1⟩)

private theorem eight_action_fourth
    (H E Z₁ Z₂ W : Subgroup G) [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 W]
    (he : E=Z₁⊔Z₂) (hd : Disjoint Z₁ Z₂)
    (hc₁ : Nat.card Z₁=4) (hc₂ : Nat.card Z₂=4)
    (hcE : Nat.card E=16) (hWE : W≤E) (hcW : Nat.card W=8)
    (hnW : H≤normalizer (W : Set G))
    (hp : ∀ g ∈ H,
      (Z₁.map (MulAut.conj g).toMonoidHom=Z₁ ∧ Z₂.map (MulAut.conj g).toMonoidHom=Z₂) ∨
      (Z₁.map (MulAut.conj g).toMonoidHom=Z₂ ∧ Z₂.map (MulAut.conj g).toMonoidHom=Z₁))
    (t : G) (ht : t∈H) (hext : Z₁.map (MulAut.conj t).toMonoidHom=Z₂) :
    ∀ g∈H, g^4 ∈ centralizer (W : Set G) := by
  let U₁ := W⊓Z₁
  let U₂ := W⊓Z₂
  let Q := U₁⊔U₂
  obtain ⟨h₁,h₂⟩ := eight_intersections E Z₁ Z₂ W he hd hc₁ hc₂ hcE hWE hcW
    t (hnW ht) hext
  have hperm : ∀ g∈H,
      (U₁.map (MulAut.conj g).toMonoidHom=U₁ ∧ U₂.map (MulAut.conj g).toMonoidHom=U₂) ∨
      (U₁.map (MulAut.conj g).toMonoidHom=U₂ ∧ U₂.map (MulAut.conj g).toMonoidHom=U₁) := by
    intro g hg
    have hw : W.map (MulAut.conj g).toMonoidHom=W := mem_normalizer_iff_map_conj_eq.mp (hnW hg)
    rcases hp g hg with hh | hh
    · exact Or.inl ⟨(Subgroup.map_inf W Z₁ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (congrArg₂ (·⊓·) hw hh.1),
        (Subgroup.map_inf W Z₂ (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).trans (congrArg₂ (·⊓·) hw hh.2)⟩
    · exact Or.inr ⟨(Subgroup.map_inf W Z₁ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (congrArg₂ (·⊓·) hw hh.1),
        (Subgroup.map_inf W Z₂ (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).trans (congrArg₂ (·⊓·) hw hh.2)⟩
  have hQW : Q≤W := sup_le inf_le_left inf_le_left
  have hcom : U₂≤centralizer (U₁ : Set G) := by
    intro u hu v hv
    exact congrArg Subtype.val (isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative W) ⟨v,hv.1⟩ ⟨u,hu.1⟩)
  have hcQ : Nat.card Q=4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U₁ U₂
      (hcom.trans (Subgroup.centralizer_le_normalizer _))
      (hd.mono inf_le_right inf_le_right),h₁,h₂]
  have hi : Q.relIndex W=2 := by
    have hh := relIndex_mul_card_of_le hQW
    rw [hcQ,hcW] at hh
    omega
  have hnQ : H≤normalizer (Q : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (U₁⊔U₂).map _=U₁⊔U₂
    rw [Subgroup.map_sup]
    rcases hperm g hg with hh | hh
    · exact congrArg₂ (·⊔·) hh.1 hh.2
    · exact (congrArg₂ (·⊔·) hh.1 hh.2).trans (sup_comm _ _)
  exact fourth_centralizes_of_index_two H W Q hQW hi hnW hnQ
    (square_centralizes_permuted_lines H U₁ U₂ h₁ h₂ hperm)

/-- The actual third-local module is its original intersection seed span. It is
either a four-group with its actual symmetric-three action, or the entire
original Thompson fixed group. -/
theorem PreparedChosenModule.decomposable_five_third_fixed_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      N ∈ maximalTwoLocalOvergroups (T : Subgroup G) → N ≠ M → N ≠ Mc →
      localModule T N = conjugateSpanBy (centralInvolutions T) (M⊓N) ∧
        ((Nat.card (localModule T N)=4 ∧
          Nonempty (internalActionImage N (localModule T N)
            (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃* Equiv.Perm (Fin 3))) ∨
         localModule T N=thompsonFixed T V) := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hN hNM hNMc
  obtain ⟨_,hnE,hWE⟩ := h.decomposable_five_third_local_control hG T hempty hM hmany hJ hu
    rfl c d hd s π hp hs hdec hq hfive hN hNM hNMc
  let E := thompsonFixed T (localModule T M)
  let W := localModule T N
  let H := M⊓N
  let Z₁ := thompsonPlane T (localModule T M) (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T (localModule T M) (c.ambientFactor d s.second).space
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWE
  have hnW : H≤normalizer (W : Set G) :=
    inf_le_right.trans (le_normalizer_conjugateSpanBy (centralInvolutions T) N)
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hspan : W=conjugateSpanBy (centralInvolutions T) H := by
    apply le_antisymm ?_ (conjugateSpanBy_mono le_rfl inf_le_right)
    apply (closure_le _).mpr
    rintro x ⟨n,hn,z,hz,rfl⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := hord n hn
    have hcz := mem_centralizer_iff.mp hb.2 z
      (le_conjugateSpanBy (centralInvolutions T) N hz)
    have he : (a*b)*z*(a*b)⁻¹=a*z*a⁻¹ := by
      calc
        _ = a*(b*z)*b⁻¹*a⁻¹ := by group
        _ = a*(z*b)*b⁻¹*a⁻¹ := by rw [hcz]
        _ = _ := by group
    rw [he]
    exact subset_closure ⟨a,⟨ha.2,ha.1⟩,z,hz,rfl⟩
  refine ⟨hspan,?_⟩
  have hex : ∃ t∈H, Z₁.map (MulAut.conj t).toMonoidHom=Z₂ := by
    let S₀ := (T : Subgroup G)⊓normalizer
      (plane (localModule T M) (c.ambientFactor d s.first).space : Set G)
    have hne : S₀≠(T : Subgroup G) := by
      intro he
      have hi := s.stabilizer_index
      change S₀.relIndex (T : Subgroup G)=2 at hi
      rw [he,relIndex_self] at hi
      omega
    obtain ⟨t,ht,htn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne
      (show S₀≤(T : Subgroup G) from inf_le_left) hne)
    exact ⟨t,⟨hM.1.2 ht,hN.2 ht⟩,(s.thompson_exchanges t ht
      (fun hh => htn ⟨ht,hh⟩)).1⟩
  obtain ⟨t,ht,hext⟩ := hex
  have hfirst : ∀ g∈H, Z₁.map (MulAut.conj g).toMonoidHom=Z₁ ∨
      Z₁.map (MulAut.conj g).toMonoidHom=Z₂ := by
    intro g hg
    let x : M := ⟨g,hg.1⟩
    have he : E.map (MulAut.conj g).toMonoidHom=E :=
      mem_normalizer_iff_map_conj_eq.mp (hnE hg)
    have hh : Z₁.map (MulAut.conj g).toMonoidHom =
        thompsonPlane T (localModule T M)
          (c.ambientFactor d (π ((actionHom M (localModule T M) h.normalized).rangeRestrict x)
            s.first)).space := by
      change ((plane _ _)⊓E).map _=(plane _ _)⊓E
      rw [map_inf _ _ _ (MulAut.conj g).injective,he,
        plane_conjugate h.normalized _ x]
      exact congrArg (fun P => plane (localModule T M) P ⊓ E)
        (hs ((actionHom M (localModule T M) h.normalized).rangeRestrict x) s.first)
    rcases s.covers (π ((actionHom M (localModule T M) h.normalized).rangeRestrict x)
      s.first) with hi | hi
    · exact Or.inl (hh.trans (congrArg (fun k => thompsonPlane T (localModule T M)
        (c.ambientFactor d k).space) hi))
    · exact Or.inr (hh.trans (congrArg (fun k => thompsonPlane T (localModule T M)
        (c.ambientFactor d k).space) hi))
  have hperm := pair_permutation_of_conjugate_orbit H Z₁ Z₂ hfirst t ht hext
  have hcE : Nat.card E=16 := s.fixed_card
  have hdiv : Nat.card W ∣ 16 := hcE ▸ card_dvd_of_le hWE
  have hWne : W≠⊥ := by
    intro he
    apply centralInvolutions_ne_bot_of_maximal_local T hN
    exact bot_unique ((le_conjugateSpanBy (centralInvolutions T) N).trans_eq he)
  have hnot2 : Nat.card W≠2 := by
    intro hc
    have hle : N≤Mc :=
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N).trans
        ((normalizer_le_centralizer_of_card_two W hc).trans
          (localModule_centralizer_le_partner T N hu))
    have hMc : Mc∈maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    exact hNMc (le_antisymm hle (hN.1.2 hMc.1.1 hle))
  have hnot8 : Nat.card W≠8 := by
    intro hc
    have hfour := eight_action_fourth H E Z₁ Z₂ W s.thompson_split
      (disjoint_iff.mpr s.thompson_disjoint) (s.thompson_card s.first)
      (s.thompson_card s.second) hcE hWE hc hnW hperm t ht hext
    exact maximal_local_action_not_twoGroup hG T hN hu hNMc
      (local_action_two_of_fourth_intersection hG T hempty hM hJ hN hfour)
  have hcases : Nat.card W=4 ∨ Nat.card W=16 := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show Nat.divisors 16={1,2,4,8,16} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    have hlow := W.one_lt_card_iff_ne_bot.mpr hWne
    omega
  rcases hcases with hc | hc
  · exact Or.inl ⟨hc,local_four_action_symmetricThree hG T hN hu hNMc hc⟩
  · exact Or.inr (eq_of_le_of_card_ge hWE (by rw [hc,hcE]))

end CFSG.Quasithin.Chapter15.Section01
