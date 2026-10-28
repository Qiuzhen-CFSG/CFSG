module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionCore
public import Theory.GroupTheory.SubgroupConjugation.PairPermutation
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The order-four partner module is diagonal

Source ordering and reducedness exclude a partner four-group meeting either
marked Thompson four-group. Its pointwise stabilizer permutes the two marked
summands and consequently has displacement inside this diagonal four-group.
This is the displacement bound for the actual partner-kernel two-core.
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

private theorem local_action_two_of_square_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hsquare : ∀ g ∈ M⊓N, g^2 ∈ centralizer (localModule T N : Set G)) :
    IsPGroup 2 (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) := by
  let W := localModule T N
  let hn : N≤normalizer (W : Set G) := le_normalizer_conjugateSpanBy (centralInvolutions T) N
  let f : N →* internalActionImage N W hn := (actionHom N W hn).rangeRestrict
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  intro d
  refine ⟨1,?_⟩
  obtain ⟨n,rfl⟩ := (actionHom N W hn).rangeRestrict_surjective d
  obtain ⟨a,ha,b,hb,he⟩ := hord n n.property
  have hb1 : f ⟨b,hb.1⟩=1 := by
    apply Subtype.ext
    change actionHom N W hn ⟨b,hb.1⟩=1
    exact (show (⟨b,hb.1⟩ : N)∈(actionHom N W hn).ker from
      (actionHom_ker N W hn).symm ▸ hb.2)
  have he' : n=(⟨a,ha.1⟩ : N)*⟨b,hb.1⟩ := Subtype.ext he.symm
  change (f n)^2=1
  rw [he',map_mul,hb1,mul_one,←f.map_pow]
  apply Subtype.ext
  change actionHom N W hn ((⟨a,ha.1⟩ : N)^2)=1
  exact (show ((⟨a,ha.1⟩ : N)^2)∈(actionHom N W hn).ker from
    (actionHom_ker N W hn).symm ▸ hsquare a ⟨ha.2,ha.1⟩)

private theorem four_intersection_square
    (H E Z₁ Z₂ W : Subgroup G) [IsElementaryAbelian 2 E]
    (he : E=Z₁⊔Z₂) (hd : Disjoint Z₁ Z₂)
    (hc₁ : Nat.card Z₁=4) (hc₂ : Nat.card Z₂=4)
    (hcE : Nat.card E=16) (hWE : W≤E) (hcW : Nat.card W=4)
    (hnW : H≤normalizer (W : Set G))
    (hp : ∀ g ∈ H,
      (Z₁.map (MulAut.conj g).toMonoidHom=Z₁ ∧ Z₂.map (MulAut.conj g).toMonoidHom=Z₂) ∨
      (Z₁.map (MulAut.conj g).toMonoidHom=Z₂ ∧ Z₂.map (MulAut.conj g).toMonoidHom=Z₁))
    (t : G) (ht : t∈H) (hext : Z₁.map (MulAut.conj t).toMonoidHom=Z₂)
    (hne : W⊓Z₁≠⊥) : ∀ g∈H, g^2∈centralizer (W : Set G) := by
  let U₁ := W⊓Z₁
  let U₂ := W⊓Z₂
  have hZ₁E : Z₁≤E := he ▸ le_sup_left
  have hZ₂E : Z₂≤E := he ▸ le_sup_right
  have hWmap : W.map (MulAut.conj t).toMonoidHom=W :=
    mem_normalizer_iff_map_conj_eq.mp (hnW ht)
  have hmap : U₁.map (MulAut.conj t).toMonoidHom=U₂ := by
    change (W⊓Z₁).map _=W⊓Z₂
    rw [map_inf _ _ _ (MulAut.conj t).injective,hWmap,hext]
  have hcards : Nat.card U₁=Nat.card U₂ := by
    rw [←hmap,card_map_of_injective (MulAut.conj t).injective]
  have hdiv : Nat.card U₁∣4 := hc₁ ▸ card_dvd_of_le (inf_le_right : U₁≤Z₁)
  have hlo : 1<Nat.card U₁ := U₁.one_lt_card_iff_ne_bot.mpr hne
  have hnot : Nat.card U₁≠4 := by
    intro hh
    have h₁ : U₁=Z₁ := eq_of_le_of_card_ge inf_le_right (by rw [hh,hc₁])
    have h₂ : U₂=Z₂ := eq_of_le_of_card_ge inf_le_right (by rw [←hcards,hh,hc₂])
    have hEW : E≤W := by
      rw [he]
      exact sup_le (h₁ ▸ (inf_le_left : U₁≤W)) (h₂ ▸ (inf_le_left : U₂≤W))
    have hh := card_le_of_le hEW
    rw [hcE,hcW] at hh
    omega
  have hcU₁ : Nat.card U₁=2 := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show Nat.divisors 4={1,2,4} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  have hcU₂ : Nat.card U₂=2 := hcards.symm.trans hcU₁
  have hcom : U₂≤centralizer (U₁ : Set G) := by
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm (⟨v,hWE hv.1⟩ : E) ⟨u,hWE hu.1⟩)
  have hgen : U₁⊔U₂=W := by
    apply eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U₁ U₂
      (hcom.trans (Subgroup.centralizer_le_normalizer _))
      (hd.mono inf_le_right inf_le_right),hcU₁,hcU₂,hcW]
  rw [←hgen]
  apply square_centralizes_permuted_lines H U₁ U₂ hcU₁ hcU₂
  intro g hg
  have hw : W.map (MulAut.conj g).toMonoidHom=W :=
    mem_normalizer_iff_map_conj_eq.mp (hnW hg)
  rcases hp g hg with hh | hh
  · exact Or.inl ⟨(Subgroup.map_inf W Z₁ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (congrArg₂ (·⊓·) hw hh.1),
      (Subgroup.map_inf W Z₂ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (congrArg₂ (·⊓·) hw hh.2)⟩
  · exact Or.inr ⟨(Subgroup.map_inf W Z₁ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (congrArg₂ (·⊓·) hw hh.1),
      (Subgroup.map_inf W Z₂ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (congrArg₂ (·⊓·) hw hh.2)⟩

private theorem local_four_diagonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T=∅)
    {M N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G)≤centralizer (localModule T M : Set G))
    (hN : N∈maximalTwoLocalOvergroups (T : Subgroup G))
    (E Z₁ Z₂ : Subgroup G) [IsElementaryAbelian 2 E]
    (he : E=Z₁⊔Z₂) (hd : Disjoint Z₁ Z₂)
    (hc₁ : Nat.card Z₁=4) (hc₂ : Nat.card Z₂=4)
    (hcE : Nat.card E=16) (hWE : localModule T N≤E) (hcW : Nat.card (localModule T N)=4)
    (hp : ∀ g∈M⊓N,
      (Z₁.map (MulAut.conj g).toMonoidHom=Z₁ ∧ Z₂.map (MulAut.conj g).toMonoidHom=Z₂) ∨
      (Z₁.map (MulAut.conj g).toMonoidHom=Z₂ ∧ Z₂.map (MulAut.conj g).toMonoidHom=Z₁))
    (t : G) (ht : t∈(T : Subgroup G)) (hext : Z₁.map (MulAut.conj t).toMonoidHom=Z₂) :
    Disjoint (localModule T N) Z₁ ∧ Disjoint (localModule T N) Z₂ ∧
      localModule T N⊔Z₁=E ∧ localModule T N⊔Z₂=E := by
  let W := localModule T N
  let hn : N≤normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have htH : t∈M⊓N := ⟨hM.1.2 ht,hN.2 ht⟩
  have hd₁ : Disjoint W Z₁ := by
    apply disjoint_iff.mpr
    by_contra hne
    have hsq := four_intersection_square (M⊓N) E Z₁ Z₂ W he hd hc₁ hc₂ hcE
      hWE hcW (inf_le_right.trans hn) hp t htH hext hne
    have htwo := local_action_two_of_square_intersection hG T hempty hM hJ hN hsq
    have hcore := maximal_local_action_twoCore hG T hN
    have htop : (⊤ : Subgroup (internalActionImage N W hn))≤pCore 2 _ :=
      le_sSup ⟨inferInstance,htwo.of_injective (⊤ : Subgroup _).subtype
        (Subgroup.subtype_injective _)⟩
    have hcentral : N≤centralizer (W : Set G) := by
      intro x hx
      have hi : (actionHom N W hn).rangeRestrict ⟨x,hx⟩=1 :=
        htop.trans hcore.le (mem_top _)
      have hh : (⟨x,hx⟩ : N)∈(actionHom N W hn).ker := congrArg Subtype.val hi
      have hh' : (⟨x,hx⟩ : N)∈(centralizer (W : Set G)).subgroupOf N :=
        (actionHom_ker N W hn) ▸ hh
      exact hh'
    apply hne
    apply bot_unique
    intro z hz
    have htz : t*z*t⁻¹=z := by rw [←hcentral (hN.2 ht) z hz.1,mul_inv_cancel_right]
    have hz₂ : z∈Z₂ := by
      rw [←htz]
      exact hext ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hz.2
    exact (disjoint_iff.mp hd).le ⟨hz.2,hz₂⟩
  have hmap : (W⊓Z₁).map (MulAut.conj t).toMonoidHom=W⊓Z₂ := by
    have hw : W.map (MulAut.conj t).toMonoidHom=W :=
      mem_normalizer_iff_map_conj_eq.mp (hn (hN.2 ht))
    rw [map_inf _ _ _ (MulAut.conj t).injective,hw,hext]
  have hd₂ : Disjoint W Z₂ := by
    apply disjoint_iff.mpr
    rw [←hmap,disjoint_iff.mp hd₁,Subgroup.map_bot]
  have hjoin (Z : Subgroup G) (hZE : Z≤E) (hcZ : Nat.card Z=4) (hdZ : Disjoint W Z) :
      W⊔Z=E := by
    have hcom : Z≤centralizer (W : Set G) := by
      intro z hz w hw
      exact congrArg Subtype.val (mul_comm (⟨w,hWE hw⟩ : E) ⟨z,hZE hz⟩)
    apply eq_of_le_of_card_ge (sup_le hWE hZE)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint W Z
      (hcom.trans (Subgroup.centralizer_le_normalizer _)) hdZ,hcW,hcZ,hcE]
  exact ⟨hd₁,hd₂,hjoin Z₁ (he ▸ le_sup_left) hc₁ hd₁,
    hjoin Z₂ (he ▸ le_sup_right) hc₂ hd₂⟩

omit [Finite G] in
private theorem diagonal_displacement
    {X : Type*} [CommGroup X] [IsElementaryAbelian 2 X]
    (A B U : Subgroup X) (hd : Disjoint A B)
    (hUA : U⊔A=⊤) (hUB : U⊔B=⊤)
    (α : MulAut X) (hfix : ∀u∈U, α u=u)
    (hperm : (A.map α.toMonoidHom=A ∧ B.map α.toMonoidHom=B) ∨
      (A.map α.toMonoidHom=B ∧ B.map α.toMonoidHom=A)) :
    ∀x:X, α x*x⁻¹∈U := by
  have hpow (x:X) : x*x=1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 X) x
  have hinv (x:X) : x⁻¹=x := (eq_inv_of_mul_eq_one_left (hpow x)).symm
  have hb (b:X) (hb:b∈B) : α b*b⁻¹∈U := by
    obtain ⟨u,hu,a,ha,hua⟩ := mem_sup.mp (show b∈U⊔A from hUA ▸ mem_top b)
    have hab : a*b=u := by
      rw [←hua]
      calc
        a*(u*a)=u*(a*a) := by ac_rfl
        _=u := by rw [hpow,mul_one]
    have hαab : α a*α b=a*b := by rw [←map_mul,hab,hfix u hu]
    rcases hperm with hp | hp
    · have hαa : α a∈A := hp.1 ▸ mem_map_of_mem α.toMonoidHom ha
      have hαb : α b∈B := hp.2 ▸ mem_map_of_mem α.toMonoidHom hb
      have he := mul_injective_of_disjoint hd
        (a₁:=(⟨α a,hαa⟩,⟨α b,hαb⟩)) (a₂:=(⟨a,ha⟩,⟨b,hb⟩)) hαab
      have he' : α b=b := congrArg (fun x : A×B => (x.2:X)) he
      rw [he',mul_inv_cancel]
      exact U.one_mem
    · have hαa : α a∈B := hp.1 ▸ mem_map_of_mem α.toMonoidHom ha
      have hαb : α b∈A := hp.2 ▸ mem_map_of_mem α.toMonoidHom hb
      have he := mul_injective_of_disjoint hd
        (a₁:=(⟨α b,hαb⟩,⟨α a,hαa⟩)) (a₂:=(⟨a,ha⟩,⟨b,hb⟩))
        ((mul_comm _ _).trans hαab)
      have he' : α b=a := congrArg (fun x : A×B => (x.1:X)) he
      rw [he',hinv,hab]
      exact hu
  intro x
  obtain ⟨u,hu,b,hb',rfl⟩ := mem_sup.mp (show x∈U⊔B from hUB ▸ mem_top x)
  have he : α (u*b)*(u*b)⁻¹=α b*b⁻¹ := by
    rw [map_mul,hfix u hu,mul_inv_rev]
    calc
      _=(u*u⁻¹)*(α b*b⁻¹) := by ac_rfl
      _=_ := by rw [mul_inv_cancel,one_mul]
  rw [he]
  exact hb b hb'

omit [Finite G] in
private theorem ambient_diagonal_displacement
    (E A B U : Subgroup G) [IsElementaryAbelian 2 E]
    (hAE : A≤E) (hBE : B≤E) (hUE : U≤E)
    (hd : Disjoint A B) (hUA : U⊔A=E) (hUB : U⊔B=E)
    (g : G) (hgn : g∈normalizer (E : Set G)) (hgc : g∈centralizer (U : Set G))
    (hp : (A.map (MulAut.conj g).toMonoidHom=A ∧ B.map (MulAut.conj g).toMonoidHom=B) ∨
      (A.map (MulAut.conj g).toMonoidHom=B ∧ B.map (MulAut.conj g).toMonoidHom=A)) :
    ∀x∈E, ⁅g,x⁆∈U := by
  let α : MulAut E := E.normalizerMonoidHom ⟨g,hgn⟩
  have hmap (X Y : Subgroup G) (hXE : X≤E)
      (hm : X.map (MulAut.conj g).toMonoidHom=Y) :
      (X.subgroupOf E).map α.toMonoidHom=Y.subgroupOf E := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      change g*(a:G)*g⁻¹∈Y
      exact hm ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom ha
    · intro hx
      change (x:G)∈Y at hx
      obtain ⟨a,ha,he⟩ := (hm.symm ▸ hx : (x:G)∈X.map (MulAut.conj g).toMonoidHom)
      exact ⟨⟨a,hXE ha⟩,ha,Subtype.ext he⟩
  have hd' : Disjoint (A.subgroupOf E) (B.subgroupOf E) := by
    apply disjoint_def.mpr
    intro x hx hy
    exact Subtype.ext (disjoint_def.mp hd hx hy)
  have hUA' : U.subgroupOf E⊔A.subgroupOf E=⊤ := by
    rw [←subgroupOf_sup hUE hAE,hUA,subgroupOf_self]
  have hUB' : U.subgroupOf E⊔B.subgroupOf E=⊤ := by
    rw [←subgroupOf_sup hUE hBE,hUB,subgroupOf_self]
  have hfix : ∀u∈U.subgroupOf E, α u=u := by
    intro u hu
    apply Subtype.ext
    change g*(u:G)*g⁻¹=(u:G)
    rw [←hgc u hu,mul_inv_cancel_right]
  have hp' : ((A.subgroupOf E).map α.toMonoidHom=A.subgroupOf E ∧
      (B.subgroupOf E).map α.toMonoidHom=B.subgroupOf E) ∨
      ((A.subgroupOf E).map α.toMonoidHom=B.subgroupOf E ∧
      (B.subgroupOf E).map α.toMonoidHom=A.subgroupOf E) := by
    rcases hp with hh | hh
    · exact Or.inl ⟨hmap A A hAE hh.1,hmap B B hBE hh.2⟩
    · exact Or.inr ⟨hmap A B hAE hh.1,hmap B A hBE hh.2⟩
  intro x hx
  exact diagonal_displacement (A.subgroupOf E) (B.subgroupOf E) (U.subgroupOf E)
    hd' hUA' hUB' α hfix hp' ⟨x,hx⟩

/-- When the actual partner module has order four, it is diagonal in the
original Thompson pair, and the partner-kernel two-core moves E only in it. -/
theorem PreparedChosenModule.decomposable_five_partner_four_diagonal_displacement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
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
      Nat.card (localModule T Mc)=4 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      Disjoint Uc Z₁ ∧ Disjoint Uc Z₂ ∧ Uc⊔Z₁=E ∧ Uc⊔Z₂=E ∧
        ⁅(centralizer (Uc : Set G)).pCoreIn 2,E⁆≤Uc := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcW
  let E := thompsonFixed T V
  let W := localModule T Mc
  let H := M⊓Mc
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_,hnE,hWE⟩ := h.decomposable_five_partner_control hG T hempty hM hmany hJ hu
    hfull c d hd s π hp hs hdec hq hfive
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMc : Mc∈maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hMcC.1,hTMc⟩
  have hex : ∃t∈(T : Subgroup G), Z₁.map (MulAut.conj t).toMonoidHom=Z₂ := by
    let S₀ := (T : Subgroup G)⊓normalizer (plane V (c.ambientFactor d s.first).space : Set G)
    have hne : S₀≠(T : Subgroup G) := by
      intro he
      have hi := s.stabilizer_index
      change S₀.relIndex (T : Subgroup G)=2 at hi
      rw [he,relIndex_self] at hi
      omega
    obtain ⟨t,ht,htn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne
      (show S₀≤(T : Subgroup G) from inf_le_left) hne)
    exact ⟨t,ht,(s.thompson_exchanges t ht (fun hh => htn ⟨ht,hh⟩)).1⟩
  obtain ⟨t,ht,hext⟩ := hex
  have hfirst : ∀g∈H, Z₁.map (MulAut.conj g).toMonoidHom=Z₁ ∨
      Z₁.map (MulAut.conj g).toMonoidHom=Z₂ := by
    intro g hg
    let x : M := ⟨g,hg.1⟩
    have he : E.map (MulAut.conj g).toMonoidHom=E :=
      mem_normalizer_iff_map_conj_eq.mp (hnE hg)
    have hh : Z₁.map (MulAut.conj g).toMonoidHom=
        thompsonPlane T V
          (c.ambientFactor d (π ((actionHom M V h.normalized).rangeRestrict x) s.first)).space := by
      change ((plane _ _)⊓E).map _=(plane _ _)⊓E
      rw [map_inf _ _ _ (MulAut.conj g).injective,he,plane_conjugate h.normalized _ x]
      exact congrArg (fun P => plane V P⊓E)
        (hs ((actionHom M V h.normalized).rangeRestrict x) s.first)
    rcases s.covers (π ((actionHom M V h.normalized).rangeRestrict x) s.first) with hi | hi
    · exact Or.inl (hh.trans (congrArg (fun k => thompsonPlane T V
        (c.ambientFactor d k).space) hi))
    · exact Or.inr (hh.trans (congrArg (fun k => thompsonPlane T V
        (c.ambientFactor d k).space) hi))
  have hperm := pair_permutation_of_conjugate_orbit H Z₁ Z₂ hfirst t ⟨hM.1.2 ht,hTMc ht⟩ hext
  obtain ⟨hd₁,hd₂,hjoin₁,hjoin₂⟩ := local_four_diagonal hG T hempty hM hJ hMc E Z₁ Z₂
    s.thompson_split (disjoint_iff.mpr s.thompson_disjoint) (s.thompson_card s.first)
    (s.thompson_card s.second) s.fixed_card hWE hcW hperm t ht hext
  refine ⟨hd₁,hd₂,hjoin₁,hjoin₂,?_⟩
  obtain ⟨_,_,hQT,hQN,_,_,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  apply commutator_le.mpr
  intro q hq e he
  exact ambient_diagonal_displacement E Z₁ Z₂ W inf_le_right inf_le_right hWE
    (disjoint_iff.mpr s.thompson_disjoint) hjoin₁ hjoin₂ q (hQN hq)
    (pCoreIn_le 2 _ hq) (hperm q ⟨hM.1.2 (hQT hq),hTMc (hQT hq)⟩) e he

end CFSG.Quasithin.Chapter15.Section01
