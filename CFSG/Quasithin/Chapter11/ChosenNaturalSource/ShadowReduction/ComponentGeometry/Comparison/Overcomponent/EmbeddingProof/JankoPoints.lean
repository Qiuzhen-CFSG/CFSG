module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.PointAlternatives
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SporadicNestedQuotients
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction

/-!
# The nonquasisimple point comparison in J₄

A nonquasisimple intrinsic two-core quotient has a characteristic eleven-core
of order divisible by 121 and has order prime to seven. If the point image
has nontrivial two-core, the actual Sylow-normalized elementary subgroup
places it in the Mathieu local or an involution centralizer; their orders
exclude 121. If its two-core is trivial, the full Sylow two-subgroup acts
faithfully on its eleven-core and hence on its Frattini quotient. That
quotient has dimension at most three over F₁₁, whose linear automorphism
group is too small in its two-part.

The comparison is transported through the literal containing quotient and
point image. It removes J₄ from PointAlternatives and proves the quintic
elementary-plane proper pair for the actual chosen flag. It uses no
maximal-Sylow-overgroup classification or normalized-module alternative.
The remaining quasisimple comparisons and equality assembly belong to
qt-d-1222-shadow-component-comparison; the authorized earlier geometry
retains its discharge by qt-d-1222-shadow-components.

Source: Aschbacher--Smith 11.4.2, printed p.776, using A.3.6 and A.3.12.
The imported J₄ carrier and local certificates retain their original
ATLAS attribution and license; no carrier data is copied here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
namespace JankoPoint
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel

private theorem square_prime {p : ℕ} (hp : p.Prime) (hl : 3 < p)
    (hd : p ^ 2 ∣ 86775571046077562880) : p = 11 := by
  have hpd := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  have he : 86775571046077562880 = 2^21*3^3*5*7*11^3*23*29*31*37*43 := by norm_num
  rw [he] at hpd
  simp only [hp.dvd_mul, or_assoc] at hpd
  rcases hpd with h | h | h | h | h | h | h | h | h | h
  · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h; omega
  · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three h; omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h
    subst p; norm_num at hd
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h
    subst p; norm_num at hd
  · exact Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 11) h
  all_goals
    have he := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
    subst p
    norm_num at hd

private theorem large_prime_core
    {A : Type*} [Group A] [Finite A]
    (hsq : IsSQTK KnownSimple.IsKnownSimple A) (hO : pCore 2 A = ⊥)
    {C : Subgroup A} (hC : C.IsCComponent) (hn : ¬ IsQuasisimple C) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p^2 ∣ Nat.card (pCore p C) := by
  have hf : ¬ fittingSubgroup C ≤ center C := by
    intro hf
    apply hn
    have hr : solvableRadical C = center C := by
      apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
      exact le_solvableRadical (center C) inferInstance
        (Group.isSolvable_of_comm (fun a b => Subtype.ext
          (mem_center_iff.mp a.property b).symm))
    let := hC.perfect
    let := hC.isSimpleGroup_quotient_solvableRadical
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
  obtain ⟨p,hp,ho,hnc⟩ := NoncentralFitting.exists_noncentral_odd_core hC hO hf
  let : Fact p.Prime := ⟨hp⟩
  have hne : pCore p C ≠ ⊥ := fun he => hnc (he ▸ bot_le)
  have hpd : p ∣ Nat.card (pCore p C) :=
    (pCore_isPGroup (p := p) (G := C)).card_eq_or_dvd.resolve_left
      (fun he => hne ((pCore p C).eq_bot_iff_card.mpr he))
  have hpf : p ∣ Nat.card (fittingSubgroup C) :=
    hpd.trans (card_dvd_of_le (pCore_le_fitting C p))
  obtain ⟨hs,_⟩ := NoncentralFitting.structure_of_noncentral hsq hO hC hf
  have hl : 3 < p := by
    rcases hs with ⟨he,q,hq,hq3,F,_,_,hF,v,_⟩ | hs
    · rw [←he,Nat.card_congr v.toEquiv] at hpf
      change p ∣ Nat.card (Fin 2 → F) at hpf
      rw [Nat.card_fun,Nat.card_fin,hF] at hpf
      exact (Nat.prime_eq_prime_of_dvd_pow hp hq hpf).symm ▸ hq3
    · have hpf' : p ∣ Nat.card (generalizedFitting C) := hs.1.symm ▸ hpf
      have hc := (hs.2.2.2 p hp hpf').1
      have ht := hp.two_le
      rcases hc with (hc | hc) | hc <;> omega
  refine ⟨p,hp,hl,?_⟩
  by_contra hsquare
  have hrc : primeRank p (pCore p C) ≤ 1 := primeRank_le_one_of_square_not_dvd hsquare
  let : IsCyclic (pCore p C) := pCore_isPGroup.isCyclic_of_odd_of_elementary_card_le ho
    (fun B hB => by
      let : IsElementaryAbelian p B := hB
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hrc B)
  let := hC.perfect
  have hc : (⊤ : Subgroup C) ≤ centralizer (pCore p C : Set C) := by
    simpa only [Group.IsPerfect.commutator_eq_top] using
      commutator_le_centralizer_of_isCyclic_normal (pCore p C)
  apply hnc
  intro x hx
  exact mem_center_iff.mpr (fun y => (hc (mem_top y) x hx).symm)

/-- The nonquasisimple core-free section has an actual characteristic
11-core of order divisible by 121, and its order is prime to seven. -/
private theorem eleven_core_of_nonquasisimple
    {A : Type*} [Group A] [Finite A]
    (hsq : IsSQTK KnownSimple.IsKnownSimple A) (hO : pCore 2 A = ⊥)
    (hC : (⊤ : Subgroup A).IsCComponent) (hn : ¬ IsQuasisimple A)
    (hd : Nat.card A ∣ 86775571046077562880) :
    11^2 ∣ Nat.card (pCore 11 A) ∧ ¬ 7 ∣ Nat.card A := by
  obtain ⟨p,hp,hl,hs⟩ := large_prime_core hsq hO hC
    (fun h => hn (h.of_mulEquiv topEquiv))
  have he : p = 11 := square_prime hp hl (hs.trans
    ((pCore p (⊤ : Subgroup A)).card_subgroup_dvd_card.trans
      (by simpa only [Nat.card_congr (topEquiv (G := A)).toEquiv] using hd)))
  subst p
  have hc : Nat.card (pCore 11 (⊤ : Subgroup A)) = Nat.card (pCore 11 A) := by
    rw [←pCore_map_iso 11 (topEquiv (G := A)),card_map_of_injective topEquiv.injective]
  refine ⟨hc ▸ hs,?_⟩
  intro h7
  apply hn
  exact (SporadicNested.quasisimple_of_sporadic_order hsq hO hC
    (by simpa only [Nat.card_congr (topEquiv (G := A)).toEquiv] using h7)
    (.inr (by simpa only [Nat.card_congr (topEquiv (G := A)).toEquiv] using hd))).of_mulEquiv topEquiv

private theorem centralizer_not_eleven_square (z : Janko4.Model) (hz : orderOf z = 2) :
    ¬ 11^2 ∣ Nat.card (centralizer ({z} : Set Janko4.Model)) := by
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    change ¬11^2 ∣ Nat.card (centralizer ({Janko4.a} : Set Janko4.Model))
    rw [Janko4.OuterReduction.OddIndex.modelCentralizer_card]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv,Janko4.InvolutionCentralizers.Second.ambient_card]
    norm_num

private theorem seven_free_small_action
    {B U : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (h7 : ¬7 ∣ Nat.card B) (hu : Nat.card U ≤ 8) (a : B →* MulAut U) : a = 1 := by
  have hdiv : Nat.card (MulAut U) ∣ 168 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
    have hn3 : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (by simpa only [hn] using hu)
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow U n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  let : Group.IsSolvable a.range := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hd
    have hpd := hd.trans (a.range.card_subgroup_dvd_card.trans hdiv)
    have hf : 168 = 2^3*3*7 := by norm_num
    rw [hf] at hpd
    simp only [hp.dvd_mul,or_assoc] at hpd
    rcases hpd with h | h | h
    · exact .inl (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h)
    · exact .inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h
      subst p
      exact (h7 (hd.trans (card_range_dvd a))).elim
  let : Group.IsPerfect a.range := Group.IsPerfect.ofSurjective a.rangeRestrict_surjective
  have hz : Subsingleton a.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable a.range inferInstance
  ext b : 1
  exact congrArg Subtype.val (hz.elim (a.rangeRestrict b) 1)

private noncomputable def markedSylow : Sylow 2 Janko4.Model :=
  Janko4.OuterReduction.OddIndex.twoSubgroup_isPGroup.toSylow (by
    rw [Janko4.OuterReduction.OddIndex.twoSubgroup,index_map_subtype,
      Janko4.OuterReduction.OddIndex.localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

/-- A nontrivial two-core cannot occur in a perfect, seven-free local
section whose order has two factors eleven. -/
private theorem no_core_case (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (hc : pCore 2 B ≠ ⊥) (h11 : 11^2 ∣ Nat.card B) (h7 : ¬7 ∣ Nat.card B) : False := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Janko4.Model S markedSylow
  let f := MulAut.conj g
  let C := B.map f.toMonoidHom
  have hS : (S : Subgroup Janko4.Model).map f.toMonoidHom =
      Janko4.OuterReduction.OddIndex.twoSubgroup := congrArg Sylow.toSubgroup hg
  have hSC : Janko4.OuterReduction.OddIndex.twoSubgroup ≤ normalizer (C : Set Janko4.Model) := by
    rw [←hS]
    exact (map_mono hn).trans (B.le_normalizer_map f.toMonoidHom)
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]; infer_instance
  have hC : C ∈ localCComponents markedSylow := by
    have h := localCComponents_map_of_solvable_ker hB f.toMonoidHom
    rw [hS] at h
    exact h
  have hcC : pCore 2 C ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := (f.subgroupMap B).toMonoidHom) _ (f.subgroupMap B).injective).mp
    rw [pCore_map_iso 2 (f.subgroupMap B)]
    exact hz
  have hC11 : 11^2 ∣ Nat.card C := by rwa [card_map_of_injective f.injective]
  have hC7 : ¬7 ∣ Nat.card C := by rwa [card_map_of_injective f.injective]
  obtain ⟨N,hN,hCN,hSN⟩ := FiveLocalFF.SolvableQuotients.exists_maximal_two_local
    markedSylow C hSC hcC
  obtain ⟨R,hR,_,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le markedSylow hN hSN
  let E := R.map (markedSylow : Subgroup Janko4.Model).subtype
  have he : IsElementaryAbelian 2 E := by let := heR; exact IsElementaryAbelian.map _
  have hne : E ≠ ⊥ := fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  rcases FiveLocalFF.JankoFour.fixed_pair_minimal_alternative
      (C ⊔ Janko4.OuterReduction.OddIndex.twoSubgroup) E
      (map_subtype_le R) hne he le_sup_right
      (sup_le (hNR ▸ hCN) (hNR ▸ hSN)) with hmax | ⟨U,hU,_,heU,hcard,hCU⟩
  · have hd := hC11.trans (card_dvd_of_le (le_sup_left.trans hmax))
    rw [Janko4.Cardinality.max1Subgroup_card] at hd
    norm_num at hd
  · let := heU
    let := FiveLocalFF.SolvableQuotients.local_perfect hC
    have hCU' := le_sup_left.trans hCU
    let a := U.normalizerMonoidHom.comp (inclusion hCU')
    have ha := seven_free_small_action hC7 hcard a
    have hcent : C ≤ centralizer (U : Set Janko4.Model) := by
      intro b hb
      have hk : inclusion hCU' ⟨b,hb⟩ ∈ U.normalizerMonoidHom.ker := by
        change a ⟨b,hb⟩ = 1
        rw [ha]; rfl
      rwa [normalizerMonoidHom_ker] at hk
    obtain ⟨u,hu,hune⟩ := U.bot_or_exists_ne_one.resolve_left hU
    have hu2 : orderOf u = 2 := orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian u hu,hune⟩
    have hCUz : C ≤ centralizer ({u} : Set Janko4.Model) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (hcent hb u hu).symm
    exact centralizer_not_eleven_square u hu2 (hC11.trans (card_dvd_of_le hCUz))

private theorem eleven_elementary_aut_card
    (A : Type*) [Group A] [Finite A] [IsElementaryAbelian 11 A]
    (n : ℕ) (hn : Nat.card A = 11^n) :
    Nat.card (MulAut A) = ∏ i : Fin n, (11^n - 11^i.val) := by
  classical
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hpow : 11 ^ Module.finrank (ZMod 11) (Additive A) = 11^n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 11) (V := Additive A)
    change Nat.card A = _ at hc
    simpa only [Nat.card_zmod,hn] using hc.symm
  have hdim := Nat.pow_right_injective (by decide : 1 < 11) hpow
  let a : MulAut A ≃* (Additive A ≃ₗ[ZMod 11] Additive A) :=
    { toFun := fun f => { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := by intro f; ext; rfl
      right_inv := by intro f; ext; rfl
      map_mul' := by intro f g; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod 11) (Additive A) hdim
  let e := a.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 11) (Additive A)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)
  rw [Nat.card_congr e.toEquiv,Matrix.card_GL_field]
  simp only [ZMod.card]

private theorem no_large_two_action
    {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]
    (ha : IsPGroup 11 A) (hc : Nat.card A ≤ 11^3)
    (hp : IsPGroup 2 P) (hP : 64 ∣ Nat.card P)
    (a : P →* MulAut A) (hi : Function.Injective a) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let : Fact (IsPGroup 11 A) := ⟨ha⟩
  let : IsElementaryAbelian 11 (A ⧸ frattini A) :=
    isElementaryAbelian_quotient_frattini (p := 11)
  have hcop : Nat.Coprime (Nat.card P) 11 := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 2 11).pow_left k
  have hd := card_dvd_of_injective _ (MonoidHom.injective_frattini_action_of_coprime ha a hi hcop)
  have hdiv := hP.trans hd
  obtain ⟨n,hn⟩ := (ha.to_quotient (frattini A)).exists_card_eq
  have hn3 : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 11)).mp (by
    rw [←hn]
    exact (Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (frattini A))).trans hc)
  rw [eleven_elementary_aut_card _ n hn] at hdiv
  interval_cases n <;> norm_num [Fin.prod_univ_succ] at hdiv

/-- No subgroup of order at least 11² in the eleven-Sylow is normalized
by the full Sylow two-subgroup of the actual J₄ carrier. -/
private theorem no_normalized_eleven_core (S : Sylow 2 Janko4.Model)
    (R : Subgroup Janko4.Model) (hR : IsPGroup 11 R)
    (h11 : 11^2 ∣ Nat.card R)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (R : Set Janko4.Model)) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hcent : (S : Subgroup Janko4.Model) ⊓ centralizer (R : Set Janko4.Model) = ⊥ := by
    apply AlternatingFive.sylow_centralizer_eq_bot_of_no_involution S R
    intro z hzR hz
    have hRz : R ≤ centralizer ({z} : Set Janko4.Model) := by
      intro r hr
      exact mem_centralizer_singleton_iff.mpr (hzR r hr)
    exact centralizer_not_eleven_square z hz (h11.trans (card_dvd_of_le hRz))
  let a := R.normalizerMonoidHom.comp (inclusion hn)
  have hi : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hcent]
    refine ⟨x.property,?_⟩
    change inclusion hn x ∈ R.normalizerMonoidHom.ker at hx
    rwa [normalizerMonoidHom_ker] at hx
  have hRcard : Nat.card R ≤ 11^3 := by
    obtain ⟨k,hk⟩ := hR.exists_card_eq
    have hd := R.card_subgroup_dvd_card
    rw [hk,Janko4.Cardinality.model_card] at hd
    have hk3 : k ≤ 3 := by
      by_contra! hh
      have he : 11^4 ∣ 86775571046077562880 :=
        (pow_dvd_pow 11 hh).trans hd
      norm_num at he
    rw [hk]
    exact Nat.pow_le_pow_right (by decide) hk3
  have hSc : 64 ∣ Nat.card S := by
    rw [Nat.card_congr (S.equiv markedSylow).toEquiv]
    change 64 ∣ Nat.card Janko4.OuterReduction.OddIndex.twoSubgroup
    rw [Janko4.OuterReduction.OddIndex.twoSubgroup_card]
    norm_num
  exact no_large_two_action hR hRcard S.isPGroup' hSc a hi

/-- Every full-Sylow-normalized local C-component of the literal J₄
carrier has quasisimple intrinsic two-core quotient. -/
theorem local_quotient_quasisimple
    (hsq : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model)) :
    IsQuasisimple (B ⧸ pCore 2 B) := by
  by_contra hnot
  have htop : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using hB.subgroupOf_of_le le_rfl le_sup_left
  let Q := B ⧸ pCore 2 B
  let : Group.IsNilpotent (pCore 2 B) := pCore_isNilpotent
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 B)
  have hsqQ := ChapterE.Structure.sqtk_two_quotient (hsq.subgroup B) (pCore 2 B) pCore_isPGroup
  obtain ⟨h11,h7⟩ := eleven_core_of_nonquasisimple hsqQ
    (pCore_quotient_pCore_eq_bot 2) hbar hnot (by
      have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
      rwa [Janko4.Cardinality.model_card] at hd)
  have h11B : 11^2 ∣ Nat.card B :=
    h11.trans ((pCore 11 Q).card_subgroup_dvd_card.trans (card_quotient_dvd_card (pCore 2 B)))
  have h7B : ¬7 ∣ Nat.card B := by
    intro hd
    rw [←(pCore 2 B).card_mul_index,index_eq_card] at hd
    rcases (by decide : Nat.Prime 7).dvd_mul.mp hd with hd | hd
    · obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
      rw [hk] at hd
      have he := Nat.prime_eq_prime_of_dvd_pow (by decide : Nat.Prime 7) Nat.prime_two hd
      omega
    · exact h7 hd
  by_cases hc : pCore 2 B = ⊥
  · let e : Q ≃* B := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    have h11core : 11^2 ∣ Nat.card (pCore 11 B) := by
      rw [←pCore_map_iso 11 e,card_map_of_injective e.injective]
      exact h11
    let R := (pCore 11 B).map B.subtype
    exact no_normalized_eleven_core S R (pCore_isPGroup.map B.subtype)
      (by rwa [card_map_of_injective B.subtype_injective])
      (hn.trans (normalizer_le_normalizer_characteristic_image B (pCore 11 B)))
  · exact no_core_case S B hB hn hc h11B h7B

end JankoPoint

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    {E : Closure.Geometry D}

/-- The J₄ comparison on the literal containing quotient. Both the original
point image and its intrinsic two-core are retained. -/
theorem point_quasisimple_in_jankoFour
    (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    (e : (J ⧸ pCore 2 J) ≃* Janko4.Model) :
    IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz) := by
  have hl := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup E.input.source.simpleQTKE T hl
  have hs : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left))).mp
      (hsq.subgroup (J.subgroupOf (J ⊔ (T : Subgroup G))))
  have hq := ChapterE.Structure.sqtk_two_quotient hs (pCore 2 J) pCore_isPGroup
  obtain ⟨P,C,hC,_,hPC,⟨a⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt e
  let := JankoPoint.local_quotient_quasisimple (hq.knownSimple_of_equiv e) P C hC hPC
  exact IsQuasisimple.of_mulEquiv a.symm

/-- Exhausting the original containing catalogue, a nonquasisimple point
quotient has precisely the quintic elementary-plane proper embedding.
The exceptional J₄ alternative has been discharged on its actual carrier. -/
theorem ofFlag_nonquasisimple_proper_pair
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      Chapter1.Section02.LocalModels.HasExtension
        ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
        (Chapter1.Section02.LocalModels.ElementaryModel 5 2) (fun Q _ => Source.IsSL Q 2 5) ∧
      (ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 5 ∨ Source.IsSL (J ⧸ pCore 2 J) 3 5) ∧
      ProperEmbedding (ofFlag S f X z H).Kz J := by
  obtain ⟨hd,hpair | hj⟩ := ofFlag_nonquasisimple_proper_pair_or_jankoFour
    S f X z H h hne hn hlinear h1132 e hcent hJ hlt
  · exact ⟨hd,hpair⟩
  · exact (hn (point_quasisimple_in_jankoFour h hJ.1 hlt hj.some)).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
