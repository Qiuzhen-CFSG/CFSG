module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationParity
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldCartan
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.SpecificGroups.PSL3Four.SylowStabilizerCoprime
public import Theory.GroupTheory.NormalizerQuotientInner
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# The Cartan in the odd-exponent preparation

Oddness removes the field action on L/O₂(L), so the actual left Cartan A
normalizes T. The earlier zero-core parity theorem and the unique maximal
two-local over H put A inside N_G(K), where K is the embedded O²(H).
Its order 2ⁿ−1 is prime to six. The literal action on K/O₂(K) preserves the
image of T∩K, so the PSL₃(4) Sylow-stabilizer calculation makes it trivial.

The quotient-action kernel on KT=H is O₂(H). Consequently [A,H] lies
inside O₂(H), and the abelian A has central image in HA/O₂(HA). This proves
the central-image clause of LinearParity.Seed before any module is chosen.
The residual maximality and nonfaithfulness premises are discharged in the
Chapter12 application. The remaining natural/TI and displacement arguments
stay with qt-d-1222-linear-field-parity.

Source: Aschbacher–Smith 5.1.17, printed pp.640–641 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- Odd degree and residual uniqueness place the entire Cartan in N_G(O²(H)). -/
theorem cartan_normalizes_residual_of_odd
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    A ≤ normalizer (residual H : Set G) := by
  have hn : (A ⊔ H).pCoreIn 2 ≠ ⊥ := fun hz =>
    (Nat.not_even_iff_odd.mpr hodd) (h.cartan_even_of_zero_core hH c hz)
  obtain ⟨M,hM,hAM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (A ⊔ H) (fun he => hn (by simp [Subgroup.pCoreIn, he]))
  have hu := (residual_geometry_of_maximal_nonfaithful h.qtke hH.1.1 hK hnf).2
  exact (hu M hM (le_sup_right.trans hAM)) ▸ le_sup_left.trans hAM

/-- With no nontrivial field action, the split Cartan preserves the ambient Sylow. -/
theorem cartan_normalizes_sylow_of_odd
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hodd : Odd n) : A ≤ normalizer (T : Set G) := by
  by_contra hn
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact (Nat.not_even_iff_odd.mpr hodd)
    (even_of_cartanFieldAction_ne_bot hTL e hF (c.fieldAction_ne_bot hTL e hn))

/-- The actual left Cartan has order prime to both two and three in odd degree. -/
theorem cartan_card_coprime_six_of_odd
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hodd : Odd n) : Nat.Coprime (Nat.card A) 6 := by
  have hcard := (c.left_cyclic_and_card hTL hpsl).2
  have ho : Odd (Nat.card A) := by
    have h := OddHall.odd_hall_odd c.left_hall
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at h
  have ht : Nat.Coprime 3 (Nat.card A) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    rw [hcard, Nat.BinaryTorusParity.three_dvd_sub_one_iff]
    exact Nat.not_even_iff_odd.mpr hodd
  exact (ho.coprime_two_right).mul_right ht.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
open scoped MatrixGroups Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- Preserve the literal quotient action when applying the Sylow-stabilizer model theorem. -/
theorem quotient_action_eq_one_of_normalizes_sylow
    (T : Sylow 2 G) (K A : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hAK : A ≤ normalizer (K : Set G))
    (hAT : A ≤ normalizer (T : Set G))
    (hcard : Nat.Coprime (Nat.card A) 6)
    (hpsl : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    ∀ a : A, normalizerQuotientAction K (pCore 2 K) (inclusion hAK a) = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hF, Matrix.PSL3Four.card_F])
  let eQ := e.trans (Atlas.fieldEquivPSL 3 eF)
  let q := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let R := P.mapSurjective hq
  let f : A →* MulAut Matrix.PSL3Four.PSL := (MulAut.congr eQ).toMonoidHom.comp
    ((normalizerQuotientAction K (pCore 2 K)).comp (inclusion hAK))
  have hequiv (a : A) (k : K) : f a (q k) =
      q (K.normalizerMonoidHom (inclusion hAK a) k) := by
    change eQ (normalizerQuotientAction K (pCore 2 K) (inclusion hAK a)
      (eQ.symm (eQ (QuotientGroup.mk' (pCore 2 K) k)))) = _
    rw [eQ.symm_apply_apply]
    simp only [normalizerQuotientAction, MonoidHom.comp_apply, quotientAut_apply_mk]
    rfl
  intro a
  have hpres : (R : Subgroup Matrix.PSL3Four.PSL).map (f a).toMonoidHom = R := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (f a).injective])
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hw
    change f a (q k) ∈ (R : Subgroup Matrix.PSL3Four.PSL)
    rw [hequiv]
    apply mem_map_of_mem
    rw [hP] at hk ⊢
    change (a : G) * (k : G) * (a : G)⁻¹ ∈ (T : Subgroup G)
    exact (mem_normalizer_iff.mp (hAT a.property) _).mp hk
  have hc : Nat.Coprime (orderOf (f a)) 6 := hcard.coprime_dvd_left
    ((orderOf_map_dvd f a).trans (orderOf_dvd_natCard a))
  have he := Matrix.PSL3Four.sylow_preserving_aut_eq_one_of_coprime R (f a) hpres hc
  apply (MulAut.congr eQ).injective
  exact he.trans (map_one (MulAut.congr eQ)).symm

open scoped commutatorElement IsMulCommutative

omit [Finite G] in
private theorem commutator_le_join_core
    (K S A : Subgroup G) (hSK : S ≤ normalizer (K : Set G))
    (hS : IsPGroup 2 S) (hAK : A ≤ normalizer (K : Set G))
    (hAS : A ≤ normalizer (S : Set G))
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (ha : ∀ a : A, normalizerQuotientAction K (pCore 2 K) (inclusion hAK a) = 1) :
    ⁅A, K ⊔ S⁆ ≤ (K ⊔ S).pCoreIn 2 := by
  let X := K ⊔ S
  have hAX : A ≤ normalizer (X : Set G) :=
    (le_inf hAK hAS).trans (normalizer_inf_normalizer_le_normalizer_sup K S)
  have hXK : X ≤ normalizer (K : Set G) := sup_le K.le_normalizer hSK
  apply commutator_le.mpr
  intro a haA x hx
  have hc : ⁅a, x⁆ ∈ X := (le_normalizer_iff_commutator_le_right.mp hAX)
    (commutator_mem_commutator haA hx)
  have hact : pCoreJoinAction 2 hSK ⟨⁅a,x⁆,hc⟩ = 1 := by
    let an : normalizer (K : Set G) := ⟨a,hAK haA⟩
    let xn : normalizer (K : Set G) := ⟨x,hXK hx⟩
    change normalizerQuotientAction K (pCore 2 K) ⁅an,xn⁆ = 1
    rw [map_commutatorElement, show normalizerQuotientAction K (pCore 2 K) an = 1 from
      ha ⟨a,haA⟩]
    simp
  have hmem : (⟨⁅a,x⁆,hc⟩ : X) ∈ pCore 2 X := by
    rw [← pCoreJoinAction_kernel 2 hSK hS hz]
    exact hact
  exact mem_map_of_mem X.subtype hmem

omit [Finite G] in
private theorem central_image_of_commutator_le_core
    (H A : Subgroup G) (hAH : A ≤ normalizer (H : Set G))
    (hab : IsMulCommutative A) (hc : ⁅A,H⁆ ≤ H.pCoreIn 2) :
    (A.subgroupOf (H ⊔ A)).map (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) := by
  let : IsMulCommutative A := hab
  let J := H ⊔ A
  let q := QuotientGroup.mk' (pCore 2 J)
  have hJH : J ≤ normalizer (H : Set G) := sup_le H.le_normalizer hAH
  have hcore : H.pCoreIn 2 ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      ((pCoreIn_le 2 H).trans le_sup_left)
      (hJH.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  let AH := (A.subgroupOf J).map q
  let HH := (H.subgroupOf J).map q
  have hcomm : HH ≤ centralizer (AH : Set (J ⧸ pCore 2 J)) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_iff_commutator_eq_one.mpr
    rintro _ ⟨a,ha,rfl⟩
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hm := hcore (hc (commutator_mem_commutator ha hx))
    obtain ⟨z,hz,he⟩ := hm
    exact (Subtype.ext he : z = ⁅a,x⁆) ▸ hz
  have hab' : AH ≤ centralizer (AH : Set (J ⧸ pCore 2 J)) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    rw [← map_mul, ← map_mul]
    apply congrArg q
    apply Subtype.ext
    exact congrArg (fun y : A => (y : G)) (mul_comm (⟨b,hb⟩ : A) ⟨a,ha⟩)
  have hgen : HH ⊔ AH = ⊤ := by
    rw [show HH ⊔ AH = ((H.subgroupOf J) ⊔ A.subgroupOf J).map q from
      (Subgroup.map_sup _ _ _).symm]
    have ht : H.subgroupOf J ⊔ A.subgroupOf J = ⊤ := by
      apply map_injective J.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show H ≤ J from le_sup_left),
        map_subgroupOf_eq_of_le (show A ≤ J from le_sup_right), ← MonoidHom.range_eq_map, range_subtype]
    rw [ht, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hall : (⊤ : Subgroup (J ⧸ pCore 2 J)) ≤ centralizer (AH : Set _) :=
    hgen ▸ sup_le hcomm hab'
  simpa only [coe_top, centralizer_univ] using (le_centralizer_iff.mp hall)


variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- In odd field degree the actual Cartan acts trivially on the exceptional residual quotient. -/
theorem cartan_residual_action_trivial_of_odd
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    A ≤ ((normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker).map
      (normalizer (residual H : Set G)).subtype := by
  have hAN := cartan_normalizes_residual_of_odd h hH c hodd hK hnf
  have hAT := cartan_normalizes_sylow_of_odd c h.sylow_normalizes h.linear hodd
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr (pCore 2 (pResidual 2 H)) (pCore 2 (residual H))
    e (pCore_map_iso 2 e)
  have hm := hlinear.of_mulEquiv q.symm
  have ha := quotient_action_eq_one_of_normalizes_sylow T (residual H) A
    (hH.1.1.2.trans (le_normalizer_residual H)) hAN hAT
    (cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd) hm
  intro a haA
  exact ⟨inclusion hAN ⟨a,haA⟩, ha ⟨a,haA⟩, rfl⟩

/-- The central Cartan image required by the literal parity seed is proved
before selecting its module, from the original residual quotient. -/
theorem cartan_image_central_of_odd
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    (A.subgroupOf (H ⊔ A)).map (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) := by
  have hAN := cartan_normalizes_residual_of_odd h hH c hodd hK hnf
  have hAT := cartan_normalizes_sylow_of_odd c h.sylow_normalizes h.linear hodd
  have heq := residual_sup_sylow T H hH.1.1.2
  have hAH : A ≤ normalizer (H : Set G) := by
    rw [← heq]
    exact (le_inf hAN hAT).trans
      (normalizer_inf_normalizer_le_normalizer_sup (residual H) (T : Subgroup G))
  have hact := cartan_residual_action_trivial_of_odd h hH c hodd hK hnf hlinear
  have ha : ∀ a : A, normalizerQuotientAction (residual H) (pCore 2 (residual H))
      (inclusion hAN a) = 1 := by
    intro a
    obtain ⟨x,hx,he⟩ := hact a.property
    have hxe : x = inclusion hAN a := Subtype.ext he
    exact hxe ▸ hx
  have hz : center ((residual H) ⧸ pCore 2 (residual H)) = ⊥ := by
    let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let q := QuotientGroup.congr (pCore 2 (pResidual 2 H)) (pCore 2 (residual H))
      e (pCore_map_iso 2 e)
    obtain ⟨F, _, _, _, ⟨f⟩⟩ := hlinear.of_mulEquiv q.symm
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    apply (center _).eq_bot_iff_forall.mpr
    intro x hx
    apply f.injective
    rw [map_one]
    have hh : f x ∈ center PSL(3,F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y,rfl⟩ := f.surjective y
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)
    simpa only [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F), mem_bot] using hh
  have hc : ⁅A,H⁆ ≤ H.pCoreIn 2 := by
    simpa only [heq] using commutator_le_join_core (residual H) (T : Subgroup G) A
      (hH.1.1.2.trans (le_normalizer_residual H)) T.isPGroup' hAN hAT hz ha
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  exact central_image_of_commutator_le_core H A hAH inferInstance hc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
