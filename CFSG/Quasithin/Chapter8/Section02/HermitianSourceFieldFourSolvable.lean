module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourParabolic
public import CFSG.Quasithin.ChapterE.Section02.SolvableStructure
public import Theory.GroupTheory.PResidual.TwoCoreOddDivisors
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.SpecificGroups.SL2.BinaryDihedral

/-!
# The solvable Hermitian parabolic sieve and residual lift

In E.2.1 the full residual of a solvable minimal parabolic modulo its
two-core is cyclic of order p, an elementary plane, or the prime
Heisenberg group. An odd divisor q of the original group survives in
that residual, so p = q. Prime rank at most one makes the residual cyclic;
all three source models have exponent p, forcing its order to be p.

For the selected Hermitian pair, I/O₂(I) supplies q = 3 or 5. The exact
embedding into H/O₂(H) and the proved odd-rank bounds place its full
residual in I⁺. Lifting through the two-core and retaining the original
conjugator proves O²(I) = O²(H), the set product H = IT, and normalization
of VA by the original Sylow group. No small-quotient inspection is assumed.

Source: Aschbacher–Smith E.2.1 and 8.2.9(1–2), printed pp.215,720–721,
refs/quasithin.pdf. The nonsolvable parabolic sieve remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE
variable {X : Type*} [Group X] [Finite X]

private theorem prime_eq_of_dvd_power {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : q ∣ p ^ k) : p = q :=
  ((Nat.dvd_prime hp).mp (hq.dvd_of_dvd_pow h) |>.resolve_left hq.ne_one).symm

/-- In the rank-one solvable source branch the full quotient residual has prime order. -/
theorem solvable_parabolic_residual_card {K : GroupClass} (hx : IsSQTK K X)
    (S : Sylow 2 X) (hS : IsMinimalParabolicOver S ⊤) (hsol : Group.IsSolvable X)
    (hout : ¬ (minimalParabolicMax S hS).pCoreIn 2 ≤ pCore 2 X)
    {q : ℕ} (hq : q.Prime) (ho : Odd q) (hdiv : q ∣ Nat.card X)
    (hrank : primeRank q X ≤ 1) :
    Nat.card (pResidual 2 (X ⧸ pCore 2 X)) = q := by
  obtain ⟨p,hp,hodd,hm⟩ := SolvableMinimalParabolic.source_models hx S hS hsol (Or.inl hout)
  have hd := odd_prime_dvd_twoCore_quotient_residual hq ho hdiv
  let R := pResidual 2 (X ⧸ pCore 2 X)
  have hpow : ∃ k : ℕ, Nat.card R = p ^ k := by
    rcases hm with ⟨hc,_⟩ | ⟨hc,_⟩ | ⟨hc,_,_⟩
    · exact ⟨1,by simpa only [pow_one] using hc⟩
    · exact ⟨2,hc⟩
    · exact ⟨3,hc⟩
  obtain ⟨k,hk⟩ := hpow
  have hpq : p = q := prime_eq_of_dvd_power hp hq (hk ▸ hd)
  subst p
  let : Fact q.Prime := ⟨hq⟩
  have hR : IsPGroup q R := IsPGroup.of_card hk
  have hr : primeRank q R ≤ 1 := (primeRank_subgroup_le q R).trans
    ((primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 X) pCore_isPGroup).trans hrank)
  let : IsCyclic R := hR.isCyclic_of_odd_of_elementary_card_le ho
    (fun E hE => by
      let := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E)
  have hexp : Monoid.exponent (Multiplicative (ZMod q)) = q := by
    rw [IsCyclic.exponent_eq_card]
    exact Nat.card_zmod q
  have he : Monoid.exponent R = q := by
    rcases hm with ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩ | ⟨_,_,⟨e⟩⟩
    · exact (Monoid.exponent_eq_of_mulEquiv e).trans hexp
    · rw [Monoid.exponent_eq_of_mulEquiv e,Monoid.exponent_prod,hexp,lcm_eq_nat_lcm,Nat.lcm_self]
    · rw [Monoid.exponent_eq_of_mulEquiv e,HeisenbergPrime.exponent]
      exact fun he => (by decide : ¬ Odd 2) (he ▸ ho)
  exact IsCyclic.exponent_eq_card.symm.trans he

open Representation.BinaryOffender
open Offenders.Parabolic.Construction
open scoped Pointwise MatrixGroups
variable {G : Type*} [Group G] [Finite G]

private theorem map_right_pair {A B : Type*} [Group A] [Group B]
    (f : A →* B) (W : Subgroup A) (x : A) :
    (W ⊔ W.map (MulAut.conj x⁻¹).toMonoidHom).map f =
      W.map f ⊔ (W.map f).map (MulAut.conj (f x)⁻¹).toMonoidHom := by
  rw [Subgroup.map_sup,map_map,map_map]
  congr 2
  ext y
  change f (x⁻¹ * y * (x⁻¹)⁻¹) = (f x)⁻¹ * f y * ((f x)⁻¹)⁻¹
  simp only [map_mul,map_inv]

/-- Lift the literal quotient containment on the same selected pair. -/
theorem selected_one_conclusions_of_quotient_cover
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hcover : pResidual 2 (H ⧸ pCore 2 H) ≤
      (I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
    (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (H : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((V ⊔
        (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G) := by
  have hIH := s.family.le_ambient
  have hVH : V ≤ H := (s.generate ▸ le_sup_left).trans hIH
  have hTH := hH.1.1.2
  let t := T.subtype hTH
  let v := V.subgroupOf H
  let j := I.subgroupOf H
  let x : H := ⟨i,hIH i.property⟩
  have htv : (t : Subgroup H) ≤ normalizer (v : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    exact comap_mono hTV
  have hgen : v ⊔ v.map (MulAut.conj x⁻¹).toMonoidHom = j := by
    apply map_injective H.subtype_injective
    rw [map_right_pair,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hIH]
    exact s.generate
  have hr0 := Normalizer.ParabolicReduction.residual_eq_of_quotient_cover t v j x htv hgen hcover
  have hr := congrArg (fun X : Subgroup H => X.map H.subtype) hr0
  rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hIH] at hr
  have hTR : (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) := by
    rw [hr]
    exact hTH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  have ha := Normalizer.offender_product_normalized I V
    (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) T i i.property s.generate
    hTV hTR (by simpa only [sup_comm] using (selected_one_core_product s).symm)
  refine ⟨hr,hTR,?_,ha.2⟩
  change (H : Set G) = (I : Set G) * ((T : Subgroup G) : Set G)
  rw [←coe_mul_of_right_le_normalizer_left I (T : Subgroup G) ha.1,
    selected_generates_hstar s hH]

/-- The solvable parabolic sieve and complete 8.2.9(1–2) on the original pair. -/
theorem selected_one_solvable_parabolic
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hsol : Group.IsSolvable H)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (h3 : primeRank 3 H ≤ 1) (h5 : primeRank 5 H ≤ 1)
    (hB : V ⊓ I.pCoreIn 2 ≤ H.pCoreIn 2)
    (himage : Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) :
    (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∨
      Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 5) ∧
    (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (H : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((V ⊔
        (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G) := by
  obtain ⟨t,ht,htP,htM⟩ := h28.minimal
  have hout : ¬ (minimalParabolicMax t htP).pCoreIn 2 ≤ pCore 2 H := by
    intro hc
    have hv : V.subgroupOf H ≤ pCore 2 H := by
      intro v hv
      obtain ⟨a,ha,he⟩ := h28.le_local_core hv
      apply hc
      rw [←htM]
      exact ⟨a,ha,Subtype.ext he⟩
    have hz : (V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = ⊥ :=
      (map_eq_bot_iff (f := QuotientGroup.mk' (pCore 2 H)) (V.subgroupOf H)).mpr
        (by simpa only [QuotientGroup.ker_mk'] using hv)
    rw [hz,card_bot] at himage
    omega
  obtain ⟨q,hq,ho,hqcases,hcard⟩ : ∃ q : ℕ, q.Prime ∧ Odd q ∧
      (q = 3 ∨ q = 5) ∧ Nat.card (I ⧸ pCore 2 I) = 2*q := by
    rcases hpair with hpair | hpair
    · obtain ⟨e⟩ := hpair
      refine ⟨3,by decide,by decide,Or.inl rfl,?_⟩
      rw [Nat.card_congr (e.trans
        Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm).toEquiv,
        DihedralGroup.nat_card]
    · obtain ⟨e⟩ := hpair
      refine ⟨5,by decide,by decide,Or.inr rfl,?_⟩
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have hdivI : q ∣ Nat.card I := (dvd_mul_left q 2).trans
    (hcard ▸ (pCore 2 I).index_dvd_card)
  have hdivH := hdivI.trans (card_dvd_of_le s.family.le_ambient)
  have hrank : primeRank q H ≤ 1 := by rcases hqcases with rfl | rfl <;> assumption
  have hc := solvable_parabolic_residual_card h28.sqtk t htP hsol hout hq ho hdivH hrank
  have hsmall : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∨
      Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 5 := by
    rcases hqcases with he | he
    · exact Or.inl (hc.trans he)
    · exact Or.inr (hc.trans he)
  obtain ⟨e,_⟩ := selected_one_pair_core_quotient s hB
  have hdivimage : q ∣ Nat.card ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) := by
    rw [←Nat.card_congr e.toEquiv,hcard]
    exact dvd_mul_left q 2
  have hcover := Normalizer.ParabolicReduction.quotient_cover_of_prime_residual
    (I.subgroupOf H) hq (fun he => (by decide : ¬ Odd 2) (he ▸ ho))
    (hc ▸ hq) hdivimage
  exact ⟨hsmall,selected_one_conclusions_of_quotient_cover s hH hTV hcover⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
