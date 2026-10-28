module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Completion
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.ReeComplete
public import Theory.Representation.SimpleCoreQuotientDegree
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv

/-!
# The remaining original quasisimple point configurations

After the rank-two comparisons, the binary containing carriers force an
original quotient order divisible by 168 and are excluded by the checked
binary-three argument. The remaining containing carriers are M₂₂, M₂₃,
HS, Held and Rudvalis: their two-ranks are at most six and their orders
are prime to 31.

The literal moved subgroup maps to a nonzero fully moved elementary
subgroup in the containing central quotient. A noncentral chief factor
therefore bounds the binary multiplicative order of every odd prime of
the original two-core quotient by six. A Suzuki quotient has a primitive
prime of binary order at least twelve. For an odd-prime PSL₂ quotient,
the bound leaves only primes 3, 5, 7 and 31; nonsolvability, the original
non-A₅ assumption, the checked binary-three comparison and the containing
orders respectively exclude them.

This closes the quasisimple branch without irreducibility of the whole
moved subgroup, and retains fixed layers, nonsplit sections and the
original moved-subgroup normalizer restriction. The literal source
consumer and both inspection contracts are assembled in `Complete`.
Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48,750--753.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02 ChapterA.Section03 BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
include D c

/-- The actual local image in either binary carrier has a binary-linear quotient of degree at least three. -/
theorem quotient_168_of_binary_containing
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hI : ClassicalGroup.IsPSL (I ⧸ center I) n 2) :
    168 ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hI
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let f := (eI.trans (Atlas.fieldEquivPSL n k)).trans (projectiveEquivLinear (by omega))
  let : Finite (LinearGroup n) := Finite.of_equiv (I ⧸ center I) f.toEquiv
  obtain ⟨S,_,hB,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let B := (L.subgroupOf I).map q
  let A := B.map f.toMonoidHom
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot_iff.mpr f.injective]
    infer_instance
  have hA := Chapter1.Section02.localCComponents_map_of_solvable_ker hB f.toMonoidHom
  obtain ⟨m,hm,hmn,⟨eA⟩⟩ := SourceEmbeddings.BinaryIntrinsic.local_twoCore_quotient n
    (by omega) (R.mapSurjective (f := f.toMonoidHom) f.surjective) A hA
  let d : (L ⧸ pCore 2 L) ≃* LinearGroup m :=
    (markedCoreQuotientEquiv D c.strict.le f).trans
      ((QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (map_map _ _ _).symm)
        (pCore_map_iso 2 _)).trans eA)
  let : NeZero m := ⟨by omega⟩
  have hc : Nat.card PSL(m, ZMod 2) = ∏ i : Fin m, (2 ^ m - 2 ^ i.val) := by
    have hh := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) m
    simpa only [Nat.card_zmod,show 2 - 1 = 1 from rfl,Nat.gcd_one_right,mul_one] using hh
  rw [Nat.card_congr (d.trans (projectiveEquivLinear (by omega)).symm).toEquiv,hc]
  have hm5 : m ≤ 5 := by omega
  interval_cases m <;> norm_num [Fin.prod_univ_succ]

/-- Binary containing carriers feed the completed 168-divisor exclusion. -/
theorem not_binary_containing
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hI : ClassicalGroup.IsPSL (I ⧸ center I) n 2) : False :=
  quasisimple_impossible_of_168 D c (quotient_168_of_binary_containing D c hn hI)
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
include D c

/-- An odd original quotient prime bounds the rank of the containing central quotient, using the actual moved subgroup. -/
theorem center_quotient_rank_of_prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    orderOf (2 : ZMod p) ≤ primeRank 2 (I ⧸ center I) := by
  obtain ⟨_,_,_,_,_,_,_,hE,hEB,hne,hm⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let e := markedCoreQuotientEquiv D c.strict.le (MulEquiv.refl _)
  let := Selection.ModuleChoice.component_quotient_simple D
    (fun hn => c.t_not_normalizes (hn c.t_mem))
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.symm.isSimpleGroup
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (markedLocalHom_surjective c.strict.le (MulEquiv.refl _))
  let := hE
  let U := E.subgroupOf B
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr hm.le)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hEB
  have hu : U ≠ ⊥ := by
    intro hz
    have hh := congrArg (map B.subtype) hz
    rw [map_subgroupOf_eq_of_le hEB,Subgroup.map_bot] at hh
    exact hne hh
  have hmU : ⁅U,(⊤ : Subgroup B)⁆ = U := by
    apply map_injective B.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hEB,←MonoidHom.range_eq_map,range_subtype]
    exact hm
  have hl := Representation.SimpleCoreQuotient.moved_elementary_prime_card U hu hmU hp hp2
    (Nat.card_congr e.toEquiv ▸ hd)
  rw [Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv] at hl
  have hu := (primeRank_le_iff_elementary_card_le (I ⧸ center I)).mp le_rfl E hE
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hl.trans hu)

/-- All containing carriers outside these five sporadic models are excluded. -/
theorem remaining_five_sporadic :
    ∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier) := by
  rcases Other.remaining_binary_or_sporadic D c (RankTwo.not_rank_two D c) with
    ⟨n,hn,hI⟩ | ⟨name,hname,⟨e⟩⟩
  · exact (Other.not_binary_containing D c hn hI).elim
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.m22,by simp,⟨e⟩⟩
    · exact ⟨.m23,by simp,⟨e⟩⟩
    · exact (Other.not_mathieuTwentyFour_of_fully_moved D c e).elim
    · exact (Other.not_jankoFour_of_fully_moved D c e).elim
    · exact ⟨.hs,by simp,⟨e⟩⟩
    · exact ⟨.he,by simp,⟨e⟩⟩
    · exact ⟨.ru,by simp,⟨e⟩⟩

/-- The remaining literal containing quotient has two-rank at most six. -/
theorem center_quotient_rank_le_six : primeRank 2 (I ⧸ center I) ≤ 6 := by
  obtain ⟨name,hname,⟨e⟩⟩ := remaining_five_sporadic D c
  let : Finite name.Carrier := Finite.of_equiv (I ⧸ center I) e.toEquiv
  rcases hname with rfl | rfl | rfl | rfl | rfl <;> rw [primeRank_equiv 2 e]
  · exact Sporadic.Mathieu.m22_twoRank_le_four.trans (by decide)
  · exact Sporadic.Mathieu.m23_twoRank_le_four.trans (by decide)
  · exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
  · exact Held.primeRank_two_le_six
  · exact Rudvalis.primeRank_le_six

/-- The actual local quotient order divides the containing quotient order, which is prime to 31. -/
theorem quotient_not_thirtyOne : ¬ 31 ∣ Nat.card (L ⧸ pCore 2 L) := by
  have hd := (card_quotient_dvd_card
    (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))))).trans
      ((L.subgroupOf I).map (QuotientGroup.mk' (center I))).card_subgroup_dvd_card
  have hc := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le (MulEquiv.refl _)).toEquiv
  have hLI : Nat.card (L ⧸ pCore 2 L) ∣ Nat.card (I ⧸ center I) := hc.symm ▸ hd
  intro h31
  have hi := h31.trans hLI
  obtain ⟨name,hname,⟨e⟩⟩ := remaining_five_sporadic D c
  rcases hname with rfl | rfl | rfl | rfl | rfl <;> rw [Nat.card_congr e.toEquiv] at hi
  · change 31 ∣ Nat.card Sporadic.Mathieu.M22 at hi
    rw [Sporadic.Mathieu.m22_order] at hi
    norm_num at hi
  · change 31 ∣ Nat.card Sporadic.Mathieu.M23 at hi
    rw [Sporadic.Mathieu.m23_order] at hi
    norm_num at hi
  · exact (by decide : ¬ 31 ∣ 2^9*3^2*5^3*7*11)
      (hi.trans Sporadic.LeechRelated.HS.card_carrier_dvd)
  · have hg := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
    have hh := Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hg
      (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hg)
    exact (by decide : ¬ 31 ∣ 2^12*(3^3*5^2*7^3*17)) (hi.trans hh)
  · change 31 ∣ Nat.card Rudvalis.Model at hi
    rw [Rudvalis.model_card] at hi
    norm_num at hi

/-- The primitive Suzuki prime exceeds the available binary rank. -/
theorem quasisimple_impossible_of_suzuki
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  obtain ⟨p,hp,horder⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul_odd
    (n := 2*m+1) ⟨m,rfl⟩ (by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [show (2 : ZMod 2) = 0 by decide,orderOf_zero] at horder
    omega
  have hd : p ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv]
    exact Representation.Suzuki.prime_dvd_card_of_orderOf_two hm hp horder
  have hl := center_quotient_rank_of_prime D c hp hp2 hd
  rw [horder] at hl
  have hu := center_quotient_rank_le_six D c
  omega
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
private theorem small_binary_order_primes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : orderOf (2 : ZMod p) ≤ 6) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have h := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hpos := (isUnit_iff_ne_zero.mpr htwo).isOfFinOrder.orderOf_pos
  let k := orderOf (2 : ZMod p)
  have hk : 0 < k := hpos
  have hk6 : k ≤ 6 := hord
  have hpow : 2 ≤ 2 ^ k := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk
  have hd : p ∣ 2 ^ k - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    simp only [Nat.cast_sub (by omega : 1 ≤ 2 ^ k),Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_one,k,pow_orderOf_eq_one,sub_self]
  by_contra! hn
  have h3 : ¬ p ∣ 3 := by simpa [Nat.dvd_prime (by decide : Nat.Prime 3),hp.ne_one] using hn.1
  have h5 : ¬ p ∣ 5 := by simpa [Nat.dvd_prime (by decide : Nat.Prime 5),hp.ne_one] using hn.2.1
  have h7 : ¬ p ∣ 7 := by simpa [Nat.dvd_prime (by decide : Nat.Prime 7),hp.ne_one] using hn.2.2.1
  have h31 : ¬ p ∣ 31 := by simpa [Nat.dvd_prime (by decide : Nat.Prime 31),hp.ne_one] using hn.2.2.2
  have h15 : ¬ p ∣ 15 := hp.not_dvd_mul h3 h5
  have h63 : ¬ p ∣ 63 := hp.not_dvd_mul h3 (hp.not_dvd_mul h3 h7)
  interval_cases k <;> norm_num only [Nat.reducePow,Nat.reduceSub] at hd <;>
    simp only [h3,h7,h31,h15,h63,Nat.dvd_one,hp.ne_one] at hd

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
include D c

/-- All odd-prime PSL₂ original quotients are excluded, retaining the original non-A₅ premise. -/
theorem quasisimple_impossible_of_prime_quotient
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p)
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hL
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.t_not_normalizes (h c.t_mem)
  let := Selection.ModuleChoice.component_quotient_simple D hn
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect (L ⧸ pCore 2 L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hns : ¬ Group.IsSolvable PSL(2,F) := by
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable (L ⧸ pCore 2 L)
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hp3 : 3 < p := hF ▸
    Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF.symm ▸ ho) hns
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card (L ⧸ pCore 2 L) = p * (p^2-1)/2 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨p,1,hp,ho,by decide,by simpa using hF⟩,hF]
  have hpdiv : p ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [hcard]
    have hpar : p^2 % 2 = 1 := by norm_num [Nat.pow_mod,Nat.odd_iff.mp ho]
    have hsq : 1 ≤ p^2 := one_le_pow₀ (by omega)
    have he : 2 ∣ p^2-1 := by omega
    apply Nat.dvd_div_of_mul_dvd
    rw [mul_comm 2 p]
    exact Nat.mul_dvd_mul_left p he
  have hord := (center_quotient_rank_of_prime D c hp hp2 hpdiv).trans
    (center_quotient_rank_le_six D c)
  rcases small_binary_order_primes hp hp2 hord with h3 | h5 | h7 | h31
  · omega
  · cases h5
    let := Fintype.ofFinite F
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let a : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    exact hna ⟨(e.trans (Atlas.fieldEquivPSL 2 a)).trans
      Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩
  · cases h7
    exact quasisimple_impossible_of_prime_seven_quotient D c
      ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
  · exact quotient_not_thirtyOne D c (h31 ▸ hpdiv)

/-- The full non-A₅ quasisimple point configuration is impossible with every original module row retained. -/
theorem quasisimple_impossible
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) : False := by
  rcases original_quotient_suzuki_or_prime D c hna with ⟨m,hm,⟨e⟩⟩ | ⟨p,hp,ho,_,hL⟩
  · exact quasisimple_impossible_of_suzuki D c hm e
  · exact quasisimple_impossible_of_prime_quotient D c hp ho hL hna
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
