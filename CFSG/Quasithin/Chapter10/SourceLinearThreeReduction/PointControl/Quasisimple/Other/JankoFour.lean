module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.LocalOrders
public import Theory.SpecificGroups.Janko4.BinaryEightSection
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# The two remaining J₄ rank-one point rows

The native normal-elementary catalogue puts a Sylow-containing local pair
in max1 or gives a nonzero normalized elementary group of order at most eight.
The actual max1 and involution-centralizer orders are prime to 31. Orbit
counting in the small elementary alternative therefore excludes 31 from
every two-local containing a full Sylow. This excludes PSL₂(32) in the
original local quotient. The exponent-three obstruction excludes PSL₂(8).

Both applications use the literal central-quotient image of the original L.
They retain all module rows and fixed vectors and require no irreducibility
or later generation bound. Other.Source combines these two comparisons
with its degree sieve to close the entire complementary rank-one family.
Source: Aschbacher–Smith A.3.12(17) and 10.2.9, pp.47–48,750–751;
GLS3 Table 5.3i and the native J₄ word certificates in the imports.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other.JankoFour
open Janko4 Janko4.Cardinality Janko4.LocalStructure Janko4.OuterReduction.OddIndex
open ChapterA.Section03.SourceEmbeddings.FiveLocalFF
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four

private noncomputable def markedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem small_normal_elementary_prime_free
    {p : ℕ} [Fact p.Prime] (hp : 8 < p)
    (hc : ∀ z : Model, orderOf z = 2 → ¬ p ∣ Nat.card (centralizer ({z} : Set Model)))
    (H A : Subgroup Model) (hne : A ≠ ⊥) (he : IsElementaryAbelian 2 A)
    (hsmall : Nat.card A ≤ 8) (hn : H ≤ normalizer (A : Set Model)) :
    ¬ p ∣ Nat.card H := by
  let := he
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hd
  have hxval : orderOf (x : Model) = p := (orderOf_coe x).trans hx
  have hpow : IsPGroup p (zpowers (x : Model)) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using hxval)
  have hfix : A ⊓ centralizer (zpowers (x : Model) : Set Model) = ⊥ := by
    apply bot_unique
    intro z hz
    apply mem_bot.mpr
    by_contra hz1
    have hzord : orderOf z = 2 := orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian z hz.1,hz1⟩
    have hxC : (x : Model) ∈ centralizer ({z} : Set Model) :=
      mem_centralizer_singleton_iff.mpr (hz.2 x (mem_zpowers (x : Model)))
    have hxc : orderOf (⟨(x : Model),hxC⟩ : centralizer ({z} : Set Model)) = p :=
      (orderOf_coe _).symm.trans hxval
    exact hc z hzord (hxc ▸ orderOf_dvd_natCard
      (⟨(x : Model),hxC⟩ : centralizer ({z} : Set Model)))
  have hmod := card_modEq_card_inf_centralizer (zpowers (x : Model)) A hpow
    ((zpowers_le.mpr x.property).trans hn)
  rw [hfix,card_bot] at hmod
  have hcard : Nat.card A = 1 := by
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (by omega : Nat.card A < p),
      Nat.mod_eq_of_lt (by omega : 1 < p)] using hmod
  exact hne (A.eq_bot_of_card_eq hcard)

private theorem fixed_prime_free
    {p : ℕ} [Fact p.Prime] (hp : 8 < p) (hm : ¬ p ∣ Nat.card M)
    (hc : ∀ z : Model, orderOf z = 2 → ¬ p ∣ Nat.card (centralizer ({z} : Set Model)))
    (H E : Subgroup Model) (hSH : twoSubgroup ≤ H)
    (hES : E ≤ twoSubgroup) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hn : H ≤ normalizer (E : Set Model)) : ¬ p ∣ Nat.card H := by
  rcases ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour.fixed_pair_minimal_alternative
    H E hES hne he hSH hn with h | ⟨A,hA,_,heA,hcard,hHA⟩
  · exact fun hd => hm (hd.trans (card_dvd_of_le h))
  · exact small_normal_elementary_prime_free hp hc H A hA heA hcard hHA

/-- The literal normal-elementary catalogue excludes a prime absent from
max1 and the two involution centralizers, provided it exceeds eight. -/
theorem normalized_elementary_prime_free
    {p : ℕ} [Fact p.Prime] (hp : 8 < p) (hm : ¬ p ∣ Nat.card M)
    (hc : ∀ z : Model, orderOf z = 2 → ¬ p ∣ Nat.card (centralizer ({z} : Set Model)))
    (S : Sylow 2 Model) (H E : Subgroup Model) (hSH : (S : Subgroup Model) ≤ H)
    (hES : E ≤ (S : Subgroup Model)) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hn : H ≤ normalizer (E : Set Model)) : ¬ p ∣ Nat.card H := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S markedSylow
  let f := MulAut.conj g
  have hS : (S : Subgroup Model).map f.toMonoidHom = twoSubgroup :=
    congrArg Sylow.toSubgroup hg
  have hSH' := map_mono (f := f.toMonoidHom) hSH
  have hES' := map_mono (f := f.toMonoidHom) hES
  rw [hS] at hSH' hES'
  let := he
  have h := fixed_prime_free hp hm hc (H.map f.toMonoidHom) (E.map f.toMonoidHom)
    hSH' hES' (fun hz => hne ((map_eq_bot_iff_of_injective _ f.injective).mp hz))
    (IsElementaryAbelian.map f.toMonoidHom)
    ((map_mono (f := f.toMonoidHom) hn).trans (E.le_normalizer_map f.toMonoidHom))
  rwa [card_map_of_injective f.injective] at h

private theorem involution_centralizer_thirtyOne_free
    (z : Model) (hz : orderOf z = 2) :
    ¬ 31 ∣ Nat.card (centralizer ({z} : Set Model)) := by
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv,OuterReduction.OddIndex.modelCentralizer_card]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv,InvolutionCentralizers.Second.ambient_card]
    norm_num

/-- Every actual two-local containing a full Sylow of J₄ is prime to 31. -/
theorem twoLocal_thirtyOne_free (S : Sylow 2 Model) (H : Subgroup Model)
    (hl : IsTwoLocal H) (hSH : (S : Subgroup Model) ≤ H) : ¬ 31 ∣ Nat.card H := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  obtain ⟨J,hHJ,hJ⟩ := Finite.exists_le_maximal hl
  suffices ¬ 31 ∣ Nat.card J from fun hd => this (hd.trans (card_dvd_of_le hHJ))
  obtain ⟨N,hN,hnN,heN,hHN⟩ :=
    exists_normal_elementary_normalizer_of_sylow_le S hJ (hSH.trans hHJ)
  let E := N.map (S : Subgroup Model).subtype
  let := heN
  apply normalized_elementary_prime_free (p := 31) (by decide) ?_
    involution_centralizer_thirtyOne_free S J E (hSH.trans hHJ) (map_subtype_le N)
    (fun hz => hN ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz))
    (IsElementaryAbelian.map _) ?_
  · rw [max1Subgroup_card]
    norm_num
  · exact hHN.le
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other.JankoFour


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The literal local image has no quotient of order divisible by 31 in J₄. -/
theorem not_jankoFour_of_thirtyOne [Group.IsPerfect I]
    (h31 : 31 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Janko4.Model) : False :=
  quotient_not_dvd_of_twoLocal_orders D c e JankoFour.twoLocal_thirtyOne_free h31

/-- The native two-local order comparison excludes the original degree-five row. -/
theorem not_jankoFour_of_degree_five [Group.IsPerfect I]
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^5))
    (e : (I ⧸ center I) ≃* Janko4.Model) : False := by
  obtain ⟨F,_,_,hF,⟨d⟩⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply not_jankoFour_of_thirtyOne D c ?_ e
  rw [Nat.card_congr (d.trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm).toEquiv,
    GorensteinWalter.sl2_card_formula,hF]
  norm_num

/-- The actual central image retains its PSL₂(8) quotient, contradicting
exponent three for every three-subgroup of the native J₄ carrier. -/
theorem not_jankoFour_of_degree_three
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^3))
    (e : (I ⧸ center I) ≃* Janko4.Model) : False := by
  obtain ⟨F,_,_,hF,⟨d⟩⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  let a := ((markedCoreQuotientEquiv D c.strict.le e).symm.trans d).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  exact Janko4.no_binary_eight_quotient B (by simpa only [show 2^3=8 from rfl] using hF)
    (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
    (a.surjective.comp (QuotientGroup.mk'_surjective _))
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
