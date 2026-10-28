module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Intersection
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActions
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# The binary component intersection and reducibility

For the actual SL₃(2) branch, X/O₂(X) has order 168 and hence 3-rank one.
The cubic-intersection theorem then gives m₃(K ∩ X) = 1. When S normalizes
X, the subgroup O₂(K)(K ∩ X) is S-invariant and is strictly between O₂(K)
and K, whose 3-rank is two. This proves the reducibility premise needed by
15.2.21(1). The final theorem applies this to the original moved-orbit
wreath reduction, retaining its exact quotient and action premises.

The binary orbit geometry, marked factors and final 15.2.22 application
remain with the linear-three branch assembly. No claim about excluding
all L₃(2)-blocks is made here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
15.2.23, printed p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

private theorem binary_component_rank_le_one
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F) : primeRank 3 X ≤ 1 := by
  obtain ⟨e⟩ := b.ms.1.model
  let := Fintype.ofFinite F
  have hc : Nat.card F = 2 := by simpa using b.field_card
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 X) pCore_isPGroup,
    primeRank_congr 3 (e.trans (Atlas.fieldEquivSL 3 ef))]
  apply primeRank_le_one_of_square_not_dvd
  rw [Matrix.PSL3Two.card_SL]
  decide

include d in
/-- The original K ∩ X has 3-rank exactly one in the binary branch. -/
theorem Branch.binary_intersection_rank_one
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    primeRank 3 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G) = 1 := by
  have hu := (primeRank_mono 3 (show (pResidual 2 H).map H.subtype ⊓ X ≤ X from inf_le_right)).trans
    (binary_component_rank_le_one b)
  have hd := b.residual_component_intersection_three_dvd d hI
  have hz : primeRank 3 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G) ≠ 0 :=
    fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd
  omega

include d in
/-- An S-invariant binary component gives a proper invariant subgroup of K/O₂(K). -/
theorem Branch.binary_reducible_of_normalized
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I)
    (hSX : planeSylow T ZS ≤ normalizer (X : Set G)) :
    ¬ IsSmallActionIrreducible (planeSylow T ZS) ((pResidual 2 H).map H.subtype) := by
  intro hirr
  let K := (pResidual 2 H).map H.subtype
  let A := K ⊓ X
  let L := K.pCoreIn 2 ⊔ A
  have hSK : planeSylow T ZS ≤ normalizer (K : Set G) := hirr.1
  have hSA : planeSylow T ZS ≤ normalizer (A : Set G) :=
    (le_inf hSK hSX).trans inf_normalizer_le_normalizer_inf
  have hSQ : planeSylow T ZS ≤ normalizer (K.pCoreIn 2 : Set G) := hSK.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hSL : planeSylow T ZS ≤ normalizer (L : Set G) :=
    (le_inf hSQ hSA).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rcases hirr.2 L le_sup_left (sup_le (pCoreIn_le 2 K) inf_le_left) hSL with he | he
  · have hp : IsPGroup 2 A := (isPGroup_pCoreIn 2 K).to_le (le_sup_right.trans he.le)
    obtain ⟨r,hr⟩ := hp.exists_card_eq
    have hd := b.residual_component_intersection_three_dvd d hI
    change 3 ∣ Nat.card A at hd
    rw [hr] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  · let B := A.subgroupOf K
    let q := QuotientGroup.mk' (pCore 2 K)
    have hgen : pCore 2 K ⊔ B = ⊤ := by
      apply map_injective K.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show A ≤ K from inf_le_left),
        ← MonoidHom.range_eq_map,range_subtype]
      exact he
    have hm : B.map q = ⊤ := by
      have hh := congrArg (map q) hgen
      have hq : (pCore 2 K).map q = ⊥ :=
        (Subgroup.map_eq_bot_iff (pCore 2 K)).mpr (by rw [QuotientGroup.ker_mk'])
      have hsur : q.range = ⊤ :=
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (pCore 2 K))
      simpa only [Subgroup.map_sup,hq,bot_sup_eq,← MonoidHom.range_eq_map,hsur] using hh
    have hr := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3)
      q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) B
    rw [hm,primeRank_congr 3 topEquiv,
      primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup,
      primeRank_congr 3 (subgroupOfEquivOfLe (show A ≤ K from inf_le_left))] at hr
    have hrK : primeRank 3 K = 2 := residual_rank_two d
    have hrA : primeRank 3 A = 1 := b.binary_intersection_rank_one d hI
    omega

include d in
/-- Apply the actual wreath-quotient orbit reduction to obtain the 15.2.21(1) reducibility premise. -/
theorem Branch.binary_reducible_of_wreath
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃* BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤) :
    ¬ IsSmallActionIrreducible (planeSylow T ZS) ((pResidual 2 H).map H.subtype) := by
  apply b.binary_reducible_of_normalized d hI
  exact ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right).trans
    (b.normal_of_wreath d hI hmove f hfull)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
