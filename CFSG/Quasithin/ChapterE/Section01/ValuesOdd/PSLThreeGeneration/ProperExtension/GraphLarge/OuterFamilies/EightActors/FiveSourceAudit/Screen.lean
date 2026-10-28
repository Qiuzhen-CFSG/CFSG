module
public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Sound necessary tests for the five-prime audit

The E1 branch is solvable, whereas the component in E2 makes that branch
nonsolvable. For an elementary actor of order eight, the respective rank-one
quotient tests require an intersection of order exactly four with the two-core,
or of order at least four with the solvable radical. These are intrinsic kernels.
E0 and the orders 64 and 192 imply Sylow containment, but do not identify two
subgroups of order 192. In particular they do not imply maximality.

The former diagnostic incorrectly identified the weak-closure normalizer with
an unrelated maximal subgroup of the same order. See `source/README.md` for the
corrected computation. No finite subgroup census is assumed or certified here.

Source: Aschbacher--Smith E.1.1--5, printed pp.209--210.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
variable {G : Type*} [Group G] [Finite G]

theorem oddCase_isSolvable {A K : Subgroup G} (h : ECaseOdd A K) :
    Group.IsSolvable K := by
  obtain ⟨p, hp, _, hq, _, _, _⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsNilpotent ((K ⧸ pCore 2 K) ⧸ pCore p (K ⧸ pCore 2 K)) := hq.isNilpotent
  let : Group.IsNilpotent (pCore p (K ⧸ pCore 2 K)) := pCore_isNilpotent
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
  have : Group.IsSolvable (K ⧸ pCore 2 K) :=
    (Group.isSolvable_iff_subgroup_quotient (pCore p (K ⧸ pCore 2 K))).mpr
      ⟨inferInstance, inferInstance⟩
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 K)).mpr
    ⟨inferInstance, inferInstance⟩

theorem componentCase_not_isSolvable {T A K : Subgroup G}
    (h : ECaseComponent T A K) : ¬ Group.IsSolvable K := by
  intro hs
  let := hs
  obtain ⟨_, _, _, L, hL, _⟩ := h
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have : Nontrivial L := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center L))
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem oddCase_kernel_card {A K : Subgroup G} [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (hA : Nat.card A = 8) (h : ECaseOdd A K) :
    Nat.card (A.subgroupOf K ⊓ pCore 2 K : Subgroup K) = 4 := by
  let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  have hc : Nat.card (A.subgroupOf K) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv).trans hA
  obtain ⟨p, _, _, _, _, _, hr⟩ := h
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
  have hk : 4 ≤ Nat.card (A.subgroupOf K ⊓ pCore 2 K : Subgroup K) :=
    (IsElementaryAbelian.rank_quotient_image_le_one_iff_of_card_eight _ _ hc).mp hr.le
  have hn : a ≠ ⊥ := by
    intro he
    change Group.rank a = 1 at hr
    rw [he, Group.rank_eq_zero] at hr
    omega
  let : Nontrivial a := (nontrivial_iff_ne_bot _).mpr hn
  have ha : 2 ≤ Nat.card a := Finite.one_lt_card
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map
    (A.subgroupOf K) (QuotientGroup.mk' (pCore 2 K))
  rw [QuotientGroup.ker_mk', hc] at hprod
  change Nat.card (A.subgroupOf K ⊓ pCore 2 K : Subgroup K) * Nat.card a = 8 at hprod
  nlinarith

theorem memberAt_one_screen {T A K : Subgroup G}
    (hA : Nat.card A = 8) (h : IsEMemberAt 1 T A K) :
    (Group.IsSolvable K ∧ Nat.card (A.subgroupOf K ⊓ pCore 2 K : Subgroup K) = 4) ∨
    (¬ Group.IsSolvable K ∧ 4 ≤ Nat.card
      (A.subgroupOf K ⊓ solvableRadical K : Subgroup K)) := by
  let := h.1.1
  have hAK := h.1.2.2.1
  rcases h.2 with ⟨ho, _⟩ | ⟨he, hr⟩
  · exact Or.inl ⟨oddCase_isSolvable ho, oddCase_kernel_card hAK hA ho⟩
  · let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
    have hc : Nat.card (A.subgroupOf K) = 8 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv).trans hA
    exact Or.inr ⟨componentCase_not_isSolvable he,
      (IsElementaryAbelian.rank_quotient_image_le_one_iff_of_card_eight _ _ hc).mp hr⟩

/-- The exact E0 intersection, together with order 192, forces containment
of an ambient Sylow of order 64. -/
theorem sylow_le_of_member_order {T : Sylow 2 G} {A K : Subgroup G}
    (h : IsEMember (T : Subgroup G) A K)
    (hT : Nat.card T = 64) (hK : Nat.card K = 192) :
    (T : Subgroup G) ≤ K := by
  obtain ⟨S, hS⟩ := h.2.2.2.2.1
  have hs : Nat.card S = 64 := by
    rw [S.card_eq_multiplicity, hK]
    rw [show (192 : ℕ) = 2 ^ 6 * 3 from by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two]
    norm_num [Nat.prime_three.factorization]
  have hc : Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) = 64 := by
    have he := card_map_of_injective (K := (T : Subgroup G).subgroupOf K)
      (f := K.subtype) K.subtype_injective
    rw [subgroupOf_map_subtype] at he
    rw [he, ← hS]
    exact hs
  have he : (T : Subgroup G) ⊓ K = (T : Subgroup G) :=
    eq_of_le_of_card_ge inf_le_left (by rw [hc, hT])
  exact inf_eq_left.mp he

/-- Every original actor is killed by the two-core of the weak-closure
normalizer. Thus that normalizer itself cannot satisfy the E1 rank condition. -/
theorem not_oddCase_weakNormalizer (T : Sylow 2 G) (Ω : Set (Subgroup G))
    {A : Subgroup G} (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G)) :
    ¬ ECaseOdd A (normalizer (weakClosure (T : Subgroup G) Ω : Set G)) := by
  let W := weakClosure (T : Subgroup G) Ω
  let M := normalizer (W : Set G)
  have hAW : A ≤ W := le_sSup ⟨hA, hAT⟩
  let : (W.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hW : IsPGroup 2 W := T.isPGroup'.to_le (weakClosure_le _ _)
  have hcore : W.subgroupOf M ≤ pCore 2 M :=
    le_sSup ⟨inferInstance, hW.comap_subtype⟩
  have ha : (A.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M)) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact (comap_mono hAW).trans hcore
  rintro ⟨p, _, _, _, _, _, hr⟩
  change Group.rank ((A.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 1 at hr
  rw [ha, Group.rank_eq_zero] at hr
  omega

/-- The corrected implication in the five-prime screen: a surviving E1
subgroup of the same order as the weak-closure normalizer escapes it. Equal
orders do not make the normalizer a member of the maximal subgroup class. -/
theorem oddCase_escapes_weakNormalizer_of_card_eq (T : Sylow 2 G)
    (Ω : Set (Subgroup G)) {A K : Subgroup G}
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G)) (hK : ECaseOdd A K)
    (hc : Nat.card K = Nat.card (normalizer (weakClosure (T : Subgroup G) Ω : Set G))) :
    ¬ K ≤ normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  intro hle
  have he := eq_of_le_of_card_ge hle hc.ge
  subst K
  exact not_oddCase_weakNormalizer T Ω hA hAT hK

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
