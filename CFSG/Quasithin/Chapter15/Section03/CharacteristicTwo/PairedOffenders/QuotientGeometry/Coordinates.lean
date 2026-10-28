module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Cases
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Sylow.RegularModel
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The block kernel and the actual Sylow quotient

The parabolic preserves the partition of eight points into two four-point
blocks. The four double swaps in `coreWords` give the product of the regular
Klein-four actions on these blocks. Their sixteen distinct words form an
elementary abelian subgroup of the canonical Sylow two-subgroup. Conjugation
by each of the seven Sylow generators preserves this group, so its restriction
to the Sylow subgroup is normal. The resulting quotient has order eight. The even part has order four,
is elementary abelian, and is normal in this quotient.

All finite permutation identities below are checked by the Lean kernel.
The `Dihedral` and `RegularEven` extensions identify the quotient and prove
the four offender positions. The identification with the parabolic two-core
is a separate proof obligation; it is not inferred just from the kernel order.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.25, calculations (I)–(IV), printed pp.1133–1134 (PDF pp.1150–1151).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

def sameHalf (x y : Fin 8) : Prop := x.val / 4 = y.val / 4

def parabolic : Subgroup Perm where
  carrier := {g | ∀ x y, sameHalf (g x) (g y) ↔ sameHalf x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    simpa using (hg (g⁻¹ x) (g⁻¹ y)).symm

def coreWords : Fin 16 → Perm :=
  cubeWords (kleinFirst 8 (by decide)) (kleinSecond 8 (by decide))
    (pairSwap 8 2 * pairSwap 8 3) secondBlockSwap

def blockCore : Subgroup Perm where
  carrier := Set.range coreWords
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have h : ∀ i j, ∃ k, coreWords i * coreWords j = coreWords k := by decide +kernel
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have h : ∀ i, (coreWords i)⁻¹ = coreWords i := by decide +kernel
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (h i).symm⟩

theorem card_blockCore : Nat.card blockCore = 16 := by
  change Nat.card (Set.range coreWords) = 16
  rw [← Nat.card_congr (Equiv.ofInjective coreWords (by decide +kernel))]
  simp

instance : IsElementaryAbelian 2 blockCore := by
  have hc : ∀ i j, coreWords i * coreWords j = coreWords j * coreWords i := by decide +kernel
  have hs : ∀ i, coreWords i ^ 2 = 1 := by decide +kernel
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact Subtype.ext (hc i j)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    rintro ⟨_, i, rfl⟩
    exact Subtype.ext (hs i)

theorem blockCore_le_sylow : blockCore ≤ canonicalSylow := by
  have h0 : kleinFirst 8 (by decide) ∈ canonicalSylow :=
    canonicalSylow.mul_mem (sylowGenerators_mem 0) (sylowGenerators_mem 1)
  have h1 := sylowGenerators_mem 4
  have h2 := canonicalSylow.mul_mem (sylowGenerators_mem 2) (sylowGenerators_mem 3)
  have h3 := sylowGenerators_mem 5
  rintro _ ⟨i, rfl⟩
  unfold coreWords cubeWords
  repeat' apply Subgroup.mul_mem
  all_goals split_ifs
  all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact Subgroup.one_mem _

theorem sylow_le_parabolic : (canonicalSylow : Subgroup Perm) ≤ parabolic := by
  have h : ∀ i x y, sameHalf (sylowGenerators i x) (sylowGenerators i y) ↔ sameHalf x y := by
    unfold sameHalf
    decide +kernel
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact h i

theorem sylow_le_normalizer_blockCore :
    (canonicalSylow : Subgroup Perm) ≤ Subgroup.normalizer (blockCore : Set Perm) := by
  have hc : ∀ i j, ∃ k,
      sylowGenerators i * coreWords j * (sylowGenerators i)⁻¹ = coreWords k := by
    decide +kernel
  have hi : ∀ i, (sylowGenerators i)⁻¹ = sylowGenerators i := by decide +kernel
  have hf (i : Fin 7) (x : Perm) (hx : x ∈ blockCore) :
      sylowGenerators i * x * (sylowGenerators i)⁻¹ ∈ blockCore := by
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  refine ⟨hf i x, fun hx => ?_⟩
  have hh := hf i _ hx
  have hs : sylowGenerators i * sylowGenerators i = 1 := by
    nth_rw 1 [← hi i]
    exact inv_mul_cancel _
  have he : sylowGenerators i * (sylowGenerators i * x * (sylowGenerators i)⁻¹) *
      (sylowGenerators i)⁻¹ = x := by
    rw [hi i]
    calc
      _ = (sylowGenerators i * sylowGenerators i) * x *
        (sylowGenerators i * sylowGenerators i) := by group
      _ = x := by rw [hs]; simp
  rwa [he] at hh

abbrev SylowGroup := canonicalSylow
abbrev sylowCore : Subgroup SylowGroup := blockCore.subgroupOf canonicalSylow

instance : sylowCore.Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer blockCore_le_sylow).mpr
    sylow_le_normalizer_blockCore

abbrev Quotient := SylowGroup ⧸ sylowCore
def quotientMap : SylowGroup →* Quotient := QuotientGroup.mk' sylowCore

theorem card_sylowCore : Nat.card sylowCore = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe blockCore_le_sylow).toEquiv]
  exact card_blockCore

theorem card_quotient : Nat.card Quotient = 8 := by
  have h := sylowCore.card_mul_index
  change Nat.card sylowCore * Nat.card Quotient = Nat.card SylowGroup at h
  rw [card_sylowCore] at h
  have hs : Nat.card SylowGroup = 128 := card_canonicalTwoSubgroup
  omega

def evenSylow : Subgroup SylowGroup := (alternatingGroup (Fin 8)).subgroupOf canonicalSylow
def evenFour : Subgroup Quotient := evenSylow.map quotientMap


theorem blockCore_le_alternating : blockCore ≤ alternatingGroup (Fin 8) := by
  have h : ∀ i, Equiv.Perm.sign (coreWords i) = 1 := by decide +kernel
  rintro _ ⟨i, rfl⟩
  exact h i

theorem blockCore_preserves_each_half {g : Perm} (hg : g ∈ blockCore) (x : Fin 8) :
    (g x).val / 4 = x.val / 4 := by
  have h : ∀ i x, (coreWords i x).val / 4 = x.val / 4 := by decide +kernel
  obtain ⟨i, rfl⟩ := hg
  exact h i x

theorem regular_not_le_blockCore {A : Subgroup Perm} (hA : EightCase.regular.Realizes A) :
    ¬ A ≤ blockCore := by
  intro h
  obtain ⟨a, ha, _⟩ := hA.2.2.2 0 4
  have hh := blockCore_preserves_each_half (h a.property) 0
  rw [ha] at hh
  norm_num at hh

theorem transposition_not_le_blockCore {A : Subgroup Perm}
    (hA : EightCase.transposition.Realizes A) : ¬ A ≤ blockCore := by
  obtain ⟨g, rfl⟩ := hA
  intro h
  have hh := blockCore_le_alternating (h (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (pairSwap_mem (n := 8) (m := 1) 0 (by decide))))
  change Equiv.Perm.sign (g * pairSwap 8 0 * g⁻¹) = 1 at hh
  have hs : Equiv.Perm.sign (pairSwap 8 0) = -1 := by decide +kernel
  simp only [map_mul, map_inv, hs] at hh
  have he := congrArg (fun x => (Equiv.Perm.sign g)⁻¹ * x * Equiv.Perm.sign g) hh
  simp at he

theorem disjoint_not_le_blockCore {A : Subgroup Perm}
    (hA : EightCase.disjoint.Realizes A) : ¬ A ≤ blockCore :=
  fun h => EightCase.disjoint_not_le_alternating hA (h.trans blockCore_le_alternating)

def quotientImage (A : Subgroup Perm) : Subgroup Quotient :=
  (A.subgroupOf canonicalSylow).map quotientMap

theorem quotientImage_eq_bot_iff {A : Subgroup Perm} (hA : A ≤ canonicalSylow) :
    quotientImage A = ⊥ ↔ A ≤ blockCore := by
  rw [quotientImage, Subgroup.map_eq_bot_iff]
  change A.subgroupOf canonicalSylow ≤ (QuotientGroup.mk' sylowCore).ker ↔ _
  rw [QuotientGroup.ker_mk']
  constructor
  · intro h x hx
    exact h (show (⟨x, hA hx⟩ : SylowGroup) ∈ A.subgroupOf canonicalSylow from hx)
  · intro h x hx
    exact h hx

theorem card_inf_mul_card_quotientImage {A : Subgroup Perm} (hA : A ≤ canonicalSylow) :
    Nat.card (A ⊓ blockCore : Subgroup Perm) * Nat.card (quotientImage A) = Nat.card A := by
  have ht := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup SylowGroup)
    (quotientMap.ker ⊓ A.subgroupOf canonicalSylow) (A.subgroupOf canonicalSylow)
    bot_le inf_le_right
  rw [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right, Subgroup.relIndex_ker,
    Subgroup.relIndex_bot_left] at ht
  have hk : quotientMap.ker ⊓ A.subgroupOf canonicalSylow =
      (A ⊓ blockCore).subgroupOf canonicalSylow := by
    rw [quotientMap, QuotientGroup.ker_mk']
    ext x
    exact and_comm
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show A ⊓ blockCore ≤ canonicalSylow from inf_le_left.trans hA)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at ht
  exact ht

theorem rank_inf_add_rank_quotientImage {A : Subgroup Perm} (hA : A ≤ canonicalSylow) :
    rank (A ⊓ blockCore) + rank (quotientImage A) = rank A := by
  have hp : IsPGroup 2 A := canonicalSylow.isPGroup'.to_le hA
  have hk : IsPGroup 2 (A ⊓ blockCore : Subgroup Perm) := hp.to_le inf_le_left
  have hi : IsPGroup 2 (quotientImage A) := by
    have hs : IsPGroup 2 (A.subgroupOf canonicalSylow) :=
      hp.of_injective (Subgroup.subgroupOfEquivOfLe hA).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hA).injective
    exact hs.map quotientMap
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  obtain ⟨i, hi⟩ := hi.exists_card_eq
  have hc := card_inf_mul_card_quotientImage hA
  rw [hk, hi, ← pow_add] at hc
  simp only [rank, hk, hi, ← hc, Nat.log_pow Nat.one_lt_two]


instance : evenSylow.Normal := by
  change ((alternatingGroup (Fin 8)).comap (canonicalSylow : Subgroup Perm).subtype).Normal
  infer_instance

instance : evenFour.Normal :=
  (inferInstance : evenSylow.Normal).map quotientMap (QuotientGroup.mk'_surjective _)

theorem sylowCore_le_evenSylow : sylowCore ≤ evenSylow := by
  intro x hx
  exact blockCore_le_alternating hx

private def sylowSign : SylowGroup →* ℤˣ :=
  Equiv.Perm.sign.comp (canonicalSylow : Subgroup Perm).subtype

private theorem sylowSign_surjective : Function.Surjective sylowSign := by
  intro x
  rcases Int.units_eq_one_or x with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨⟨pairSwap 8 0, sylowGenerators_mem 0⟩, by decide +kernel⟩

theorem card_evenSylow : Nat.card evenSylow = 64 := by
  have hk : sylowSign.ker = evenSylow := rfl
  have hi : evenSylow.index = 2 := by
    rw [← hk, Subgroup.index_ker]
    rw [sylowSign.range_eq_top_of_surjective sylowSign_surjective,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ℤˣ) ≃* ℤˣ).toEquiv,
      Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  have hc := evenSylow.card_mul_index
  have hs : Nat.card SylowGroup = 128 := card_canonicalTwoSubgroup
  rw [hi, hs] at hc
  omega

theorem card_evenFour : Nat.card evenFour = 4 := by
  have ht := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup SylowGroup)
    (quotientMap.ker ⊓ evenSylow) evenSylow bot_le inf_le_right
  rw [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right, Subgroup.relIndex_ker,
    Subgroup.relIndex_bot_left] at ht
  have hk : quotientMap.ker ⊓ evenSylow = sylowCore := by
    rw [quotientMap, QuotientGroup.ker_mk', inf_eq_left.mpr sylowCore_le_evenSylow]
  rw [hk, card_sylowCore, card_evenSylow] at ht
  change 16 * Nat.card evenFour = 64 at ht
  omega

theorem evenSylow_square_mem_core (x : SylowGroup) (hx : x ∈ evenSylow) :
    x ^ 2 ∈ sylowCore := by
  have h : ∀ i, Equiv.Perm.sign (sylowWord i) = 1 →
      ∃ j, coreWords j = sylowWord i ^ 2 := by decide +kernel
  obtain ⟨i, hi⟩ := (mem_canonicalTwoSubgroup x).mp x.property
  have hs : Equiv.Perm.sign (sylowWord i) = 1 := hi ▸ hx
  obtain ⟨j, hj⟩ := h i hs
  exact ⟨j, hj.trans (congrArg (· ^ 2) hi)⟩

instance : IsElementaryAbelian 2 evenFour := by
  have hp (x : evenFour) : x ^ 2 = 1 := by
    obtain ⟨a, ha, he⟩ := x.property
    apply Subtype.ext
    change x.val ^ 2 = 1
    rw [← he, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (evenSylow_square_mem_core a ha)
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hp }
  intro a b
  exact (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
