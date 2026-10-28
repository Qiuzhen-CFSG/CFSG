module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Marked
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.SourceSet
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Action
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.OrdinaryFusion.Fusion
public import Theory.GroupTheory.InvolutionTransferResidual
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic
/-!
# Transfer and normalizer fusion in the ordinary A₆ case

Every involution of the actual LE ≃ S₆ × C₂ is L-conjugate into the marked
sixteen-group. The proof uses cycle types and corrects an odd conjugator by
a transposition centralizing the chosen representative. The product of sign
with the central C₂ character has value −1 on each marked generator. If the
total product were not fused with z, the pair and triple exclusions would
therefore make every Sylow conjugate of z avoid this character's kernel.
Thompson transfer then contradicts O²(G) = G in a nonabelian simple group.

The corrected set β is zᴳ ∩ A throughout. The imported Sylow calculation
constructs the two-member maximal elementary family and proves weak closure
of A. Burnside fusion then gives normalizer transitivity on this five-point set.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

open Equiv Equiv.Perm Subgroup
@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Six.OrdinaryFusion
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def representative (n : Fin 4) (c : Multiplicative (ZMod 2)) : Binary :=
  Multiplicative.ofAdd (fun i => if i = 3 then c.toAdd else if i.val < n.val then 1 else 0)

theorem representative_cycleType (n : Fin 4) (c : Multiplicative (ZMod 2)) :
    (coordinateHom (representative n c)).1.cycleType = Multiset.replicate n.val 2 := by
  revert n c; decide +kernel

theorem representative_second (n : Fin 4) (c : Multiplicative (ZMod 2)) :
    (coordinateHom (representative n c)).2 = c := by
  revert n c; decide +kernel

theorem representative_commute (n : Fin 4) (c : Multiplicative (ZMod 2)) :
    Commute (swap 0 1) (coordinateHom (representative n c)).1 := by
  have hc : c = 1 ∨ c = Multiplicative.ofAdd 1 := by
    revert c
    decide +kernel
  rcases hc with rfl | rfl <;> fin_cases n
  all_goals
    apply Equiv.ext
    intro x
    fin_cases x <;> decide +kernel

theorem product_involution_coverage (a : Product) (ha : a ^ 2 = 1) :
    ∃ k ∈ alternatingGroup (Fin 6), ∃ v : Binary,
      (k, 1) * a * (k, 1)⁻¹ = coordinateHom v := by
  have hp : a.1 ^ 2 = 1 := congrArg Prod.fst ha
  have hc := cycleType_of_pow_prime_eq_one hp
  have hn : a.1.cycleType.card < 4 := by
    have hsum := sum_cycleType_le a.1
    rw [hc, Multiset.sum_replicate] at hsum
    simp only [nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hsum
    omega
  let n : Fin 4 := ⟨a.1.cycleType.card, hn⟩
  let v := representative n a.2
  let q := (coordinateHom v).1
  have hq : a.1.cycleType = q.cycleType := hc.trans (representative_cycleType n a.2).symm
  obtain ⟨k, hk⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr hq)
  have hk' : k * a.1 * k⁻¹ = q := hk
  have hconj : ∃ k ∈ alternatingGroup (Fin 6), k * a.1 * k⁻¹ = q := by
    rcases Int.units_eq_one_or (sign k) with he | he
    · exact ⟨k, mem_alternatingGroup.mpr he, hk'⟩
    · refine ⟨swap 0 1 * k, ?_, ?_⟩
      · rw [mem_alternatingGroup, map_mul, sign_swap (by decide : (0 : Fin 6) ≠ 1), he]
        decide
      · calc
          (swap 0 1 * k) * a.1 * (swap 0 1 * k)⁻¹ =
              swap 0 1 * (k * a.1 * k⁻¹) * (swap 0 1)⁻¹ := by group
          _ = swap 0 1 * q * (swap 0 1)⁻¹ := by rw [hk']
          _ = q := by rw [(representative_commute n a.2).eq, mul_inv_cancel_right]
  obtain ⟨k, hkA, hkq⟩ := hconj
  refine ⟨k, hkA, v, Prod.ext hkq ?_⟩
  simpa only [Prod.snd_mul, Prod.snd_inv, inv_one, one_mul, mul_one] using
    (representative_second n a.2).symm

/-- The order-two character, equal to sign times the central coordinate. -/
def centralSign : Multiplicative (ZMod 2) →* ℤˣ where
  toFun c := if c.toAdd = 0 then 1 else -1
  map_one' := rfl
  map_mul' := by decide +kernel

def productCharacter : Product →* ℤˣ :=
  (sign.comp (MonoidHom.fst _ _)) * (centralSign.comp (MonoidHom.snd _ _))

theorem character_basis (i : Fin 4) : productCharacter (coordinateHom (basis i)) = -1 := by
  revert i; decide +kernel

theorem card_units_int : Nat.card ℤˣ = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨1, -1, by decide, ?_⟩
  ext u
  simpa using Int.units_eq_one_or u

variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

def character (M : AlternatingProductModel L z r 6) : AlternatingOvergroup L z r →* ℤˣ :=
  productCharacter.comp M.equiv.toMonoidHom

theorem character_embedding (M : AlternatingProductModel L z r 6) (v : Binary) :
    character M ⟨embedding M v, elementary_le M ⟨v, rfl⟩⟩ =
      productCharacter (coordinateHom v) := by
  change productCharacter (M.equiv (M.equiv.symm (coordinateHom v))) = _
  rw [M.equiv.apply_symm_apply]

theorem involution_coverage (M : AlternatingProductModel L z r 6) {a : G}
    (ha : a ∈ AlternatingOvergroup L z r) (ha2 : a ^ 2 = 1) :
      ∃ l ∈ L, MulAut.conj l a ∈ elementary M := by
  let aH : AlternatingOvergroup L z r := ⟨a, ha⟩
  have hpow : (M.equiv aH) ^ 2 = 1 := by
    rw [← map_pow]
    have h : aH ^ 2 = 1 := Subtype.ext ha2
    rw [h, map_one]
  obtain ⟨k, hk, v, he⟩ := product_involution_coverage (M.equiv aH) hpow
  refine ⟨lift M (k, 1), lift_even_mem M k hk, v, ?_⟩
  have hh := congrArg (lift M) he
  rw [map_mul, map_mul, map_inv, lift_equiv] at hh
  exact hh.symm

/-- Every involution of the actual Sylow subgroup is fused into A under L. -/
theorem sylow_involution_coverage (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r)
    (a : T) (ha : a ^ 2 = 1) :
    ∃ l ∈ L, MulAut.conj l (a : G) ∈ elementary M := by
  have hT : (T : Subgroup G) ≤ AlternatingOvergroup L z r := hLT ▸ le_sup_right
  exact involution_coverage M (hT a.property) (congrArg Subtype.val ha)

def sylowCharacter (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≤ AlternatingOvergroup L z r) : T →* ℤˣ :=
  (character M).comp (inclusion hT)

theorem character_nonfusion (M : AlternatingProductModel L z r 6)
    (hex : ProductExclusions M) (htotal : ¬ IsConj z (total M))
    {a : AlternatingOvergroup L z r} (ha : IsConj z (a : G)) :
    character M a ≠ 1 := by
  classical
  have hz2 : z ^ 2 = 1 := by
    rw [← generator_three M, generator, ← map_pow, vector_exp, map_one]
  have ha2 : (a : G) ^ 2 = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp ha
    rw [← hg]
    change (MulAut.conj g z) ^ 2 = 1
    rw [← map_pow, hz2, map_one]
  obtain ⟨l, hl, hla⟩ := involution_coverage M a.property ha2
  have hb : MulAut.conj l (a : G) ∈ beta M :=
    ⟨hla, ha.trans (isConj_iff.mpr ⟨l, rfl⟩)⟩
  have halpha : MulAut.conj l (a : G) ∈ alpha M := by
    rcases beta_subset M hex.1 hex.2 hb with hm | hm
    · exact hm
    · exact (htotal ((Set.mem_singleton_iff.mp hm) ▸ hb.2)).elim
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp halpha
  let lH : AlternatingOvergroup L z r := ⟨l, mem_sup_left (mem_sup_left hl)⟩
  have he : character M (lH * a * lH⁻¹) = -1 := by
    have hi' : lH * a * lH⁻¹ =
        ⟨embedding M (basis i), elementary_le M (generator_mem M i)⟩ := Subtype.ext hi.symm
    rw [hi', character_embedding, character_basis]
  have hc : character M (lH * a * lH⁻¹) = character M a := by
    rw [map_mul, map_mul, map_inv, mul_comm (character M lH), mul_inv_cancel_right]
  rw [hc] at he
  rw [he]
  decide


theorem character_z (M : AlternatingProductModel L z r 6) :
    character M ⟨z, mem_sup_right (mem_zpowers z)⟩ = -1 := by
  change productCharacter (M.equiv _) = -1
  rw [M.central_image]
  decide +kernel

/-- The constructed character is onto on every Sylow subgroup containing A. -/
theorem sylowCharacter_surjective (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≤ AlternatingOvergroup L z r)
    (hAT : elementary M ≤ (T : Subgroup G)) : Function.Surjective (sylowCharacter M hT) := by
  have hz : z ∈ (T : Subgroup G) := hAT (by simpa only [generator_three] using generator_mem M 3)
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨⟨z, hz⟩, character_z M⟩

/-- The index-two subgroup used in transfer, inside the actual Sylow subgroup. -/
def transferSubgroup (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≤ AlternatingOvergroup L z r) : Subgroup T :=
  (sylowCharacter M hT).ker

theorem transferSubgroup_index (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≤ AlternatingOvergroup L z r)
    (hAT : elementary M ≤ (T : Subgroup G)) : (transferSubgroup M hT).index = 2 := by
  rw [transferSubgroup, index_ker,
    MonoidHom.range_eq_top.mpr (sylowCharacter_surjective M hT hAT), card_top, card_units_int]

theorem character_r (M : AlternatingProductModel L z r 6) :
    character M ⟨r, mem_sup_left (mem_sup_right (mem_zpowers r))⟩ = -1 := by
  have hs : sign (outerPermutation M) = -1 :=
    (isSwap_iff_cycleType.mpr (outerPermutation_cycleType M)).sign_eq
  change sign (outerPermutation M) * centralSign (M.equiv _).2 = -1
  rw [hs, M.outer_second, map_one, mul_one]

private theorem mem_component_of_character_one (M : AlternatingProductModel L z r 6)
    (a : AlternatingOvergroup L z r) (hc : character M a = 1) (hs : (M.equiv a).2 = 1) :
    (a : G) ∈ L := by
  apply (M.component_iff a).mpr
  refine ⟨mem_alternatingGroup.mpr ?_, hs⟩
  change sign (M.equiv a).1 * centralSign (M.equiv a).2 = 1 at hc
  simpa only [hs, map_one, mul_one] using hc

/-- The character kernel is exactly the source subgroup L⟨rz⟩ in LE. -/
theorem character_kernel_iff (M : AlternatingProductModel L z r 6)
    (a : AlternatingOvergroup L z r) :
    character M a = 1 ↔ (a : G) ∈ L ⊔ zpowers (r * z) := by
  let rH : AlternatingOvergroup L z r := ⟨r, mem_sup_left (mem_sup_right (mem_zpowers r))⟩
  let zH : AlternatingOvergroup L z r := ⟨z, mem_sup_right (mem_zpowers z)⟩
  have hcR : character M (rH * zH) = 1 := by
    rw [map_mul, character_r, character_z]
    decide
  constructor
  · intro ha
    by_cases hsecond : (M.equiv a).2 = 1
    · exact mem_sup_left (mem_component_of_character_one M a ha hsecond)
    have hsecond' : (M.equiv a).2 = Multiplicative.ofAdd 1 := by
      have hc (c : Multiplicative (ZMod 2)) : c = 1 ∨ c = Multiplicative.ofAdd 1 := by
        revert c; decide +kernel
      exact (hc _).resolve_left hsecond
    have hb : (a * (rH * zH)⁻¹ : AlternatingOvergroup L z r).val ∈ L := by
      apply mem_component_of_character_one M
      · rw [map_mul, map_inv, ha, hcR, inv_one, one_mul]
      · rw [map_mul, map_inv, map_mul]
        simp only [Prod.snd_mul, Prod.snd_inv]
        have hz : (M.equiv zH).2 = Multiplicative.ofAdd 1 :=
          congrArg Prod.snd M.central_image
        have hr : (M.equiv rH).2 = 1 := M.outer_second
        rw [hsecond', hr, hz, one_mul, mul_inv_cancel]
    have hm := (L ⊔ zpowers (r * z)).mul_mem (mem_sup_left hb)
      (mem_sup_right (mem_zpowers (r * z)))
    change (a : G) * (r * z)⁻¹ * (r * z) ∈ L ⊔ zpowers (r * z) at hm
    simpa only [inv_mul_cancel_right] using hm
  · intro ha
    let J := (character M).ker.map (AlternatingOvergroup L z r).subtype
    have hL : L ≤ J := by
      intro l hl
      let lH : AlternatingOvergroup L z r := ⟨l, mem_sup_left (mem_sup_left hl)⟩
      refine ⟨lH, ?_, rfl⟩
      have hp := (M.component_iff lH).mp hl
      change sign (M.equiv lH).1 * centralSign (M.equiv lH).2 = 1
      rw [mem_alternatingGroup.mp hp.1, hp.2, map_one, one_mul]
    have hR : r * z ∈ J := ⟨rH * zH, hcR, rfl⟩
    obtain ⟨b, hb, he⟩ := (sup_le hL (zpowers_le.mpr hR)) ha
    have he' : b = a := Subtype.ext he
    exact he' ▸ hb

/-- The Sylow kernel is the intersection T ∩ L⟨rz⟩, with relative index two. -/
theorem transferSubgroup_eq (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≤ AlternatingOvergroup L z r) :
    transferSubgroup M hT = (L ⊔ zpowers (r * z)).subgroupOf (T : Subgroup G) := by
  ext a
  exact character_kernel_iff M (inclusion hT a)

variable [Finite G]

private theorem twoResidual_eq_top_of_simple [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G) : pResidual 2 G = ⊤ := by
  let : Group.IsPerfect G := ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (_root_.commutator G) inferInstance).resolve_left
      (fun he => hnonab ((commutator_eq_bot_iff G).mp he))⟩
  apply (pResidual_eq_top_iff 2 G).mpr
  intro N hN hp
  let := hN
  have hsub : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The ordinary branch forces fusion of the total product by Thompson transfer.
Only the supplied local model, its Sylow placement, the product exclusions and
nonabelian simplicity are needed. -/
theorem total_conjugate [IsSimpleGroup G] (hnonab : ¬ IsMulCommutative G)
    (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hAT : elementary M ≤ (T : Subgroup G))
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r)
    (hex : ProductExclusions M) : IsConj z (total M) := by
  by_contra hn
  have hT : (T : Subgroup G) ≤ AlternatingOvergroup L z r := hLT ▸ le_sup_right
  have hz : z ∈ (T : Subgroup G) := hAT (by simpa only [generator_three] using generator_mem M 3)
  have hz2 : orderOf z = 2 := by
    have hs : z ^ 2 = 1 := by
      rw [← generator_three M, generator, ← map_pow, vector_exp, map_one]
    have hne : z ≠ 1 := generator_three M ▸ generator_ne_one M 3
    exact orderOf_eq_prime hs hne
  have hres : z ∉ pResidual 2 G := by
    apply T.not_mem_twoResidual_of_nonfusion_index_two
      (transferSubgroup M hT) (transferSubgroup_index M hT hAT)
      ⟨z, hz⟩ ((orderOf_coe _).symm.trans hz2)
    intro a ha
    exact character_nonfusion M hex hn (a := inclusion hT a) ha
  exact hres (twoResidual_eq_top_of_simple hnonab ▸ mem_top z)

/-- Both the five-point set and its cardinality use the actual A, not T. -/
theorem beta_of_ordinary [IsSimpleGroup G] (hnonab : ¬ IsMulCommutative G)
    (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hAT : elementary M ≤ (T : Subgroup G))
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r)
    (hr : IsConj z r) (hex : ProductExclusions M) :
    beta M = (alpha M : Set G) ∪ {total M} ∧ Nat.card (beta M) = 5 := by
  have ht := total_conjugate hnonab M hAT hLT hex
  exact ⟨beta_eq_of_total_conjugate M hr hex.1 hex.2 ht,
    beta_card_of_total_conjugate M hr hex.1 hex.2 ht⟩

/-- The complete transfer and fusion output for the ordinary LT = LE branch.
The geometric model, its placement, and its product exclusions remain the
explicit inputs constructed by the source-theorem assembly. -/
theorem fusion [IsSimpleGroup G] (hnonab : ¬ IsMulCommutative G)
    (M : AlternatingProductModel L z r 6) {T : Sylow 2 G}
    (hAT : elementary M ≤ (T : Subgroup G))
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r)
    (hr : IsConj z r) (hex : ProductExclusions M) :
    IsConj z (total M) ∧ NormalizerTransitive M ∧
      beta M = (alpha M : Set G) ∪ {total M} ∧ Nat.card (beta M) = 5 := by
  have ht := total_conjugate hnonab M hAT hLT hex
  exact ⟨ht, normalizer_transitive M hAT hLT,
    beta_eq_of_total_conjugate M hr hex.1 hex.2 ht,
    beta_card_of_total_conjugate M hr hex.1 hex.2 ht⟩

end CFSG.Quasithin.Chapter16.Intersections.Six.OrdinaryFusion
