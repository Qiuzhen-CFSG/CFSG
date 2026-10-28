module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource
public import Theory.GroupAction.CoprimeQuotientOrbitBound

/-!
# The original torus invariant interval

Every nonidentity torus element acts fixed-point freely on R. Coprime
fixed-point lifting makes its action on U/N free away from one. Orbit
counting and |U|=q² leave no proper subgroup between Z(R) and U.
Source: Aschbacher–Smith, proof of 2.4.18, printed p.534.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The odd torus leaves no intermediate subgroup between Z(R) and U.
Fixed-point lifting on U/N proves the statement directly on the original
cover, without assuming an equivariant coordinate identification. -/
theorem source_centerless_torus_invariant_interval
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥)
    (D N : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype)
    (hDodd : Odd (Nat.card D)) (hDcard : Nat.card D = 2^n-1)
    (hDN : D ≤ normalizer (N : Set G))
    (hZN : distinguishedZ d ≤ N)
    (hNU : N ≤ sourceModule (d.block.map d.H.subtype)) :
    N = distinguishedZ d ∨ N = sourceModule (d.block.map d.H.subtype) := by
  let L := d.block.map d.H.subtype
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  let Z := distinguishedZ d
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  let : IsElementaryAbelian 2 U := by
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map L.subtype
  have hUcard : Nat.card U = 2^n * 2^n := by
    rw [show Nat.card U = Nat.card (ChapterC.blockU L) from card_map_of_injective L.subtype_injective]
    have hfixed : Nat.card (ChapterC.blockFixed L) = 1 := by
      change Nat.card ((center L).subgroupOf (ChapterC.blockU L)) = 1
      rw [hz,bot_subgroupOf,card_bot]
    rw [card_eq_card_quotient_mul_card_subgroup (ChapterC.blockFixed L),hfixed,mul_one]
    exact hK.module_card.trans (by rw [show n*2=n+n by omega,pow_add])
  have hDU : D ≤ normalizer (U : Set G) := hDL.trans
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  let ρ := U.normalizerMonoidHom.comp (inclusion hDU)
  let : MulDistribMulAction D U := MulDistribMulAction.compHom U ρ
  let N' := N.subgroupOf U
  let : N'.Normal := inferInstance
  have hinv : IsInvariant D U N' := ⟨fun a u => mem_normalizer_iff.mp (hDN a.property) u⟩
  by_cases he : N = U
  · exact Or.inr he
  have hproper : N' ≠ ⊤ := by
    intro ht
    have hm := congrArg (map U.subtype) ht
    rw [map_subgroupOf_eq_of_le hNU,← MonoidHom.range_eq_map,range_subtype] at hm
    exact he hm
  have hcop : Nat.Coprime (Nat.card D) (Nat.card U) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hDodd).pow_right _
  have hUR : U ≤ R := by
    change sourceModule (d.block.map d.H.subtype) ≤ R
    rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
    exact le_sSup (d.core_source hG T hST).2.2
  have hf : ∀ a : D, a ≠ 1 → ∀ u : U, a • u = u → u ∈ N' := by
    intro a ha u hu
    have hu1 : u = 1 := by
      by_contra hu1
      have ha1 := source_centerless_odd_fixed_free d hG T hST hsingle hL hM hTM hunique hz
        D hDL hDodd a a.property u (hUR u.property)
        (fun he => hu1 (Subtype.ext he)) (congrArg Subtype.val hu)
      exact ha (Subtype.ext ha1)
    exact hu1 ▸ N'.one_mem
  have hb := Theory.GroupAction.card_actor_lt_card_quotient_of_fixed_le N' hinv
    (inferInstance : Group.IsSolvable U) hcop hproper hf
  rw [hDcard] at hb
  have hpos : 0 < 2^n := pow_pos (by decide) _
  have hq : 2^n ≤ Nat.card (U ⧸ N') := by omega
  have hcount := card_eq_card_quotient_mul_card_subgroup N'
  rw [hUcard,Nat.card_congr (subgroupOfEquivOfLe hNU).toEquiv] at hcount
  have hNcard : Nat.card N ≤ 2^n := by nlinarith
  have hZcard := (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.1
  exact Or.inl (eq_of_le_of_card_ge hZN (hZcard ▸ hNcard)).symm
end CFSG.Quasithin.Chapter2.LinearShadows.Single
