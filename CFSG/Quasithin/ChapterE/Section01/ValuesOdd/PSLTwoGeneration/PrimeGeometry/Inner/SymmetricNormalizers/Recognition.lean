module

public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.SelfCentralizingFourSymmetricFour
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import GorensteinWalter.KleinFourMapInjective
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-!
# Recognizing four-group normalizers in the inner PSL₂ calculation

A self-centralizing four-group has normalizer of order at most 24, by its
conjugation action on the four-group. In a Sylow two-subgroup of order at
least eight it lies in an order-eight subgroup which normalizes it. Thus
an element of order three in the normalizer forces order 24; the faithful
four-point recognition theorem then identifies the actual normalizer as S₄.

We also construct the intrinsic normal four-group in every S₄ overgroup of
the ambient Sylow subgroup, and show uniqueness of a normal four-group in S₄.
The order-three element is an explicit, still unconstructed input here.

Source: Aschbacher--Smith, E.1.14(6), printed p.214, citing Asc82a 4.10;
these are the local group reductions used for the E.1.2 geometry.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
variable {G : Type*} [Group G] [Finite G]

theorem normalizer_card_le (B : Subgroup G) [IsKleinFour B]
    (hself : centralizer (B : Set G) = B) : Nat.card (normalizer (B : Set G)) ≤ 24 := by
  let f := B.normalizerMonoidHom
  have hk : Nat.card f.ker = 4 := by
    rw [normalizerMonoidHom_ker, hself,
      Nat.card_congr (subgroupOfEquivOfLe (le_normalizer (H := B))).toEquiv]
    exact IsKleinFour.card_four
  have hr : Nat.card f.range ≤ 6 := by
    simpa only [IsKleinFour.card_mulAut] using
      Nat.card_le_card_of_injective (fun x : f.range => (x : MulAut B)) Subtype.val_injective
  have hc := f.ker.card_mul_index
  rw [index_ker, hk] at hc
  omega

omit [Finite G] in
theorem klein_subgroupOf (B H : Subgroup G) [IsKleinFour B] (h : B ≤ H) :
    IsKleinFour (B.subgroupOf H) := by
  let e := subgroupOfEquivOfLe h
  exact ⟨(Nat.card_congr e.toEquiv).trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩

theorem exists_eight_overgroup (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (B : Subgroup G) [IsKleinFour B] (hBT : B ≤ T) :
    ∃ D : Subgroup G, B ≤ D ∧ D ≤ T ∧ Nat.card D = 8 ∧ D ≤ normalizer (B : Set G) := by
  have hdvd : 2 ^ (2 + 1) ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn] at hT ⊢
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hT)
  have hBc : Nat.card (B.subgroupOf (T : Subgroup G)) = 2 ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBT).toEquiv, IsKleinFour.card_four]
    norm_num
  obtain ⟨D₀, hD₀, hBD₀⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hBc
  let D := D₀.map (T : Subgroup G).subtype
  have hDT : D ≤ (T : Subgroup G) := map_subtype_le D₀
  have hBD : B ≤ D := by
    intro b hb
    exact mem_map.mpr ⟨⟨b, hBT hb⟩, hBD₀ hb, rfl⟩
  have hDc : Nat.card D = 8 := by
    rw [show Nat.card D = Nat.card D₀ from card_subtype _ _]
    exact hD₀
  have hBi : (B.subgroupOf D).index = 2 := by
    have hc := (B.subgroupOf D).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hBD).toEquiv,
      IsKleinFour.card_four, hDc] at hc
    omega
  exact ⟨D, hBD, hDT, hDc,
    (normal_subgroupOf_iff_le_normalizer hBD).mp (normal_of_index_eq_two hBi)⟩

theorem normalizer_equiv_of_cubic (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (B : Subgroup G) [IsKleinFour B] (hBT : B ≤ T)
    (hself : centralizer (B : Set G) = B)
    (hcubic : ∃ x : normalizer (B : Set G), orderOf x = 3) :
    Nonempty (normalizer (B : Set G) ≃* Equiv.Perm (Fin 4)) := by
  let N := normalizer (B : Set G)
  have hBN : B ≤ N := le_normalizer
  have h8 : 8 ∣ Nat.card N := by
    obtain ⟨D, _, _, hD, hDN⟩ := exists_eight_overgroup T hT B hBT
    rw [← hD]
    exact card_dvd_of_le hDN
  have h3 : 3 ∣ Nat.card N := by
    obtain ⟨x, hx⟩ := hcubic
    rw [← hx]
    exact orderOf_dvd_natCard x
  have h24 : Nat.card N = 24 := by
    have hdiv : 24 ∣ Nat.card N :=
      (show Nat.Coprime 8 3 by decide).mul_dvd_of_dvd_of_dvd h8 h3
    exact Nat.le_antisymm (normalizer_card_le B hself)
      (Nat.le_of_dvd Nat.card_pos hdiv)
  let U := B.subgroupOf N
  let : IsKleinFour U := klein_subgroupOf B N hBN
  let : IsElementaryAbelian 2 U :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hcent : centralizer (U : Set N) ≤ U := by
    intro x hx
    apply hself.le
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx ⟨b, hBN hb⟩ hb)
  exact mulEquiv_perm_four_of_selfCentralizing_four_card_twentyfour U
    IsKleinFour.card_four hcent h24

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
variable {G : Type*} [Group G] [Finite G]
theorem symmetric_core_klein (e : G ≃* Equiv.Perm (Fin 4)) :
    IsKleinFour (pCore 2 G) := by
  have hG : Nat.card G = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  obtain ⟨hel, hc⟩ := symmetric_four_model_twoCore_data (Or.inl ⟨e⟩)
  have hcore : Nat.card (pCore 2 G) = 4 := by rcases hc with hc | hc <;> omega
  let : IsElementaryAbelian 2 (pCore 2 G) := hel
  let : Nontrivial (pCore 2 G) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcore]; decide)
  exact ⟨hcore, IsElementaryAbelian.exponent_eq_prime⟩

theorem normal_four_eq_core (e : G ≃* Equiv.Perm (Fin 4)) (A : Subgroup G)
    [IsKleinFour A] [A.Normal] : A = pCore 2 G := by
  let : IsKleinFour (pCore 2 G) := symmetric_core_klein e
  have hA : IsPGroup 2 A := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; decide)
  have hle : A ≤ pCore 2 G := le_sSup ⟨inferInstance, hA⟩
  apply eq_of_le_of_card_ge hle
  simp only [IsKleinFour.card_four, le_refl]

theorem exists_normal_four_le_sylow (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (eM : M ≃* Equiv.Perm (Fin 4)) :
    ∃ B : Subgroup G, B ≤ (T : Subgroup G) ∧ IsKleinFour B ∧
      M ≤ normalizer (B : Set G) := by
  let S := T.comapOfInjective M.subtype M.subtype_injective (by simpa using hTM)
  let B := (pCore 2 M).map M.subtype
  let : IsKleinFour (pCore 2 M) := symmetric_core_klein eM
  have hp : IsPGroup 2 (pCore 2 M) := pCore_isPGroup
  have hcore : pCore 2 M ≤ (S : Subgroup M) := hp.le_sylow_of_normal S
  have hBM : B ≤ M := map_subtype_le _
  refine ⟨B, ?_, GorensteinWalter.isKleinFour_map_of_injective _ inferInstance _
    M.subtype_injective, ?_⟩
  · rintro b ⟨x, hx, rfl⟩
    exact hcore hx
  · apply (normal_subgroupOf_iff_le_normalizer hBM).mp
    change (comap M.subtype ((pCore 2 M).map M.subtype)).Normal
    rw [comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
