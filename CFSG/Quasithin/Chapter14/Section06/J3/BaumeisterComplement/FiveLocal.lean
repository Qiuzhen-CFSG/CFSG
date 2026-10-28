module
public import Theory.SpecificGroups.AlternatingSix.GoldenClassGeometry
public import Mathlib.GroupTheory.Sylow

/-!
# The five-normalizers used in Baumeister's second parabolic

The centralizer of a quintic in A₆ has order five. The automizer bound
and Sylow congruence force its normalizer to have order ten. Conversely,
every order-ten subgroup is such a normalizer, so is self-normalizing,
and Sylow conjugacy aligns any two of them.

These are the quotient calculations for the literal L₁₂ in Lemma 2.5,
Baumeister, A geometry for groups of J₃-type (2007), p.496. The
`LiteralQuotient` extension applies them through the original cubic map.
-/

open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
local notation "A6" => alternatingGroup (Fin 6)
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem five_normalizer_card (P : Subgroup A6) (hP : Nat.card P = 5) :
    Nat.card (normalizer (P : Set A6)) = 10 := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  have hxG : orderOf (x : A6) = 5 := (orderOf_coe x).trans hx
  have hPx : P = zpowers (x : A6) :=
    (eq_of_le_of_card_ge (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers,hxG,hP])).symm
  let N := normalizer (P : Set A6)
  let C := (centralizer (P : Set A6)).subgroupOf N
  have hC : Nat.card C = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set A6))).toEquiv,
      hPx, zpowers_eq_closure, centralizer_closure]
    exact AlternatingSix.GoldenClassGeometry.centralizer_five _ hxG
  have hi : C.index ∣ 4 := by
    have hh := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
    let : IsCyclic P := isCyclic_of_prime_card hP
    rw [normalizerMonoidHom_ker, ← index, IsCyclic.card_mulAut, hP] at hh
    simpa only [Nat.totient_prime (by decide : Nat.Prime 5)] using hh
  have hN := C.index_mul_card
  rw [hC] at hN
  have hG : Nat.card A6 = 360 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  let S : Sylow 5 A6 := Sylow.ofCard P (by rw [hP,hG]; decide +kernel)
  have hm := card_sylow_modEq_one 5 A6
  rw [S.card_eq_index_normalizer] at hm
  change N.index % 5 = 1 % 5 at hm
  have hcard := N.card_mul_index
  rw [hG] at hcard
  have hib : C.index ≤ 4 := Nat.le_of_dvd (by decide) hi
  change Nat.card N = 10
  rw [← hN]
  rw [← hN] at hcard
  interval_cases k : C.index <;> omega

theorem ten_eq_five_normalizer (B : Subgroup A6) (hB : Nat.card B = 10) :
    ∃ P : Sylow 5 A6, normalizer (P : Set A6) = B := by
  let S : Sylow 5 B := default
  have hS : Nat.card S = 5 := by rw [S.card_eq_multiplicity,hB]; decide +kernel
  have hi : (S : Subgroup B).index = 2 := by
    have hh := (S : Subgroup B).card_mul_index
    rw [hS,hB] at hh
    omega
  let : (S : Subgroup B).Normal := normal_of_index_eq_two hi
  let P0 := (S : Subgroup B).map B.subtype
  have hP : Nat.card P0 = 5 := (card_map_of_injective B.subtype_injective).trans hS
  let P : Sylow 5 A6 := Sylow.ofCard P0 (by
    rw [hP,nat_card_alternatingGroup, Nat.card_eq_fintype_card]; decide +kernel)
  have hle : B ≤ normalizer (P0 : Set A6) := by
    have hh := (S : Subgroup B).le_normalizer_map B.subtype
    rw [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  exact ⟨P,(eq_of_le_of_card_ge hle (by rw [five_normalizer_card P0 hP,hB])).symm⟩

theorem ten_self_normalizing (B : Subgroup A6) (hB : Nat.card B = 10) :
    normalizer (B : Set A6) = B := by
  obtain ⟨P,rfl⟩ := ten_eq_five_normalizer B hB
  exact P.normalizer_normalizer

theorem ten_conjugate (B E : Subgroup A6) (hB : Nat.card B = 10)
    (hE : Nat.card E = 10) : ∃ g : A6, B.map (MulAut.conj g).toMonoidHom = E := by
  obtain ⟨P,hP⟩ := ten_eq_five_normalizer B hB
  obtain ⟨Q,hQ⟩ := ten_eq_five_normalizer E hE
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A6 P Q
  have he := congrArg (fun S : Sylow 5 A6 => (S : Subgroup A6)) hg
  change (P : Subgroup A6).map (MulAut.conj g).toMonoidHom = (Q : Subgroup A6) at he
  refine ⟨g,?_⟩
  rw [← hP,← hQ]
  change (normalizer ((P : Subgroup A6) : Set A6)).map _ =
    normalizer ((Q : Subgroup A6) : Set A6)
  rw [map_equiv_normalizer_eq,he]
end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
