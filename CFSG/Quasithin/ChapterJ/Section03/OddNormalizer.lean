module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.OddPrimeCompletion
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.LocalSource
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Odd-prime normalizer orders in the source Ru configuration

The literal centralizer of an embedded Sylow seven- or thirteen-subgroup is
its direct product with the original four-group S₀. Kernel and image counting
for the normalizer action gives order 4p(p−1). The Sylow congruence consequently
gives the precise congruence modulo 169 used in the J.3 order argument.

The only earlier input is the actual J.2.9 Suzuki conclusion; J.2.10 supplies
its normalizer action and centralizer on the original ambient subgroup.
Source: Aschbacher--Smith J.2.10 and J.3.1, printed pp.438--439.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

theorem prime_normalizer_card (c : Choices d) (r : c.SuzukiSourceConclusion)
    {p : ℕ} [Fact p.Prime] (hp : p=7 ∨ p=13) (Y : Sylow p c.Ls) :
    let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
    Nat.card YG = p ∧ Nat.card (normalizer (YG : Set G)) = p*4*(p-1) := by
  let := c.S0_elementary_source
  let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
  obtain ⟨hY,_,_,hC,_,hA⟩ := r.oddPrime_source_conclusions c hp Y
  have h4 : Nat.card c.S0 = 4 := c.S0_card_source
  have hYL : YG ≤ c.Ls := map_subtype_le _
  have hn : c.S0 ≤ normalizer (YG : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact r.central.trans (centralizer_le hYL)
  have hd : Disjoint YG c.S0 := disjoint_of_coprime_natCard (by
    rw [hY,h4]
    rcases hp with rfl | rfl <;> decide)
  have hcardC : Nat.card (centralizer (YG : Set G)) = p*4 := by
    rw [hC,card_sup_eq_mul_of_normalizes_of_disjoint YG c.S0 hn hd,hY,h4]
  have hk : Nat.card YG.normalizerMonoidHom.ker = Nat.card (centralizer (YG : Set G)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (YG : Set G))).toEquiv]
  have he := YG.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hk,hcardC,hA] at he
  exact ⟨hY,he.symm⟩

/-- The original Sylow-thirteen subgroup gives the source congruence modulo169. -/
theorem card_mod_thirteen_square (c : Choices d) (r : c.SuzukiSourceConclusion) :
    Nat.ModEq (13^2) (Nat.card G) (13*48) := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let Y : Sylow 13 c.Ls := Classical.choice inferInstance
  let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
  obtain ⟨hY,hN⟩ := prime_normalizer_card c r (Or.inr rfl) Y
  have he := Sylow.card_normalizer_modEq_card (p:=13) (n:=1)
    (H:=YG) (by simpa only [pow_one] using hY)
  rw [hN] at he
  exact he.symm

theorem prime_dvd_card (c : Choices d) (r : c.SuzukiSourceConclusion)
    {p : ℕ} [Fact p.Prime] (hp : p=7 ∨ p=13) : p ∣ Nat.card G := by
  let Y : Sylow p c.Ls := Classical.choice inferInstance
  obtain ⟨hY,_⟩ := prime_normalizer_card c r hp Y
  rw [← hY]
  exact ((Y : Subgroup c.Ls).map c.Ls.subtype).card_subgroup_dvd_card

end CFSG.Quasithin.ChapterJ.Section03
