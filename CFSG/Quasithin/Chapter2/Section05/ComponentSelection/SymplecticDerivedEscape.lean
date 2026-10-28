module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticEscapeSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticBinaryEscape
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticDerivedSource
/-!
# The complete derived-symplectic escaping source family

At field two, the literal derived carrier is A₆ and its original source
Borel identity forces innerness of the mark. At larger fields, root generation
identifies the derived and full symplectic carriers, with trivial center.
Both branches therefore construct the required escaping component join from
the original saturated local pair, preserving Γ₀ and both star families.

Source: Aschbacher–Smith, 2.5.2(2) and 2.5.3(4), printed pp.551–553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}
theorem derived_symplectic_escaping_source
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type) [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : D ≃* commutator (Sp F))
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  by_cases hk1 : k = 1
  · have hc : Nat.card F = 2 := by simpa [hk1] using hF
    exact alternating_six_escaping_source hG T₀ hM hT₀M hunique hH hempty B hp hBH hHnorm
      hpair hbig hsat S hUS D hD (e.trans (Binary.derivedEquivAlternatingSix hc)) hout
  · have hk2 : 2 ≤ k := by omega
    let : CharP F 2 := EvenProjective.charTwo_of_card hF
    have hpow : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk2
    let j := e.trans (derivedEquivFull_of_card_gt_two (by omega : 2 < Nat.card F))
    have hz : center D = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      have hb : j a ∈ center (Sp F) := ((centerCongr j) ⟨a,ha⟩).property
      have hb1 : j a = 1 := mem_bot.mp ((EvenProjective.center_eq_bot (F := F)) ▸ hb)
      exact mem_bot.mpr (j.injective (hb1.trans (map_one j).symm))
    let q : D ⧸ center D ≃* Sp F :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans j
    exact symplectic_escaping_source hG T₀ hM hT₀M hunique hH B hp hBH hHnorm
      hpair hbig hsat S hUS D hD F hk2 hF (q.trans EvenProjective.equiv) hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
