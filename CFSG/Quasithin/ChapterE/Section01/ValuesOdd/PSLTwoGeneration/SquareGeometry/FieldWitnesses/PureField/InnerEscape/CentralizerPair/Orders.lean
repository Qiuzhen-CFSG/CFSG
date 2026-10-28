module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.FixedCentralizer
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

/-!
# Orders and Sylow placement for the subfield centralizer pair

The canonical inner extension has order p²(p⁴−1). The literal centralizer
of its pure field involution has index p(p²+1)/2, which is odd. Thus a Sylow
two-subgroup of that centralizer is a Sylow subgroup of the inner extension.
The same order calculation gives index two in the full semilinear group,
so projective conjugations preserve the specified inner model.

These are the Sylow-placement and conjugation-preservation inputs to the
subfield route for E.1.14(6), including p=3. Source: Aschbacher--Smith,
E.1.8 and E.1.14(6), printed pp.210--211 and 214 (citing Asc82a, 4.10).
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair
variable {F : Type*} [Field F] [Finite F]

/-- The order of the actual subgroup PSL₂(F)⟨σ⟩. -/
theorem innerModel_card {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    Nat.card (innerModel F σ) = p ^ 2 * (p ^ 4 - 1) := by
  have hlarge : 3 < Nat.card F := by rw [hF]; have := hp.two_le; nlinarith
  let : (pGammaL2PSLRange F).Normal :=
    pGammaL2PSLRange_normal F ⟨p, 2, hp, hodd, by decide, hF⟩ hlarge
  have hd : Disjoint (pGammaL2PSLRange F) (zpowers (SemidirectProduct.inr σ)) := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    rintro x ⟨hx, hxσ⟩
    obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff F x).mp hx
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hxσ
    have hs : σ ^ n = 1 := by
      have hh := congrArg SemidirectProduct.right (hn.trans hy.symm)
      simpa only [← map_zpow, SemidirectProduct.right_inr,
        SemidirectProduct.right_inl] using hh
    apply mem_bot.mpr
    rw [← hn, ← map_zpow, hs, map_one]
  rw [innerModel, card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (by rw [normalizer_eq_top]; exact le_top) hd,
    Nat.card_zpowers, orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective,
    hσ, ← Nat.card_congr (pGammaL2PSLRangeEquiv F).toEquiv]
  have h := ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (by rw [hF]; exact hodd.pow)
  rw [hF] at h
  simpa only [← pow_mul] using h

/-- The literal centralizer has index p(p²+1)/2. -/
theorem pureCentralizer_index_twice {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    (centralizer ({pure σ} : Set (innerModel F σ))).index * 2 = p * (p ^ 2 + 1) := by
  have h := (centralizer ({pure σ} : Set (innerModel F σ))).card_mul_index
  rw [pureCentralizer_card hp hodd hF σ hσ, innerModel_card hp hodd hF σ hσ] at h
  have hp2 := hp.two_le
  have hs : 1 < p ^ 2 := by nlinarith
  have he : p ^ 4 - 1 = (p ^ 2 - 1) * (p ^ 2 + 1) := by
    have hsub := Nat.sub_add_cancel hs.le
    have hfour : 1 ≤ p ^ 4 := by nlinarith
    have hsub4 := Nat.sub_add_cancel hfour
    nlinarith
  rw [he] at h
  have hn : 0 < p * (p ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.eq_of_mul_eq_mul_left hn
  nlinarith [h]

/-- The subfield centralizer has odd index, uniformly for all odd p. -/
theorem pureCentralizer_index_odd {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    Odd (centralizer ({pure σ} : Set (innerModel F σ))).index := by
  have h := pureCentralizer_index_twice hp hodd hF σ hσ
  have hpmod : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hemod : (p * (p ^ 2 + 1)) % 4 = 2 := by
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rw [Nat.mul_mod, Nat.add_mod, Nat.pow_mod]
    rcases hp4 with hp4 | hp4 <;> norm_num [hp4]
  rw [← h] at hemod
  exact Nat.odd_iff.mpr (by omega)

/-- A Sylow subgroup can be chosen inside the literal pure-field centralizer. -/
theorem exists_sylow_le_pureCentralizer {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)] :
    ∃ T : Sylow 2 (innerModel F σ),
      (T : Subgroup (innerModel F σ)) ≤ centralizer ({pure σ} : Set (innerModel F σ)) := by
  let C := centralizer ({pure σ} : Set (innerModel F σ))
  let R : Sylow 2 C := default
  have hidx : ¬ 2 ∣ ((R : Subgroup C).map C.subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul R.not_dvd_index
      (pureCentralizer_index_odd hp hodd hF σ hσ).not_two_dvd_nat
  exact ⟨(R.isPGroup'.map C.subtype).toSylow hidx, map_subtype_le _⟩

/-- The canonical inner model is normal in the full semilinear group. -/
theorem innerModel_normal {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    (innerModel F σ).Normal := by
  apply normal_of_index_eq_two
  have h := (innerModel F σ).card_mul_index
  rw [innerModel_card hp hodd hF σ hσ, SemidirectProduct.card,
    pgl2_card_formula, FiniteField.card_ringAut_of_card_prime_pow hp hF, hF] at h
  have hp2 := hp.two_le
  have hn : 0 < p ^ 2 * (p ^ 4 - 1) := by
    have hs : 1 < p ^ 2 := by nlinarith
    have hfour : 1 < p ^ 4 := by
      calc
        1 < (p ^ 2) ^ 2 := by nlinarith
        _ = p ^ 4 := by ring
    apply Nat.mul_pos (by nlinarith) (by omega)
  apply Nat.eq_of_mul_eq_mul_left hn
  simpa only [← pow_mul] using h

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair
