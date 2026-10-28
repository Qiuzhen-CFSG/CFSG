module

public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.GroupTheory.TwoRankFourthPower
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.Representation.BinaryPrimeDegree

/-!
# The M₁₁ and J₁ inputs to G.7

Both actual source carriers have an element of order eleven. Their certified
orders and inner automorphism theorems give the required automorphism two-rank
bounds. For M₁₁ the semidihedral Sylow subgroup even gives rank at most two:
its element of order eight rules out elementary subgroups of index at most two.
For J₁ the two-part of the order is eight.

The applications retain the literal central quotient of the source component.
Divisibility lifts through that quotient and the subgroup inclusion; faithful
automorphism descent for perfect groups transports the rank estimate to the
cover. No identification of a cover with its central quotient is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.2(1) and
the discarded M₁₁/J₁ cases of G.7.3(2), printed pp.347--348 (PDF pp.358--359).
-/

public section
namespace CFSG.Quasithin.ChapterG.Section07.SporadicLocal
open Theory.GroupTheory Sporadic.Mathieu Subgroup

/-- Eleven divides the order of the concrete Witt-design M₁₁. -/
theorem m11_eleven_dvd_card : 11 ∣ Nat.card M11 := by
  rw [m11_order]
  norm_num

/-- Eleven divides the order of the concrete seven-dimensional J₁ model. -/
theorem j1_eleven_dvd_card : 11 ∣ Nat.card Janko1.Model := by
  rw [Janko1.card_model]
  norm_num

private theorem m11_twoRank_le_two : primeRank 2 M11 ≤ 2 := by
  obtain ⟨P, a, _, ha, _, _, _⟩ := m11_exists_semidihedral_sylow
  rw [P.primeRank_eq]
  have hcard : Nat.card P = 2 ^ (2 + 2) := by
    rw [P.card_eq_multiplicity, m11_order]
    decide +kernel
  have hx : a ^ 4 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha] at hd
    norm_num at hd
  exact twoRank_le_of_card_pow_and_fourth_ne 2 hcard a hx

/-- The automorphism two-rank bound used to discard M₁₁ in G.7.3(2). -/
theorem m11_automorphism_twoRank_le_three : primeRank 2 (MulAut M11) ≤ 3 := by
  let e : M11 ≃* MulAut M11 := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot m11_center_eq_bot,
      fun f => m11_automorphism_inner f⟩
  rw [← primeRank_equiv 2 e]
  exact m11_twoRank_le_two.trans (by decide)

/-- The automorphism two-rank bound used to discard J₁ in G.7.3(2). -/
theorem j1_automorphism_twoRank_le_three : primeRank 2 (MulAut Janko1.Model) ≤ 3 := by
  let P : Sylow 2 Janko1.Model := Classical.choice inferInstance
  apply automorphism_primeRank_le_of_prime_order_inner P
  · rw [P.card_eq_multiplicity, Janko1.card_model]
    decide +kernel
  · intro f _
    exact Janko1.OuterCertificate.aut_inner f

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
private theorem eleven_dvd_of_subgroup_centralQuotient
    {S : Type*} [Group S] (hS : 11 ∣ Nat.card S)
    (L : Subgroup G) (e : L ⧸ center L ≃* S) : 11 ∣ Nat.card G := by
  have hquot : 11 ∣ Nat.card (L ⧸ center L) := by
    rw [Nat.card_congr e.toEquiv]
    exact hS
  exact (hquot.trans (center L).card_quotient_dvd_card).trans L.card_subgroup_dvd_card

/-- G.7.2(1) for a component with central quotient M₁₁, in the original
faithful ambient representation. -/
theorem m11_centralQuotient_finrank_ge_ten
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (L : Subgroup G) (e : L ⧸ center L ≃* M11) :
    10 ≤ Module.finrank (ZMod 2) V := by
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] using
    Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ
      (by decide : Nat.Prime 11) (by decide : 11 ≠ 2)
      (eleven_dvd_of_subgroup_centralQuotient m11_eleven_dvd_card L e)

/-- G.7.2(1) for a component with central quotient J₁, in the original
faithful ambient representation. -/
theorem j1_centralQuotient_finrank_ge_ten
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (L : Subgroup G) (e : L ⧸ center L ≃* Janko1.Model) :
    10 ≤ Module.finrank (ZMod 2) V := by
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] using
    Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ
      (by decide : Nat.Prime 11) (by decide : 11 ≠ 2)
      (eleven_dvd_of_subgroup_centralQuotient j1_eleven_dvd_card L e)

variable {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

/-- The M₁₁ automorphism bound also applies to the actual perfect central cover. -/
theorem m11_centralQuotient_automorphism_twoRank_le_three
    (e : L ⧸ center L ≃* M11) : primeRank 2 (MulAut L) ≤ 3 := by
  have h := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at h
  exact h.trans m11_automorphism_twoRank_le_three

/-- The J₁ automorphism bound also applies to the actual perfect central cover. -/
theorem j1_centralQuotient_automorphism_twoRank_le_three
    (e : L ⧸ center L ≃* Janko1.Model) : primeRank 2 (MulAut L) ≤ 3 := by
  have h := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at h
  exact h.trans j1_automorphism_twoRank_le_three

end CFSG.Quasithin.ChapterG.Section07.SporadicLocal
