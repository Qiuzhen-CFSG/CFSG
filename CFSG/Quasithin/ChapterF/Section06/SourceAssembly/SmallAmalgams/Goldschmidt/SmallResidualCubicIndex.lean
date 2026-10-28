module
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PResidual.SupplementCommutator
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.TwoPerfectOrderTwelve
public import Mathlib.GroupTheory.IndexNormal

/-!
# A small cubic commutator determines the local two-residual

Let Q = O₂(H), assume H/Q is S₃, and choose an actual element x of order
three. The subgroup Q⟨x⟩ has index two, hence has the same embedded
two-residual as H. The residual supplement formula identifies that residual
with ⟨x⟩[Q,⟨x⟩]. If the latter commutator has order at most four, its
possible orders are one, two and four. Two-perfectness excludes residual
order six; the remaining orders three and twelve give C₃ and A₄.

The literal commutator and the chosen cubic element are retained for the
outside-involution argument in Goldschmidt (4.2). No local recognition map
or additional normality premise is assumed.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.2),
printed pp.392--393; the residual and order-twelve recognition are reused
from the general finite-group library.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {H : Type*} [Group H] [Finite H]

private theorem twoPerfect_card_ne_six (h : IsPPerfect 2 H) : Nat.card H ≠ 6 := by
  intro hc
  let P : Sylow 3 H := Sylow.nonempty.some
  have hPc : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hc]
    change 3 ^ (Nat.factorization (2 * 3) 3) = 3
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hPi : (P : Subgroup H).index = 2 := by
    have hh := (P : Subgroup H).index_mul_card
    rw [hPc, hc] at hh
    omega
  let hn : (P : Subgroup H).Normal := normal_of_index_eq_two hPi
  have ht := h P hn (IsPGroup.of_card (n := 1)
    (by simpa only [← index_eq_card, pow_one] using hPi))
  have hh := index_eq_one.mpr ht
  omega

omit [Finite H] in
private theorem cubic_isTwoPerfect (x : H) (hx : orderOf x = 3) :
    IsPPerfect 2 (zpowers x) := by
  apply (pResidual_eq_top_iff 2 _).mp
  apply top_unique
  intro y _
  apply mem_pResidual_of_orderOf_coprime
  have hc : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    (hc ▸ orderOf_dvd_natCard y)

/-- A cubic commutator of order at most four forces the original local
two-residual to be C₃ or A₄. -/
theorem residual_cubic_or_alternatingFour_of_small_cubic_commutator
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (x : H) (hx : orderOf x = 3)
    (hsmall : Nat.card (⁅pCore 2 H, zpowers x⁆ : Subgroup H) ≤ 4) :
    Nonempty ((pResidual 2 H) ≃* Multiplicative (ZMod 3)) ∨
      Nonempty ((pResidual 2 H) ≃* alternatingGroup (Fin 4)) := by
  let Q := pCore 2 H
  let X := zpowers x
  let C := ⁅Q, X⁆
  let J := Q ⊔ X
  have hXc : Nat.card X = 3 := by rw [Nat.card_zpowers, hx]
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hXc)
  have hQp : IsPGroup 2 Q := pCore_isPGroup
  have hd : Disjoint Q X := hQp.disjoint_of_coprime hXp (by decide)
  have hJc : Nat.card J = Nat.card Q * 3 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Q X le_normalizer_of_normal hd, hXc]
  have hJi : J.index = 2 := by
    have hh := J.index_mul_card
    rw [hJc, SymmetricThreeTwoCore.card_eq e] at hh
    have hqpos := Nat.card_pos (α := Q)
    nlinarith
  let hJn : J.Normal := normal_of_index_eq_two hJi
  have hrJ : pResidual 2 H ≤ J := sInf_le ⟨hJn,
    IsPGroup.of_card (n := 1) (by simpa only [← index_eq_card, pow_one] using hJi)⟩
  have htop : (pResidual 2 (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype =
      pResidual 2 H := map_pResidual 2 Subgroup.topEquiv
  have hemb : (pResidual 2 J).map J.subtype = pResidual 2 H := by
    exact (embedded_pResidual_eq_of_le_of_residual_le 2
      (show J ≤ (⊤ : Subgroup H) from le_top) (htop.symm ▸ hrJ)).trans htop
  have hr : pResidual 2 H = X ⊔ C := by
    rw [← hemb]
    exact embedded_pResidual_sup_eq_sup_commutator Q X hQp (cubic_isTwoPerfect x hx)
  have hCQ : C ≤ Q := commutator_le_left _ _
  have hCp : IsPGroup 2 C := hQp.to_le hCQ
  have hCcop : Nat.Coprime (Nat.card C) 3 := by
    obtain ⟨n, hn⟩ := hCp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hCc : Nat.card C = 1 ∨ Nat.card C = 2 ∨ Nat.card C = 4 := by
    have hpos := Nat.card_pos (α := C)
    change Nat.card C ≤ 4 at hsmall
    interval_cases hc : Nat.card C <;> norm_num [hc] at *
  have hcount : Nat.card (pResidual 2 H) = Nat.card C * 3 := by
    rw [hr, sup_comm, card_sup_eq_mul_of_normalizes_of_disjoint C X
      (normalizer_commutator_ge_right Q X) (hd.mono_left hCQ), hXc]
  rcases hCc with h1 | h2 | h4
  · exact Or.inl ⟨mulEquivOfPrimeCardEq (by simpa only [h1, one_mul] using hcount)
      (by simp)⟩
  · exact (twoPerfect_card_ne_six (isPPerfect_pResidual 2)
      (by simpa only [h2] using hcount)).elim
  · exact Or.inr (alternatingFour_of_twoPerfect_card_twelve (isPPerfect_pResidual 2)
      (by simpa only [h4] using hcount))

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
