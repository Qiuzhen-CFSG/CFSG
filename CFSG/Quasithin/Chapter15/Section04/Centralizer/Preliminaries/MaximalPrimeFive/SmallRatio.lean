module
public import Theory.Representation.CyclicPrimeSmallRatio
public import Theory.Representation.BinaryGroupAction
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportOrders

/-!
# The small-support prime bound used in 15.4.3(4)

A self-centralizing normal subgroup of odd prime order makes every nontrivial
elementary two-actor cyclic. The actual cubic-ratio minimum supplies such an
involution with fixed codimension at most two. The binary group-action transport
identifies its support, and the proved D.2.11 small-support theorem gives the
prime three or five. No general minimal-offender inheritance is required.
-/
noncomputable section
open Subgroup BenderSuzuki.PFAppendixIII Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeFive
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]

private theorem involution_moved_eq_range (ρ : Representation (ZMod 2) D V)
    (t : D) (ht : BenderSuzuki.PFAppendixIII.IsInvolution t) :
    subspaceCommutator ρ ⊤ (zpowers t) = LinearMap.range (ρ t - LinearMap.id) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    have hoa : orderOf t = 2 := orderOf_eq_prime ht.sq_eq_one ht.ne_one
    rw [mem_zpowers_iff_mem_range_orderOf, hoa] at ha
    have he : a = 1 ∨ a = t := by
      obtain ⟨n, hn, he⟩ := Finset.mem_image.mp ha
      have hn2 : n = 0 ∨ n = 1 := by have := Finset.mem_range.mp hn; omega
      rcases hn2 with rfl | rfl
      · exact Or.inl (by simpa using he.symm)
      · exact Or.inr (by simpa using he.symm)
    rcases he with rfl | rfl
    · simp only [map_one, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _
    · exact ⟨v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨t, mem_zpowers t, v, Submodule.mem_top, rfl⟩

/-- The actual odd prime is three or five. This applies the proved Chapter D
small-support theorem to the literal involution and prime-element witnesses. -/
public theorem prime_three_or_five_of_cubicRatio [Finite V]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (P : Subgroup D) [P.Normal] (hP : Nat.card P = p)
    (hC : centralizer (P : Set D) ≤ P)
    (ρ : Representation (ZMod 2) D V) (hfaith : Function.Injective ρ)
    (hratio : cubicRatio ρ ≤ 2) : p = 3 ∨ p = 5 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, x, ht, _, hx, hinv, hsmall⟩ :=
    Representation.CyclicPrimeSmallRatio.exists_small_inverter (hp.odd_of_ne_two hodd) P hP hC ρ hratio
  let := Representation.BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := Representation.BinaryGroupAction.elementary
  let : FaithfulSMul D (Multiplicative V) := Representation.BinaryGroupAction.faithful ρ hfaith
  have hfix : fixingSubgroup D (Set.univ : Set (Multiplicative V)) = ⊥ := by
    apply bot_unique
    intro g hg
    apply mem_bot.mpr
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Multiplicative V)
    intro v
    exact (hg ⟨v, Set.mem_univ v⟩).trans (one_smul D v).symm
  have hcard : Nat.card (commutatorAction (zpowers t) (Multiplicative V)) ≤ 4 := by
    rw [Representation.BinaryGroupAction.commutator_card, involution_moved_eq_range ρ t ht,
      ← fixedCodim_zpowers_eq_displacement_rank]
    calc
      2 ^ fixedCodim ρ (zpowers t) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hsmall
      _ = 4 := by decide
  have hxne : x ≠ 1 := by
    intro he
    have hp1 : p = 1 := by simpa [he] using hx.symm
    exact hp.ne_one hp1
  have ho : Odd (orderOf x) := by rw [hx]; exact hp.odd_of_ne_two hodd
  simpa only [hx] using ChapterD.invertedOddElement_order_three_or_five_of_small_involution_support
    (V := Multiplicative V) x t hxne ho ht hinv hcard hfix
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeFive
