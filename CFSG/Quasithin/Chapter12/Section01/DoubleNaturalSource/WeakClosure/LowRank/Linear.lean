module
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Common involution fixed spaces on dual binary modules

Evaluation at a nonfixed vector embeds an actor with common nonidentity
fixed spaces into its displacement space. Duality identifies that dimension
with the dual fixed codimension. If the same fixed-space condition holds
on the dual module, an involution bounds the actor rank by half the natural
dimension. This is the low-image-rank step of 12.1.8.
Source: Aschbacher--Smith, printed pp.792--793 (PDF809--810).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {K X : Type*} [Group K] [Finite K] [AddCommGroup X]
  [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

omit [Finite K] in
/-- If every nonidentity actor has the common fixed space, evaluation at
a nonfixed vector embeds the actor into the displacement space. -/
theorem rank_le_dual_fixedCodim_of_common_fixed
    (ρ : Representation (ZMod 2) K X) (hf : Function.Injective ρ)
    (hc : ∀ a : K, a ≠ 1 → fixedSpace ρ (zpowers a) ≤ fixedSpace ρ ⊤) :
    rank (⊤ : Subgroup K) ≤ fixedCodim ρ.dual ⊤ := by
  by_cases ht : (⊤ : Subgroup K) = ⊥
  · simp [ht, rank]
  have hp := fixedCodim_pos_of_faithful ρ hf ht
  have hne : fixedSpace ρ ⊤ ≠ ⊤ := by
    intro he
    have hs := fixedCodim_add_finrank ρ ⊤
    rw [he, finrank_top] at hs
    omega
  obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top _ hne
  let C := Coinvariants.ker ρ
  let d (a : K) : C := ⟨ρ a v - v, Coinvariants.sub_mem_ker a v⟩
  have hinj : Function.Injective d := by
    intro a b hab
    have he : ρ a v = ρ b v := sub_left_injective (congrArg Subtype.val hab)
    by_contra hn
    have hab1 : b⁻¹ * a ≠ 1 := by
      intro hh
      apply hn
      simpa only [mul_inv_cancel_left, mul_one] using congrArg (b * ·) hh
    have hvfix : v ∈ fixedSpace ρ (zpowers (b⁻¹ * a)) := by
      rw [mem_fixedSpace_zpowers_iff, map_mul, Module.End.mul_apply, he,
        ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    exact hv (hc _ hab1 hvfix)
  let : Finite C := Module.finite_of_finite (ZMod 2)
  have hb := Nat.log_mono_right (b := 2) (Nat.card_le_card_of_injective d hinj)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C), Nat.card_zmod,
    Nat.log_pow (by decide)] at hb
  have hd : fixedCodim ρ.dual ⊤ = Module.finrank (ZMod 2) C := by
    rw [fixedCodim_dual_eq_moved_finrank, subspaceCommutator_top_eq_coinvariants]
    have he : Coinvariants.ker (ρ.comp (⊤ : Subgroup K).subtype) = C := by
      unfold Coinvariants.ker C
      congr 1
      ext w
      constructor
      · rintro ⟨⟨a,x⟩,rfl⟩
        exact ⟨(a.val,x),rfl⟩
      · rintro ⟨⟨a,x⟩,rfl⟩
        exact ⟨(⟨a,Subgroup.mem_top a⟩,x),rfl⟩
    rw [he]
  simpa [rank, hd] using hb

/-- Common fixed spaces on both dual summands force an elementary actor
to have rank at most half the natural dimension. -/
theorem rank_bound_of_common_dual_fixed [IsElementaryAbelian 2 K]
    (ρ : Representation (ZMod 2) K X) (hf : Function.Injective ρ)
    (hc : ∀ a : K, a ≠ 1 → fixedSpace ρ (zpowers a) ≤ fixedSpace ρ ⊤)
    (hd : ∀ a : K, a ≠ 1 → fixedSpace ρ.dual (zpowers a) ≤ fixedSpace ρ.dual ⊤) :
    2 * rank (⊤ : Subgroup K) ≤ Module.finrank (ZMod 2) X := by
  by_cases htr : ∀ a : K, a = 1
  · have ht : (⊤ : Subgroup K) = ⊥ := by
      ext a
      simp [htr a]
    simp [ht, rank]
  push Not at htr
  obtain ⟨a,ha⟩ := htr
  have ho : orderOf a = 2 := orderOf_eq_prime
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 K) a) ha
  have he : fixedSpace ρ.dual (zpowers a) = fixedSpace ρ.dual ⊤ :=
    le_antisymm (hd a ha) (fun v hv b => hv ⟨b,Subgroup.mem_top _⟩)
  have hr := rank_le_dual_fixedCodim_of_common_fixed ρ hf hc
  have hi := (involution_actor_rank_and_fixedCodim ρ.dual a ho).2.2.2
  have hdims : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) X) =
      Module.finrank (ZMod 2) X := Subspace.dual_finrank_eq
  rw [hdims] at hi
  unfold fixedCodim at hr hi
  rw [he] at hi
  omega
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
