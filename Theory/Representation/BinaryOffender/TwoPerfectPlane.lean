module

public import Theory.Representation.BinaryPlaneNormalizer
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.CyclicFixedRank
public import Theory.GroupTheory.TwoPerfectSmallAction

/-!
# Offender displacement in a nontrivial two-perfect binary plane

An order-two offender has at most one-dimensional displacement. If a
two-perfect group normalizes that offender, it fixes its displacement line.
A nonzero vector fixed in an invariant binary plane forces the two-perfect
action on that plane to be trivial. Consequently an offender whose nonzero
displacement lies in a nontrivial such plane cannot be normalized.

Source: the last contradiction in Aschbacher–Smith13.7.14, printed p.943.
-/

public section

open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The source binary-plane obstruction, retaining the specified action,
plane, normalizer and offender. -/
theorem not_normalized_order_two_offender_in_plane
    (hρ : Function.Injective ρ) {K B : Subgroup G} (hK : IsPPerfect 2 K)
    (P : Submodule (ZMod 2) V) (hP : K ≤ subspaceStabilizer ρ P)
    (hd : Module.finrank (ZMod 2) P = 2) (hn : ¬ P ≤ fixedSpace ρ K)
    (hB : IsOffender ρ B) (hc : Nat.card B = 2)
    (hmove : subspaceCommutator ρ ⊤ B ≤ P) :
    ¬ K ≤ normalizer (B : Set G) := by
  intro hKB
  let W := subspaceCommutator ρ ⊤ B
  obtain ⟨b,hb⟩ := B.isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card hc)
  have hdim : Module.finrank (ZMod 2) W ≤ 1 := by
    have he := fixedCodim_zpowers_eq_displacement_rank ρ b
    rw [hb] at he
    rw [show W = LinearMap.range (ρ b - LinearMap.id) from
      by dsimp only [W]; rw [← hb]; exact Representation.CyclicFixedRank.commutator_eq_range ρ b, ← he]
    simpa only [rank,hc,show Nat.log 2 2 = 1 from by decide] using hB.2
  have hW : K ≤ subspaceStabilizer ρ W :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤
      (fun _ _ _ _ => Submodule.mem_top)) hKB
  have hWne : W ≠ ⊥ := by
    intro hz
    have hfix := (subspaceCommutator_eq_bot_iff ρ ⊤ B).mp hz
    apply hB.1.1
    apply eq_bot_iff.mpr
    intro b hb
    change b = 1
    apply hρ
    ext v
    exact (hfix Submodule.mem_top ⟨b,hb⟩).trans (by simp)
  have hex : ∃ w : V, w ∈ W ∧ w ≠ 0 := by
    by_contra! hzero
    exact hWne (eq_bot_iff.mpr (fun w hw => (Submodule.mem_bot (ZMod 2)).mpr (hzero w hw)))
  obtain ⟨w,hw,hwne⟩ := hex
  let τ : Representation (ZMod 2) K W := Representation.subrepresentation (ρ.comp K.subtype) W
    (fun k v hv => (hW k.property v).2 hv)
  let : MulAction K W := {
    smul := fun k v => τ k v
    one_smul := fun v => by change τ 1 v = v; rw [map_one]; rfl
    mul_smul := fun k l v => by change τ (k*l) v = τ k (τ l v); rw [map_mul]; rfl }
  have hcard : Nat.card W ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim).trans_eq (by decide)
  let : Finite W := Module.finite_of_finite (ZMod 2)
  have hfixw (k : K) : ρ k w = w := congrArg Subtype.val
    (MulAction.fixed_of_twoPerfect_of_card_le_two hK hcard k (⟨w,hw⟩ : W))
  let σ : Representation (ZMod 2) K P := Representation.subrepresentation (ρ.comp K.subtype) P
    (fun k v hv => (hP k.property v).2 hv)
  have htriv := BinaryPlaneNormalizer.twoPerfect_plane_fixed σ hK hd
    (⟨w,hmove hw⟩ : P) (fun he => hwne (congrArg Subtype.val he))
    (fun k => Subtype.ext (hfixw k))
  apply hn
  intro v hv k
  exact congrArg Subtype.val (LinearMap.congr_fun (htriv k) (⟨v,hv⟩ : P))

end Representation.BinaryOffender
