module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.TwoPowerActors
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# The index-three obstruction for symplectic Borel actors

A two-power automorphism of the rank-two split torus arising from a Borel
actor cannot fix an index-three subgroup pointwise unless its torus action
is trivial. The fixed subgroup bounds the displacement image by three.
The three-residual calculation reduces a nontrivial actor to degrees two
and six, where the displacement image has order greater than three.

We supply the automorphism-classification premise from the proved
inner-field theorem. The quotient form below retains an arbitrary kernel
in the acting group and the two-core of the centralized subgroup.

Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928.
The imported intrinsic torus calculations do not use Chapter 13 theorems.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CubicInverter
open ActorReduction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- This includes every degree greater than one, including degrees two and six. -/
theorem torus_eq_one_of_index_three_fixer {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (τ : MulAut (Fˣ × Fˣ)) (hτ : τ ∈ zpowers (graphTorus (F := F)))
    (hp : IsPGroup 2 (zpowers τ)) (C : Subgroup (Fˣ × Fˣ))
    (hi : C.index = 3) (hfix : ∀ c ∈ C, τ c = c) : τ = 1 := by
  by_contra hne
  have hC : pResidual 3 (Fˣ × Fˣ) ≤ C := by
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    simpa only [← C.index_eq_card, pow_one] using hi
  have hdeg := two_power_fixed_residual_degree hn hF τ hτ hp hne
    (fun c hc => hfix c (hC hc))
  have hgt := two_power_displacement_gt_three hF τ hτ hp hne hdeg
  have hle : C ≤ (torusDisplacement τ).ker := by
    intro c hc
    change τ c * c⁻¹ = 1
    rw [hfix c hc, mul_inv_cancel]
  have hcard := index_antitone hle
  rw [index_ker, hi] at hcard
  omega


/-- The exact odd quotient of a Borel, including a possibly nonfaithful actor.
Centralization modulo O₂(C) suffices: its image in the odd torus is trivial. -/
theorem action_eq_one_of_index_three_fixer {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n)
    (a : ActorReduction.stabilizer (F := F)) (hp : IsPGroup 2 (zpowers a))
    {B : Type*} [Group B] [Finite B]
    (q : B →* Fˣ × Fˣ) (hq : Function.Surjective q)
    (β : MulAut B) (heq : ∀ b, q (β b) = torusAction hF a (q b))
    (C : Subgroup B) (hi : (C ⊔ q.ker).index = 3)
    (hfix : ∀ c ∈ C, c⁻¹ * β c ∈ C.pCoreIn 2) :
    torusAction hF a = 1 := by
  apply torus_eq_one_of_index_three_fixer hn hF _
    (torusAction_mem_graph hF hn
      DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram a)
    (C := C.map q)
  · have ht := hp.map (torusAction hF)
    rw [MonoidHom.map_zpowers] at ht
    exact ht
  · rw [index_map, q.range_eq_top_of_surjective hq, index_top, mul_one]
    exact hi
  · rintro x ⟨c, hc, rfl⟩
    rw [← heq]
    have hk := Theory.GroupAction.OddCommutatorImage.twoCore_le_ker
      (q.comp C.subtype) (Nat.coprime_two_left.mp (torus_odd hF))
    obtain ⟨d, hd, he⟩ := hfix c hc
    have heq := congrArg q he
    have hd' := hk hd
    change q (C.subtype d) = 1 at hd'
    rw [hd', map_mul, map_inv] at heq
    exact (inv_mul_eq_one.mp heq.symm).symm

/-- An actual inverted cubic image contradicts the index-three fixer. -/
theorem no_cubic_inverter {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (a : ActorReduction.stabilizer (F := F)) (hp : IsPGroup 2 (zpowers a))
    {B : Type*} [Group B] [Finite B]
    (q : B →* Fˣ × Fˣ) (hq : Function.Surjective q)
    (β : MulAut B) (heq : ∀ b, q (β b) = torusAction hF a (q b))
    (C : Subgroup B) (hi : (C ⊔ q.ker).index = 3)
    (hfix : ∀ c ∈ C, c⁻¹ * β c ∈ C.pCoreIn 2)
    (b : B) (horder : orderOf (q b) = 3) (hinv : q (β b) = (q b)⁻¹) : False := by
  have ht := action_eq_one_of_index_three_fixer hn hF a hp q hq β heq C hi hfix
  have he : q b = (q b)⁻¹ := by simpa only [heq, ht, MulAut.one_apply] using hinv
  have hs : (q b)^2 = 1 := by
    calc
      _ = q b * q b := pow_two _
      _ = q b * (q b)⁻¹ := congrArg (fun x => q b * x) he
      _ = 1 := mul_inv_cancel _
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [horder] at hd
  norm_num at hd

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CubicInverter
