module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic

/-!
# The three-part deduction in the ordinary M₂₂ branch

A two-group kernel preserves the three-adic valuation of group order.
Thus actual placement of L₁ in the native partition stabilizer, whose
order is 384, gives |L₁|₃ = 3. The nonzero lower bound comes from theta
and the nontrivial seed action, not an assumed rank-one statement.
The earlier order-nine quotient in the covered-A₆ case then excludes
that case.

Source: Aschbacher–Smith, 13.8.21(2), p.956; the local quotient alternatives
in Notation 13.2.1 and the proof of 13.7.5, p.938. These are conditional
transport deductions; construction of the placement remains separate.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M22ValueBound.Concrete
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement

variable {G : Type*} [Group G] [Finite G]

/-- Restriction of the chosen intrinsic component coordinates to a source subgroup. -/
noncomputable def markedMap (K X : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (hXK : X ≤ K) : X →* M22 := (componentMap K e).comp (inclusion hXK)

/-- The marked subgroup is mapped through O₂(K), not through O₂(X). -/
noncomputable def markedImage (K X : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22) :
    Subgroup M22 := (X.subgroupOf K).map (componentMap K e)

omit [Finite G] in
theorem markedMap_range (K X : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (hXK : X ≤ K) : (markedMap K X e hXK).range = markedImage K X e := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨inclusion hXK x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, hx⟩, rfl⟩

omit [Finite G] in
theorem markedMap_kernel_isTwoGroup (K X : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (hXK : X ≤ K) :
    IsPGroup 2 (markedMap K X e hXK).ker := by
  have hk : (markedMap K X e hXK).ker = (pCore 2 K).comap (inclusion hXK) := by
    rw [markedMap, ← MonoidHom.comap_ker, componentMap_ker]
  rw [hk]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hXK)

private theorem three_factorization_of_two_kernel {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (f : A →* B) (hk : IsPGroup 2 f.ker) :
    (Nat.card A).factorization 3 = (Nat.card f.range).factorization 3 := by
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  rw [← f.ker.card_mul_index, index_ker, hn,
    Nat.factorization_mul (pow_ne_zero n (by decide)) Nat.card_pos.ne']
  simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]

/-- In particular the source subgroup and its actual native image have equal three-parts. -/
theorem markedImage_three_factorization (K X : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (hXK : X ≤ K) :
    (Nat.card X).factorization 3 = (Nat.card (markedImage K X e)).factorization 3 := by
  rw [← markedMap_range K X e hXK]
  exact three_factorization_of_two_kernel _ (markedMap_kernel_isTwoGroup K X e hXK)

omit [Finite G] in
/-- A nontrivial theta seed has three-divisible order. -/
theorem three_dvd_seed (H M L₁ V₃ : Subgroup G)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hne : V₃ ≠ ⊥) (hgen : ⁅V₃, L₁⁆ = V₃) : 3 ∣ Nat.card L₁ := by
  by_contra hn
  have hbot : L₁ = ⊥ := by
    rw [htheta]
    apply le_antisymm _ bot_le
    apply (closure_le _).mpr
    intro x hx
    have hxL : x ∈ L₁ := htheta.symm ▸ subset_closure hx
    have ho : orderOf (⟨x, hxL⟩ : L₁) = 3 := (orderOf_coe _).symm.trans hx.2
    exact (hn (ho ▸ orderOf_dvd_natCard (⟨x, hxL⟩ : L₁))).elim
  rw [hbot, commutator_bot_right] at hgen
  exact hne hgen.symm

/-- This is the exact cardinal three-part, not just three-rank one. -/
theorem three_part_of_marked_placement (K L₁ : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (hL : L₁ ≤ K)
    (hplacement : markedImage K L₁ e ≤ second) (hthree : 3 ∣ Nat.card L₁) :
    3 ^ (Nat.card L₁).factorization 3 = 3 := by
  have he := markedImage_three_factorization K L₁ e hL
  have hd : 3 ∣ Nat.card (markedImage K L₁ e) := by
    apply (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mpr
    rw [← he]
    exact (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hthree
  rw [he]
  exact Native.three_part_of_le_partition _ hplacement hd

/-- The setup supplies theta; only the still-to-be-constructed geometric placement
and the genuine earlier seed action are needed for this arithmetic deduction. -/
theorem Setup.three_part {H K L₁ T G₁ M : Subgroup G}
    (s : Setup H K L₁ T G₁ M) (V₃ : Subgroup G) (hne : V₃ ≠ ⊥)
    (hgen : ⁅V₃, L₁⁆ = V₃) (hplacement : markedImage K L₁ s.model ≤ second) :
    3 ^ (Nat.card L₁).factorization 3 = 3 :=
  three_part_of_marked_placement K L₁ s.model s.seed_le_component hplacement
    (three_dvd_seed H M L₁ V₃ s.theta hne hgen)

/-- The order calculation is independent of which maximal-parabolic class
is chosen in the hexad quotient. This version uses the actual overlap. -/
theorem Setup.three_part_of_overlap_card {H K L₁ T G₁ M : Subgroup G}
    (s : Setup H K L₁ T G₁ M) (V₃ : Subgroup G) (hne : V₃ ≠ ⊥)
    (hgen : ⁅V₃, L₁⁆ = V₃)
    (hJ : Nat.card (markedImage K (K ⊓ M) s.model) = 384) :
    3 ^ (Nat.card L₁).factorization 3 = 3 := by
  have hd : Nat.card (markedImage K L₁ s.model) ∣ 384 := by
    rw [← hJ]
    exact card_dvd_of_le (map_mono (comap_mono s.seed_le_overlap))
  have he := markedImage_three_factorization K L₁ s.model s.seed_le_component
  have hl : 1 ≤ (Nat.card L₁).factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp
      (three_dvd_seed H M L₁ V₃ s.theta hne hgen)
  have hu : ¬ 2 ≤ (Nat.card L₁).factorization 3 := by
    rw [he]
    intro h
    have h9 : 9 ∣ Nat.card (markedImage K L₁ s.model) :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr h
    exact (by decide : ¬ 9 ∣ 384) (h9.trans hd)
  have hone : (Nat.card L₁).factorization 3 = 1 := by omega
  rw [hone]
  rfl

/-- The covered-A₆ case has an actual order-nine local quotient in the earlier
source setup. That quotient is incompatible with the proved three-part. -/
theorem uncovered_of_three_part (L L₁ : Subgroup G)
    (hthree : 3 ^ (Nat.card L₁).factorization 3 = 3)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hcovered : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 9) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  rcases hmodels with h | h
  · exact h
  · have hd : 9 ∣ Nat.card L₁ := by
      rw [← hcovered h]
      exact card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L₁))
        (QuotientGroup.mk'_surjective _)
    have htwo : 2 ≤ (Nat.card L₁).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hd
    have hone : (Nat.card L₁).factorization 3 = 1 := by
      apply Nat.pow_right_injective (by decide : 1 < 3)
      simpa only [pow_one] using hthree
    omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
