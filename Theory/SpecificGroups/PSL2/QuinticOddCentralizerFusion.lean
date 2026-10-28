module

public import Theory.SpecificGroups.PSL2.QuinticCentralInvolutionEscape
public import Theory.GroupTheory.OddCentralizerWholeSubgroupPlacement

/-!
# Quintic fusion through an odd-index inner centralizer

For a normal self-centralizing odd PSL₂ component N and G=N⟨a⟩, an
involution a can be fused out of the quintic two-core while
returning to the originally supplied Sylow subgroup whenever its actual
inner centralizer has odd index. First an N-conjugator makes a Sylow-central;
if it has not yet escaped, the proved corefree Z-star argument completes
the fusion. This is a whole-subgroup statement for the cyclic group ⟨a⟩.

This supplies the cyclic case of the quadratic field-involution argument
in Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

/-- Odd inner fixed-group index suffices for whole cyclic involution fusion
in the actual quintic Sylow supplement. -/
theorem odd_quintic_odd_centralizer_cyclic_fusion
    {G : Type*} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (h8 : 8 ∣ Nat.card PSL(2,F))
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (hC : centralizer (N : Set G) = ⊥)
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (a : G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (hgen : N ⊔ zpowers a = ⊤)
    (hi : Odd ((centralizer ({a} : Set G)).subgroupOf N).index) :
    ∃ g ∈ N, (zpowers a).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ (zpowers a).map (MulAut.conj g).toMonoidHom ≤
        (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  classical
  let S := (X ⊔ (T : Subgroup G)).pCoreIn 2
  have haord : orderOf a = 2 := orderOf_eq_prime_iff.mpr ⟨ha2, ha1⟩
  have hAp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, haord, pow_one])
  have hAC : zpowers a ≤ centralizer ({a} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨g, hg, hAg, hag⟩ := odd_centralizer_whole_subgroup_placement N a hgen hi
    (zpowers a) hAp (mem_zpowers a) hAC T
  let b := g * a * g⁻¹
  have hbT : b ∈ (T : Subgroup G) := hAg (mem_map_of_mem _ (mem_zpowers a))
  have hb2 : b ^ 2 = 1 := by
    change (MulAut.conj g a) ^ 2 = 1
    rw [← map_pow, ha2, map_one]
  have hb1 : b ≠ 1 := by
    intro he
    exact ha1 ((MulAut.conj g).injective (he.trans (map_one _).symm))
  have hgenT : N ⊔ (T : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have hb : b ∈ N ⊔ (T : Subgroup G) :=
      (show (T : Subgroup G) ≤ N ⊔ (T : Subgroup G) from le_sup_right) hbT
    have hg' : g ∈ N ⊔ (T : Subgroup G) :=
      (show N ≤ N ⊔ (T : Subgroup G) from le_sup_left) hg
    have hh := (N ⊔ (T : Subgroup G)).mul_mem
      ((N ⊔ (T : Subgroup G)).mul_mem ((N ⊔ (T : Subgroup G)).inv_mem hg') hb) hg'
    change g⁻¹ * (g * a * g⁻¹) * g ∈ _ at hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  by_cases hbS : b ∈ S
  · obtain ⟨k, hk, hkbT, hkbS⟩ := odd_quintic_central_involution_escape hF h8 N e hC
      T hgenT X hXN hfive hTX b hbS hb2 hb1 hag
    have he : MulAut.conj (k * g) a = k * b * k⁻¹ := by
      change (k * g) * a * (k * g)⁻¹ = k * (g * a * g⁻¹) * k⁻¹
      group
    refine ⟨k * g, N.mul_mem hk hg, ?_, ?_⟩
    · rw [MonoidHom.map_zpowers]
      change zpowers (MulAut.conj (k * g) a) ≤ _
      rw [he]
      exact zpowers_le.mpr hkbT
    · rw [MonoidHom.map_zpowers]
      change ¬ zpowers (MulAut.conj (k * g) a) ≤ _
      rw [he]
      exact fun hh => hkbS (hh (mem_zpowers _))
  · exact ⟨g, hg, hAg, fun hh => hbS (hh (mem_map_of_mem _ (mem_zpowers a)))⟩

end Theory.PSL2
