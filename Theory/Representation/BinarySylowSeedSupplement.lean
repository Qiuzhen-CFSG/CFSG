module
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Orbit generation from a Sylow-fixed seed and a normal supplement

If a normal subgroup and a seed-fixing subgroup generate the actor, the
normal-subgroup orbit span is already invariant under the whole actor.
A normal marked S₃ in a group S₃ × C₂ has two-group quotient, so every
Sylow two-subgroup supplies precisely such a supplement. The conclusion
keeps the original action and fixed seed, rather than choosing a model seed.

Source: Aschbacher--Smith 15.1.2, printed p.1085, the S₃ × C₂ exclusion.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.BinarySylowSeedSupplement
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem orbitSpan_eq_of_fixed_seed_normal_supplement
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G) [H.Normal]
    (S : Subgroup G) (hgen : S ⊔ H = ⊤) (I : Submodule (ZMod 2) V)
    (hfix : I ≤ fixedSpace ρ S) :
    Homogeneous.orbitSpan ρ ⊤ I = Homogeneous.orbitSpan ρ H I := by
  let R := Homogeneous.orbitSpan ρ H I
  have hSR : S ≤ subspaceStabilizer ρ R := by
    apply le_subspaceStabilizer
    intro s hs v hv
    change v ∈ ⨆ h : H, I.map (ρ h) at hv
    refine Submodule.iSup_induction (fun h : H => I.map (ρ h))
      (motive := fun w => ρ s w ∈ R) hv ?_ ?_ ?_
    · intro h w hw
      obtain ⟨i,hi,rfl⟩ := hw
      have hsi : ρ s i = i := hfix hi ⟨s,hs⟩
      let k : H := ⟨s * h * s⁻¹,(inferInstance : H.Normal).conj_mem h h.property s⟩
      apply le_iSup (fun h : H => I.map (ρ h)) k
      refine ⟨i,hi,?_⟩
      change ρ (s * (h : G) * s⁻¹) i = ρ s (ρ h i)
      have hsinv : ρ s⁻¹ i = i := hfix hi ⟨s⁻¹,S.inv_mem hs⟩
      simp only [map_mul,Module.End.mul_apply,hsinv]
    · simpa only [map_zero] using R.zero_mem
    · intro x y hx hy
      simpa only [map_add] using R.add_mem hx hy
  have hR : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ R := by
    rw [←hgen]
    exact sup_le hSR (Homogeneous.orbitSpan_invariant ρ H I)
  apply le_antisymm
  · exact Homogeneous.orbitSpan_le ρ (Homogeneous.le_orbitSpan ρ H I) hR
  · exact Homogeneous.orbitSpan_le ρ (Homogeneous.le_orbitSpan ρ ⊤ I)
      (le_top.trans (Homogeneous.orbitSpan_invariant ρ ⊤ I))

variable [Finite G]

theorem small_symmetricThree_seed_eq
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G) [H.Normal]
    (j : H ≃* Equiv.Perm (Fin 3))
    (e : G ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))
    (S : Sylow 2 G) :
    Homogeneous.orbitSpan ρ ⊤ (fixedSpace ρ (S : Subgroup G)) =
      Homogeneous.orbitSpan ρ H (fixedSpace ρ (S : Subgroup G)) := by
  have hc : Nat.card G = 12 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
      exact Nat.card_zmod 2
    rw [h2]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hH : Nat.card H = 6 := by
    rw [Nat.card_congr j.toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hq : Nat.card (G ⧸ H) = 2 := by
    have hh := H.card_mul_index
    rw [hH,hc,H.index_eq_card] at hh
    omega
  have hp : IsPGroup 2 (G ⧸ H) := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hq)
  exact orbitSpan_eq_of_fixed_seed_normal_supplement ρ H (S : Subgroup G)
    (S.sup_eq_top_of_quotient_isPGroup H hp) _ le_rfl
end Representation.BinarySylowSeedSupplement
