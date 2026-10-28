module
public import Theory.GroupAction.Quotient
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# Fixed vectors modulo a central subspace

A finite two-group acting on a nonzero elementary binary quotient has a
nonidentity fixed vector. For an ambient subgroup W and a central invariant
subgroup Z, lift that vector to u in W outside Z. The conclusion retains
actual ambient commutators [u,s] in Z, so it can be used without choosing
coordinates for W/Z.

The proof is the orbit-counting congruence modulo two. This is the common
fixed-vector construction used in Aschbacher--Smith 14.6.17 and 14.6.24;
exceptional nonsplit module covers may require a further lifting argument.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Theory.GroupAction
variable {G : Type*} [Group G] [Finite G]

theorem exists_nonidentity_fixed_modulo
    (S W Z : Subgroup G) [IsElementaryAbelian 2 W]
    (hS : IsPGroup 2 S) (hSW : S ≤ normalizer (W : Set G))
    (hSZ : S ≤ centralizer (Z : Set G)) (hZW : Z < W) :
    ∃ u ∈ W, u ∉ Z ∧ ∀ s ∈ S, ⁅u,s⁆ ∈ Z := by
  let : Normalizes S W := ⟨hSW⟩
  let N := Z.subgroupOf W
  let : IsInvariant S W N := ⟨by
    intro s w
    change (w : G) ∈ Z ↔ (s : G) * (w : G) * (s : G)⁻¹ ∈ Z
    exact (hSZ.trans (centralizer_le_normalizer _) s.property) w⟩
  let : MulDistribMulAction S (W ⧸ N) := quotientMulDistribMulAction N inferInstance
  have hp : IsPGroup 2 (W ⧸ N) :=
    (IsElementaryAbelian.isPGroup 2 W).of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  have hne : Nat.card (W ⧸ N) ≠ 1 := by
    intro hc
    have ht : N = ⊤ := index_eq_one.mp (by rwa [index_eq_card])
    apply hZW.not_ge
    intro w hw
    exact show (⟨w,hw⟩ : W) ∈ N from ht ▸ mem_top _
  have hdiv : 2 ∣ Nat.card (W ⧸ N) := hp.card_eq_or_dvd.resolve_left hne
  obtain ⟨v,hv,hvne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := W ⧸ N) hdiv (show (1 : W ⧸ N) ∈ MulAction.fixedPoints S (W ⧸ N) by
      simp [MulAction.mem_fixedPoints])
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N v
  refine ⟨u,u.property,?_,?_⟩
  · intro hu
    exact hvne ((QuotientGroup.eq_one_iff (N := N) u).mpr hu).symm
  · intro s hs
    have hf := MulAction.mem_fixedPoints.mp hv (⟨s⁻¹,S.inv_mem hs⟩ : S)
    change (QuotientGroup.mk' N) ((⟨s⁻¹,S.inv_mem hs⟩ : S) • u) =
      QuotientGroup.mk' N u at hf
    have hz : ((⟨s⁻¹,S.inv_mem hs⟩ : S) • u)⁻¹ * u ∈ N :=
      QuotientGroup.eq.mp hf
    change (s⁻¹ * (u : G) * (s⁻¹)⁻¹)⁻¹ * (u : G) ∈ Z at hz
    have hz' := (hSZ.trans (centralizer_le_normalizer _) hs _).mp hz
    have hi : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_left (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) u.property)
    simpa [commutatorElement_def, mul_assoc,hi] using hz'

end Theory.GroupAction
