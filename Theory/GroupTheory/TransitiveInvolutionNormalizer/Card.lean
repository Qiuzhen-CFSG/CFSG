module
public import Theory.GroupTheory.TransitiveInvolutionNormalizer
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting a point normalizer in a transitive conjugation action

When K normalizes A and is transitive on A minus the identity, the orbit
of the nonidentity element of a subgroup P of order two has |A|-1 elements.
Its stabilizer is the literal intersection K∩N_G(P), so orbit-stabilizer
computes that intersection's order without an abstract action replacement.

Source application: Aschbacher–Smith 14.3.19, printed p.997, identifying
K∩H with the original point parabolic R O²(N_H(A)).
-/

@[expose] public noncomputable section
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]

/-- Orbit-stabilizer for an original subgroup of order two inside A. -/
theorem card_point_normalizer_of_transitive
    (A K P : Subgroup G) (hKA : K ≤ normalizer (A:Set G))
    (hPA : P ≤ A) (hP : Nat.card P = 2)
    (ht : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ k ∈ K, k*(a:G)*k⁻¹ = b) :
    (Nat.card A-1)*Nat.card (K⊓normalizer (P:Set G):Subgroup G)=Nat.card K := by
  classical
  let := conjMulDistribMulActionOfLeNormalizer K A hKA
  obtain ⟨z,hz,hu⟩ := (Nat.card_eq_two_iff' (1:P)).mp hP
  let a:A := ⟨z,hPA z.property⟩
  have ha : a≠1 := by
    intro h
    have hh:(z:G)=1 := congrArg (fun x:A => (x:G)) h
    exact hz (Subtype.ext hh)
  have horbit:MulAction.orbit K a={b:A | b≠1} := by
    ext b
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k,rfl⟩ hh
      have hh' : (k:G)*(a:G)*(k:G)⁻¹=1 := congrArg Subtype.val hh
      have he : (a:G)=1 := (MulAut.conj (k:G)).injective (hh'.trans (map_one (MulAut.conj (k:G))).symm)
      exact ha (Subtype.ext he)
    · intro hb
      obtain ⟨k,hk,he⟩ := ht a b ha hb
      exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hstab:MulAction.stabilizer K a=(K⊓normalizer (P:Set G)).subgroupOf K := by
    ext k
    change k • a = a ↔ (k:G)∈K⊓normalizer (P:Set G)
    constructor
    · intro hh
      refine ⟨k.property,?_⟩
      apply centralizer_le_normalizer (P:Set G)
      intro x hx
      by_cases hx1:x=1
      · simp [hx1]
      have hxz:x=(z:G) := congrArg Subtype.val (hu ⟨x,hx⟩ (fun h=>hx1 (congrArg Subtype.val h)))
      rw [hxz]
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)).symm
    · intro hk
      have hh := normalizer_le_centralizer_of_card_two P hP hk.2 (z:G) z.property
      apply Subtype.ext
      change (k:G)*(z:G)*(k:G)⁻¹=z
      rw [←hh,mul_inv_cancel_right]
  have hc:Nat.card {b:A // b≠1}=Nat.card A-1 := by
    let :Fintype A:=Fintype.ofFinite A
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_unique]
  have h:=Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K a)
  rw [Nat.card_prod,horbit,hstab] at h
  change Nat.card {b:A // b≠1} * Nat.card ((K⊓normalizer (P:Set G)).subgroupOf K)=Nat.card K at h
  rw [hc,Nat.card_congr (subgroupOfEquivOfLe (show K⊓normalizer (P:Set G)≤K from inf_le_left)).toEquiv] at h
  exact h
end Subgroup
