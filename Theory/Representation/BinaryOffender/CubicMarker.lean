module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# A cubic fixing a binary section and its kernel

If a cubic centralizes E and fixes V/E, its displacement on V is both
quadratic unipotent and of odd order, hence zero. In particular no assumption
that it stabilizes V is needed: the actual displacement containment implies
that stabilization. Lifting elementary three-subgroups through a two-group
kernel applies this calculation to a literal quotient marker.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the use of
15.3.49(5) in the proof of 15.3.67, printed pp.1153–1154.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryOffender
variable {G D W : Type*} [Group G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A cubic that fixes E and whose displacement on v lies in E fixes v.
Only exponent two of E is needed. -/
theorem cubic_centralizes_of_displacement (E : Subgroup G)
    [IsElementaryAbelian 2 E] (x : G) (h3 : x ^ 3 = 1)
    (hx : x ∈ centralizer (E : Set G)) (v : G) (hv : ⁅x, v⁆ ∈ E) :
    v * x = x * v := by
  let d := x * v * x⁻¹ * v⁻¹
  have hd : d ∈ E := hv
  have hd2 : d * d = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) d hd
  have hxd : x * d * x⁻¹ = d := by rw [← hx d hd, mul_inv_cancel_right]
  have h2 : x * (x * v * x⁻¹) * x⁻¹ = v := by
    calc
      _ = (x * d * x⁻¹) * (d * v) := by dsimp [d]; group
      _ = d * (d * v) := by rw [hxd]
      _ = v := by rw [← mul_assoc, hd2, one_mul]
  have h := congrArg (fun w => x * w * x⁻¹) h2
  have h3v : x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = v := by
    calc
      _ = x ^ 3 * v * (x ^ 3)⁻¹ := by simp only [pow_succ, pow_zero, one_mul]; group
      _ = v := by rw [h3]; simp
  exact (mul_inv_eq_iff_eq_mul.mp (h.symm.trans h3v)).symm

variable [Finite G]

/-- A quotient marker centralizer has order prime to three if its actual
lifts fix E and V/E and N_G(Z), for Z ≤ V, has order prime to three.
The `hmarker` premise is a literal displacement comparison for the paired
marker, not a no-cubic or generation premise. -/
theorem markerCentralizer_coprime_three_of_section
    (q : G →* D) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker)
    (E V Z C : Subgroup G) [IsElementaryAbelian 2 E]
    (hQC : q.ker ≤ C) (hCE : C ≤ centralizer (E : Set G)) (hZV : Z ≤ V)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G))))
    (σ : Representation (ZMod 2) D W) (I : Subgroup D) (hIC : I ≤ C.map q)
    (P : Submodule (ZMod 2) W)
    (hmarker : ∀ x ∈ C, q x ∈ I → (∀ w ∈ P, σ (q x) w = w) →
      ∀ v ∈ V, ⁅x, v⁆ ∈ E) :
    Nat.Coprime 3 (Nat.card (subspaceKernel (σ.comp I.subtype) P ⊤)) := by
  let : Finite D := Finite.of_surjective q hq
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hdvd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  let d : D := a.val.val
  have hd : orderOf d = 3 := by
    rw [show orderOf d = orderOf a.val from (Subgroup.orderOf_coe a.val),
      Subgroup.orderOf_coe a, ha]
  let A := zpowers d
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.zpowers_of_pow_eq_one
    (show d ^ 3 = 1 from hd ▸ pow_orderOf_eq_one d)
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨B, hB, hmap, hcard⟩ :=
    exists_elementaryAbelian_map_eq_of_surjective_coprime q hq hcop A
  let : IsElementaryAbelian 3 B := hB
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ B, q x = d := by
    exact (show d ∈ B.map q from hmap.symm ▸ mem_zpowers d)
  have hx3 : x ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hxC : x ∈ C := by
    have : x ∈ (C.map q).comap q := by
      change q x ∈ C.map q
      rw [hxd]
      exact hIC a.val.property
    rwa [comap_map_eq_self hQC] at this
  have hxI : q x ∈ I := by
    rw [hxd]
    exact a.val.property
  have hxP : ∀ w ∈ P, σ (q x) w = w := by
    intro w hw
    rw [hxd]
    exact a.property.2 w hw
  have hxV : x ∈ centralizer (V : Set G) := fun v hv =>
    cubic_centralizes_of_displacement E x hx3 (hCE hxC) v (hmarker x hxC hxI hxP v hv)
  have hxZ : x ∈ normalizer (Z : Set G) :=
    centralizer_le_normalizer _ ((centralizer_le hZV) hxV)
  have hdvd' : 3 ∣ Nat.card (normalizer (Z : Set G)) := by
    have horder : orderOf x = 3 := Nat.dvd_antisymm
      (orderOf_dvd_of_pow_eq_one hx3) (hd ▸ hxd ▸ orderOf_map_dvd q x)
    rw [← horder, Subgroup.orderOf_coe (⟨x, hxZ⟩ : normalizer (Z : Set G))]
    exact orderOf_dvd_natCard _
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hZ) hdvd'

omit [Finite G] in
/-- The pointwise marker centralizer maps onto the centralizer of the same
marker through a surjective change of actors. -/
theorem markerCentralizer_map_surjective
    (σ : Representation (ZMod 2) D W) (q : G →* D) (hq : Function.Surjective q)
    (P : Submodule (ZMod 2) W) :
    (subspaceKernel (σ.comp q) P ⊤).map q = subspaceKernel σ P ⊤ := by
  ext d
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨mem_top _, hg.2⟩
  · intro hd
    obtain ⟨g, rfl⟩ := hq d
    exact ⟨g, ⟨mem_top _, hd.2⟩, rfl⟩

omit [Finite G] in
/-- A prime-to-three marker centralizer makes the entire action kernel
prime to three as well. -/
theorem action_kernel_coprime_three_of_marker
    (ρ : Representation (ZMod 2) G W) (P : Submodule (ZMod 2) W)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ P ⊤))) :
    Nat.Coprime 3 (Nat.card (actionHom ρ).ker) := by
  have hle : (actionHom ρ).ker ≤ subspaceKernel ρ P ⊤ := by
    intro g hg
    exact ⟨mem_top _, fun v _ => (actionHom_eq_one_iff ρ g).mp hg v⟩
  exact hP.of_dvd_right (card_dvd_of_le hle)

omit [Finite G] in
/-- The actual image marker centralizer inherits prime-to-three order. -/
theorem image_markerCentralizer_coprime_three
    (ρ : Representation (ZMod 2) G W) (P : Submodule (ZMod 2) W)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ P ⊤))) :
    Nat.Coprime 3 (Nat.card (subspaceKernel (imageRepresentation ρ) P ⊤)) := by
  have hm := markerCentralizer_map_surjective (imageRepresentation ρ)
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective P
  have he : (imageRepresentation ρ).comp (actionHom ρ) = ρ := rfl
  rw [he] at hm
  rw [← hm]
  exact hP.of_dvd_right (card_map_dvd _ _)

end Representation.BinaryOffender
