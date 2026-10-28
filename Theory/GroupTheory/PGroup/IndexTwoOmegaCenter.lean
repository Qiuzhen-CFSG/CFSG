module

public import Theory.GroupAction.IndexTwoFixedCard
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.IndexNormal

/-!
# Central involutions in an index-two subgroup

If `S` has index two in a finite group `T`, conjugation on the elementary
abelian group `Ω₁(Z(S))` factors through `T/S`. The involution fixed-point
bound gives `|Ω₁(Z(S))| ≤ |Ω₁(Z(T))|²`. In particular, if the latter omega
subgroup has order two, any central elementary abelian four-subgroup of `S`
is exactly `Ω₁(Z(S))`.

This is the group-theoretic argument of Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), Lemma 15.3.8,
printed p.1122. The application supplies the index-two plane stabilizer `S`
and the four-subgroup `Z_S = C_V(S)` from the natural orthogonal action.
-/

open Subgroup

namespace Subgroup

/-- A normal elementary abelian subgroup centralized by an index-two subgroup
has order at most the square of the central omega subgroup. -/
public theorem elementary_card_le_omega_center_sq_of_index_two
    {G : Type*} [Group G] [Finite G]
    (S E : Subgroup G) (hS : S.index = 2)
    [E.Normal] [IsElementaryAbelian 2 E]
    (hES : E ≤ centralizer (S : Set G)) :
    Nat.card E ≤ Nat.card (omega₁ (center G) (p := 2)) ^ 2 := by
  let f : G →* MulAut E := E.normalizerMonoidHom.comp
    ((MonoidHom.id G).codRestrict (normalizer (E : Set G)) (fun g =>
      (normalizer_eq_top E).symm ▸ mem_top g))
  let : MulDistribMulAction G E := MulDistribMulAction.compHom E f
  have hfix : ∀ s ∈ S, ∀ e : E, s • e = e := by
    intro s hs e
    apply Subtype.ext
    change s * (e : G) * s⁻¹ = (e : G)
    exact mul_inv_eq_iff_eq_mul.mpr ((hES e.property) s hs)
  have hbound := card_le_fixed_card_sq_of_index_two_kernel S hS hfix
  let C := FixedPoints.subgroup G E
  let j : C → omega₁ (center G) (p := 2) := fun e =>
    let z : center G := ⟨(e : E), mem_center_iff.mpr (fun g => by
      have hg := congrArg E.subtype (e.property g)
      change g * ((e : E) : G) * g⁻¹ = ((e : E) : G) at hg
      exact mul_inv_eq_iff_eq_mul.mp hg)⟩
    ⟨z, subset_closure (by
      change z ^ (2 ^ 1) = 1
      apply Subtype.ext
      change ((e : E) : G) ^ 2 = 1
      exact elemPow_eq_one_of_isElementaryAbelian
        ((e : E) : G) (e : E).property)⟩
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : omega₁ (center G) (p := 2) => ((x : center G) : G)) h
  exact hbound.trans (Nat.pow_le_pow_left (Nat.card_le_card_of_injective j hj) 2)

/-- Passing to an index-two subgroup increases the central omega order by
at most a square. -/
public theorem card_omega_center_le_sq_of_index_two
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (hS : S.index = 2) :
    Nat.card (omega₁ (center S) (p := 2)) ≤
      Nat.card (omega₁ (center G) (p := 2)) ^ 2 := by
  let : S.Normal := normal_of_index_eq_two hS
  let : (omega₁ (center S) (p := 2)).Characteristic := omega₁_characteristic _
  let A := (omega₁ (center S) (p := 2)).map (center S).subtype
  let E := A.map S.subtype
  have hnorm : E.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← normalizer_eq_top S]
    exact normalizer_le_normalizer_characteristic_image S A))
  let : IsElementaryAbelian 2 (omega₁ (center S) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hES : E ≤ centralizer (S : Set G) := by
    rintro _ ⟨a, ha, rfl⟩ s hs
    obtain ⟨z, hz, rfl⟩ := ha
    exact congrArg S.subtype (mem_center_iff.mp z.property ⟨s, hs⟩)
  have hbound := elementary_card_le_omega_center_sq_of_index_two S E hS hES
  simpa only [E, A, card_map_of_injective S.subtype_injective,
    card_map_of_injective (center S).subtype_injective] using hbound

/-- A central four-subgroup exhausts the central omega subgroup when the
ambient central omega subgroup has order two. -/
public theorem omega_center_eq_four_of_index_two
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (hS : S.index = 2)
    (hZ : Nat.card (omega₁ (center G) (p := 2)) = 2)
    (V : Subgroup S) [IsElementaryAbelian 2 V]
    (hV : V ≤ center S) (hcard : Nat.card V = 4) :
    omegaOneAmbient (center S) = V := by
  have hle : V ≤ omegaOneAmbient (center S) := by
    rw [← omegaOneAmbient_eq_self V]
    exact omegaOneAmbient_mono hV
  apply (eq_of_le_of_card_ge hle ?_).symm
  have hbound := card_omega_center_le_sq_of_index_two S hS
  rw [hZ] at hbound
  rw [omegaOneAmbient, card_map_of_injective (center S).subtype_injective, hcard]
  exact hbound

end Subgroup
