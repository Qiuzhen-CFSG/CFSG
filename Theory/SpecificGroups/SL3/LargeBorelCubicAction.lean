module
public import Theory.SpecificGroups.PSL3.BorelCubicAction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.SL3.RadicalNormalizer
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
/-!
# Cubic Borel displacement in the full special-linear carrier

Perfectness makes the central-quotient action on automorphisms faithful.
The projective cubic-displacement theorem therefore lifts to the full SL₃
carrier through the original surjection and Sylow map, retaining its cubic
scalar center. A solvable overgroup of the defining Sylow is triangular
and hence normalizes that same Sylow. These two statements supply the
original normal-component argument without identifying SL₃ with PSL₃.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837.
-/
public section
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions
open scoped MatrixGroups
namespace Matrix.SL3.LargeBorelCubicAction
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem centerAction_conj (x : SL(3,F)) :
    centerAction F (MulAut.conj x) = MulAut.conj (projection F x) := by
  ext y
  obtain ⟨z,rfl⟩ := projection_surjective F y
  change centerAction F (MulAut.conj x) (QuotientGroup.mk z) = _
  rw [centerAction_mk]
  change projection F (x * z * x⁻¹) = _
  simp only [map_mul,map_inv,MulAut.conj_apply]

/-- Cubic displacement through the full special-linear quotient is detected
by the original Sylow inner action; the scalar center remains in the carrier. -/
theorem normalizer_actor_mem_sylow_inner {X : Type*} [Group X] [Finite X]
    {n : ℕ} (hn : 4 ≤ n) (hF : Nat.card F = 2^n)
    (q : X →* SL(3,F)) (hq : Function.Surjective q) (P : Sylow 2 X)
    (A : Subgroup (MulAut SL(3,F))) (hA : IsPGroup 2 A)
    (hPA : ((P : Subgroup X).map q).map MulAut.conj ≤ A)
    (α : MulAut X) (β : MulAut SL(3,F)) (hβ : β ∈ A)
    (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup X).map α.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set X), (α x * x⁻¹)^3 ∈ (P : Subgroup X)) :
    β ∈ ((P : Subgroup X).map q).map MulAut.conj := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let r := (projection F).comp q
  have hr : Function.Surjective r := (projection_surjective F).comp hq
  have hPA' : ((P : Subgroup X).map r).map MulAut.conj ≤ A.map (centerAction F) := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨MulAut.conj (q x),hPA ⟨q x,⟨x,hx,rfl⟩,rfl⟩,centerAction_conj (q x)⟩
  have he' (x : X) : r (α x) = centerAction F β (r x) := by
    change projection F (q (α x)) = centerAction F β (QuotientGroup.mk (q x))
    rw [he,centerAction_mk]
    rfl
  obtain ⟨_,⟨x,hx,rfl⟩,heq⟩ := Matrix.PSL3.BorelCubicAction.normalizer_actor_mem_sylow_inner
    hn hF r hr P (A.map (centerAction F)) (hA.map _) hPA' α
    (centerAction F β) (mem_map_of_mem _ hβ) he' hP hc
  refine ⟨q x,⟨x,hx,rfl⟩,ActorCoverage.centerAction_injective F ?_⟩
  exact (centerAction_conj (q x)).trans heq

/-- Solvable overgroups of a defining Sylow in the full SL₃ normalize that Sylow. -/
theorem solvable_overgroup_le_normalizer {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2^n) (P : Sylow 2 SL(3,F))
    (H : Subgroup SL(3,F)) [Group.IsSolvable H] (hPH : (P : Subgroup SL(3,F)) ≤ H) :
    H ≤ normalizer (P : Set SL(3,F)) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F) P
    (BorelQuotient.unipotentSLSylow F (by omega : 0 < n) hF)
  let e := MulAut.conj g
  have hP : (P : Subgroup SL(3,F)).map e.toMonoidHom = unipotentSL F := by
    change ((g • P : Sylow 2 SL(3,F)) : Subgroup SL(3,F)) = _
    rw [hg]
    rfl
  let : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hUH : unipotentSL F ≤ H.map e.toMonoidHom := by
    rw [←hP]
    exact map_mono hPH
  have hN := (SolvableOvergroups.solvable_le_borelSL F hfour (H.map e.toMonoidHom) hUH).trans
    (borelSL_le_normalizer_unipotentSL F)
  rw [←hP,←map_equiv_normalizer_eq (P : Subgroup SL(3,F)) e] at hN
  exact (map_le_map_iff_of_injective e.injective).mp hN
end Matrix.SL3.LargeBorelCubicAction
