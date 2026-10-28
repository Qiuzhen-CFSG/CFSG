module

public import Theory.GroupTheory.PStar.ActionTools
public import Theory.GroupTheory.PStar.Supplement
public import Theory.GroupAction.SubgroupConjugation

/-!
# Two-star action decomposition and normal products

Assume precisely the universal Sylow-centralizer residual theorem of
GLS II, Chapter B, 5.4. Then a two-group acting on a two-star group G gives
G = [G,A] C_G(A), also with the intrinsic two-residual of C_G(A).

For the induction, put K = [G,A]. The supporting module proves that K is
two-perfect. Choose an A-invariant Sylow two-subgroup P of K. If C_G(P) is
proper, apply 5.4 and induction to its residual, which supplements K by
the definition of two-star. If C_G(P) is all of G, transfer makes K odd;
every K-coset then has an A-fixed point. This avoids any additional
semisimple-action or decomposition premise.

For normal-product closure, act on each normal factor with the literal
Sylow subgroup of an arbitrary normal subgroup of their join. Its action
commutators lie in that normal subgroup, and its fixed points lie in the
required Sylow centralizer. The action theorem therefore gives the
supplement required in the definition of two-star.

Source: GLS II, Chapter B, Lemmas 5.5 and the normal-product clause of 5.6,
using 5.4 as an explicit parameter. These are conditional exports; their
unconditional assembly must supply 5.4.
-/

public section

open Subgroup
namespace Theory.GroupTheory
open PStarAction
universe u v
variable {G : Type u} [Group G] [Finite G]
variable (h54 : ∀ (Y : Type u) [Group Y] [Finite Y], IsPStar 2 Y →
  ∀ (N : Subgroup Y) [N.Normal] (P : Sylow 2 N),
    IsPStar 2 (pResidual 2 (centralizer ((P : Subgroup N).map N.subtype : Set Y))))

include h54

/-- GLS II 5.5 at the prime two, conditional only on the universal 5.4
Sylow-centralizer residual theorem. -/
theorem IsPStar.commutator_sup_fixed_of_centralizerResidual {A : Type v} [Group A]
    [MulDistribMulAction A G] (hA : IsPGroup 2 A) (hG : IsPStar 2 G) :
    commutatorAction A G ⊔ fixedPointSubgroup A G = ⊤ := by
  suffices ∀ n (Y : Type u) [Group Y] [Finite Y] [MulDistribMulAction A Y],
      Nat.card Y = n → IsPStar 2 Y →
      commutatorAction A Y ⊔ fixedPointSubgroup A Y = ⊤ from
    this _ G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y _ _ _ hcard hY
    let K := commutatorAction A Y
    let _ : K.Normal := commutatorAction_normal
    let _ : IsInvariant A Y K := commutatorAction_isInvariant
    obtain ⟨P, hPI⟩ := exists_invariant_sylow_same_prime (G := K) hA
    let _ : IsInvariant A K (P : Subgroup K) := hPI
    let S := (P : Subgroup K).map K.subtype
    let _ : IsInvariant A Y S := isInvariant_map_subtype K (P : Subgroup K)
    let C := centralizer (S : Set Y)
    let _ : IsInvariant A Y C := isInvariant_centralizer S
    by_cases hC : C = ⊤
    · have hS : S ≤ center Y := centralizer_eq_top_iff_subset.mp hC
      have hP : (P : Subgroup K) ≤ center K := by
        intro k hk
        apply mem_center_iff.mpr
        intro x
        exact Subtype.ext (mem_center_iff.mp (hS (mem_map_of_mem K.subtype hk)) x)
      exact commutator_sup_fixed_eq_top_of_coprime hA
        (coprime_card_of_central_sylow (hY.isPPerfect_commutatorAction (A := A)) P hP)
    · let R := pResidual 2 C
      let _ : IsInvariant A C R := isInvariant_of_characteristic R
      have hRC : Nat.card R ≤ Nat.card C := R.card_le_card_group
      have hCY : Nat.card C < Nat.card Y := lt_of_le_of_ne C.card_le_card_group
        (fun he => hC (C.card_eq_iff_eq_top.mp he))
      have hRn : Nat.card R < n := hcard ▸ (hRC.trans_lt hCY)
      have hRstar : IsPStar 2 R := h54 Y hY K P
      have hrec := ih (Nat.card R) hRn R rfl hRstar
      let f : R →* Y := C.subtype.comp R.subtype
      have hd : (commutatorAction A R).map f ≤ K := by
        rw [map_le_iff_le_comap, commutatorAction_eq_closure]
        apply (closure_le _).mpr
        rintro _ ⟨a, x, rfl⟩
        change ((x : C) : Y)⁻¹ * (a • ((x : C) : Y)) ∈ K
        exact subset_closure ⟨a, ((x : C) : Y), mem_top _, rfl⟩
      have hf : (fixedPointSubgroup A R).map f ≤ fixedPointSubgroup A Y := by
        rintro _ ⟨x, hx, rfl⟩ a
        exact congrArg (fun z : R => f z) (hx a)
      have hrange : f.range = R.map C.subtype := by
        change (C.subtype.comp R.subtype).range = _
        rw [MonoidHom.range_comp, range_subtype]
      have hRle : R.map C.subtype ≤ K ⊔ fixedPointSubgroup A Y := by
        rw [← hrange, MonoidHom.range_eq_map, ← hrec, Subgroup.map_sup]
        exact sup_le (hd.trans le_sup_left) (hf.trans le_sup_right)
      apply top_unique
      rw [← hY.sup_pResidual_centralizer_eq_top K P]
      exact sup_le le_sup_left hRle

/-- The second equality in GLS II 5.5: replace the fixed subgroup by its
intrinsic two-residual, embedded by its subtype. -/
theorem IsPStar.commutator_sup_fixedResidual_of_centralizerResidual {A : Type v} [Group A]
    [MulDistribMulAction A G] (hA : IsPGroup 2 A) (hG : IsPStar 2 G) :
    commutatorAction A G ⊔ (pResidual 2 (fixedPointSubgroup A G)).map
      (fixedPointSubgroup A G).subtype = ⊤ := by
  let _ : (commutatorAction A G).Normal := commutatorAction_normal
  exact sup_embedded_pResidual_eq_top ((pResidual_eq_top_iff 2 G).mp hG.1)
    _ _ (IsPStar.commutator_sup_fixed_of_centralizerResidual h54 hA hG)

private theorem normal_factor_le_sylow_supplement
    (X N : Subgroup G) [X.Normal] [N.Normal] (hX : IsPStar 2 X) (P : Sylow 2 N) :
    X ≤ N ⊔ centralizer ((P : Subgroup N).map N.subtype : Set G) := by
  let _ : MulDistribMulAction P X :=
    MulDistribMulAction.compHom X (P : Subgroup N).subtype
  let S := (P : Subgroup N).map N.subtype
  have hgen := IsPStar.commutator_sup_fixed_of_centralizerResidual h54 P.isPGroup' hX
  have hd : (commutatorAction P X).map X.subtype ≤ N := by
    rw [map_le_iff_le_comap, commutatorAction_eq_closure]
    apply (closure_le _).mpr
    rintro _ ⟨a, x, rfl⟩
    change (x : G)⁻¹ * (((a : N) : G) * (x : G) * ((a : N) : G)⁻¹) ∈ N
    have hc := (inferInstance : N.Normal).conj_mem ((a : N) : G)
      (a : N).property (x : G)⁻¹
    simpa only [inv_inv, mul_assoc] using N.mul_mem hc (N.inv_mem (a : N).property)
  have hf : (fixedPointSubgroup P X).map X.subtype ≤ centralizer (S : Set G) := by
    rintro _ ⟨x, hx, rfl⟩ y ⟨a, ha, rfl⟩
    have he := congrArg (fun z : X => (z : G)) (hx ⟨a, ha⟩)
    change (a : G) * (x : G) * (a : G)⁻¹ = (x : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  have hh := congrArg (Subgroup.map X.subtype) hgen
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
  rw [← hh]
  exact sup_le (hd.trans le_sup_left) (hf.trans le_sup_right)

/-- A group generated by two normal two-star subgroups is two-star,
conditional on the universal GLS II 5.4 input. -/
theorem isPStar_of_normal_sup_eq_top_of_centralizerResidual
    (X₁ X₂ : Subgroup G) [X₁.Normal] [X₂.Normal]
    (h₁ : IsPStar 2 X₁) (h₂ : IsPStar 2 X₂) (hgen : X₁ ⊔ X₂ = ⊤) :
    IsPStar 2 G := by
  refine ⟨top_unique ?_, ?_⟩
  · rw [← hgen]
    exact sup_le (le_pResidual_of_isPPerfect X₁ ((pResidual_eq_top_iff 2 X₁).mp h₁.1))
      (le_pResidual_of_isPPerfect X₂ ((pResidual_eq_top_iff 2 X₂).mp h₂.1))
  · intro N _ P
    apply top_unique
    rw [← hgen]
    exact sup_le (normal_factor_le_sylow_supplement h54 X₁ N h₁ P)
      (normal_factor_le_sylow_supplement h54 X₂ N h₂ P)

/-- Normal-product closure in GLS II 5.6, conditional on the universal 5.4
input. Normality is restricted to the join and the factors are transported
through the actual subgroup equivalences. -/
theorem IsPStar.normal_sup_of_centralizerResidual (X₁ X₂ : Subgroup G) [X₁.Normal] [X₂.Normal]
    (h₁ : IsPStar 2 X₁) (h₂ : IsPStar 2 X₂) : IsPStar 2 (X₁ ⊔ X₂ : Subgroup G) := by
  exact isPStar_of_normal_sup_eq_top_of_centralizerResidual h54
    (X₁.subgroupOf (X₁ ⊔ X₂)) (X₂.subgroupOf (X₁ ⊔ X₂))
    (h₁.of_equiv (subgroupOfEquivOfLe (show X₁ ≤ X₁ ⊔ X₂ from le_sup_left)).symm)
    (h₂.of_equiv (subgroupOfEquivOfLe (show X₂ ≤ X₁ ⊔ X₂ from le_sup_right)).symm)
    (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])

end Theory.GroupTheory
