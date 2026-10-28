module
public import Theory.GroupAction.Quotient
public import Theory.GroupTheory.SubgroupConjugation
/-!
# Full conjugation actions on subgroup quotients

If P normalizes U and Z, then P acts by conjugation on the literal
quotient U/(Z.subgroupOf U). This module constructs its homomorphism into
the quotient's automorphism group with the exact quotient-conjugation
formula. The plain action construction and its kernel criterion are
exported separately for the terminal quotient recognition, which does not
need the full-commutator hypothesis. If [U,Q] lies in Z, the Q-elements of P lie in the kernel. If
E≤P and [U,E]=U, the actual image of E has full action commutator on
the quotient. No finite-group or coprimality hypothesis is required.

Invariance of Z descends the conjugation action. The commutator identity
identifies the Q-action with the identity modulo Z. To descend fullness,
pull the quotient action-commutator subgroup back to U: every generator
of [U,E] belongs to that preimage, so it contains U.

This supplies the exact action on V₁/Z_(alpha+1) used before (1.3) in
Stellmacher (9.1), Journal of Algebra 190 (1997), p.47. The graph, local
residual, and elementary abelian hypotheses belong to its consumer.
-/

namespace Subgroup
open scoped Pointwise commutatorElement
universe u
public theorem exists_quotient_conjugation_action
    {G : Type u} [Group G] (P U Z : Subgroup G)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G))
    (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    ∃ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
      ∀ p : P, ∀ u : U,
        ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩ := by
  let _ := hN
  let _ : Subgroup.Normalizes P U := ⟨hPU⟩
  let _ : MulDistribMulAction P U :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P U hPU
  have hInv : IsInvariant P U (Z.subgroupOf U) := by
    constructor
    intro p u
    change (u : G) ∈ Z ↔ (p : G) * (u : G) * (p : G)⁻¹ ∈ Z
    exact Subgroup.mem_normalizer_iff.mp (hPZ p.property) u
  let _ : MulDistribMulAction P (U ⧸ Z.subgroupOf U) :=
    quotientMulDistribMulAction (Z.subgroupOf U) hInv
  refine ⟨MulDistribMulAction.toMulAut P (U ⧸ Z.subgroupOf U), ?_⟩
  intro p u
  let _ : MulAction.QuotientAction P (Z.subgroupOf U) := quotientAction_of_isInvariant _ hInv
  exact MulAction.Quotient.smul_coe (Z.subgroupOf U) p u
public theorem quotient_conjugation_action_kills_commutator_layer
    {G : Type u} [Group G] (P U Z Q : Subgroup G)
    (hN : (Z.subgroupOf U).Normal)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hUQ : ⁅U,Q⁆ ≤ Z) :
    let _ := hN
    ∀ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ p : P, ∀ u : U,
        ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) →
      Q.subgroupOf P ≤ ρ.ker := by
  let _ := hN
  dsimp only
  intro ρ hρ p hp
  apply MonoidHom.mem_ker.mpr
  ext w
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
  rw [hρ]
  change QuotientGroup.mk' (Z.subgroupOf U) _ = QuotientGroup.mk' (Z.subgroupOf U) u
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (p : G) * (u : G) * (p : G)⁻¹ / (u : G) ∈ Z
  have hc : ⁅(p : G), (u : G)⁆ ∈ Z := by
    rw [Subgroup.commutator_comm] at hUQ
    exact hUQ (Subgroup.commutator_mem_commutator hp u.property)
  simpa only [commutatorElement_def, div_eq_mul_inv] using hc

private theorem quotient_action_full
    {G : Type u} [Group G] (P U Z E : Subgroup G)
    (hN : (Z.subgroupOf U).Normal)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hEP : E ≤ P) (hfull : ⁅U,E⁆ = U) :
    let _ := hN
    ∀ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ p : P, ∀ u : U,
        ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) →
      commutatorAction ((E.subgroupOf P).map ρ) (U ⧸ Z.subgroupOf U) = ⊤ := by
  let _ := hN
  dsimp only
  intro ρ hρ
  let F := (E.subgroupOf P).map ρ
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  let C := commutatorAction F (U ⧸ Z.subgroupOf U)
  let D := (C.comap π).map U.subtype
  have hUD : U ≤ D := by
    rw [← hfull]
    apply Subgroup.commutator_le.mpr
    intro u hu e he
    let uU : U := ⟨u,hu⟩
    let eP : P := ⟨e,hEP he⟩
    let eF : F := ⟨ρ eP, Subgroup.mem_map_of_mem ρ he⟩
    have hmem : ⁅u,e⁆ ∈ U := hfull.le (Subgroup.commutator_mem_commutator hu he)
    refine ⟨⟨⁅u,e⁆,hmem⟩, ?_, rfl⟩
    change π ⟨⁅u,e⁆,hmem⟩ ∈ C
    have hh : (π uU⁻¹)⁻¹ * (eF • π uU⁻¹) ∈ C := by
      dsimp only [C]
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨eF, π uU⁻¹, rfl⟩
    have heq : (π uU⁻¹)⁻¹ * (eF • π uU⁻¹) = π ⟨⁅u,e⁆,hmem⟩ := by
      change (π uU⁻¹)⁻¹ * (ρ eP) (π uU⁻¹) = _
      rw [hρ, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, commutatorElement_def]
      simp only [uU, eP, mul_assoc]
    exact heq ▸ hh
  apply top_unique
  intro w _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
  obtain ⟨v,hv,hvu⟩ := hUD u.property
  have hvu' : v = u := Subtype.ext hvu
  exact hvu' ▸ hv
public theorem exists_quotient_conjugation_full_action
    {G : Type u} [Group G] (P U Z E Q : Subgroup G)
    (hPU : P ≤ normalizer (U : Set G))
    (hPZ : P ≤ normalizer (Z : Set G))
    (hN : (Z.subgroupOf U).Normal)
    (hEP : E ≤ P) (hfull : ⁅U,E⁆ = U) (hUQ : ⁅U,Q⁆ ≤ Z) :
    let _ := hN
    ∃ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ p : P, ∀ u : U,
        ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) ∧
      Q.subgroupOf P ≤ ρ.ker ∧
      commutatorAction ((E.subgroupOf P).map ρ) (U ⧸ Z.subgroupOf U) = ⊤ := by
  let _ := hN
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action P U Z hPU hPZ hN
  exact ⟨ρ,hρ,quotient_conjugation_action_kills_commutator_layer P U Z Q hN hPU hUQ ρ hρ,
    quotient_action_full P U Z E hN hPU hEP hfull ρ hρ⟩
end Subgroup
