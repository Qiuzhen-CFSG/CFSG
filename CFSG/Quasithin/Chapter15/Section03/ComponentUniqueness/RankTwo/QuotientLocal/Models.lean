module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The simple models of the component quotient

Every one of the six alternatives of 1.1.5(3) is transported to the actual
central quotient. In the Lie and odd-linear cases the original group is
centerless. Alternating triple covers already supply the central-quotient
isomorphism. For the two-covers and sporadic alternatives, Z(L)=O₂(L)
identifies the two denominators. The latter identity follows from the
odd-core conclusion of 15.3.33, without any extra model-order certification.

The output records the underlying simple models used in 15.3.41(1), with
all parameters and all sporadic alternatives retained. The involution-action
clauses remain in the upstream ModelAction115 input; no classification
of those actions is assumed for the quotient.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
1.1.5(3), printed pp.501--503, and 15.3.41(1), printed p.1138.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
open Candidates.ComponentStructure ClassificationModels Chapter1.Section02.LocalModels

/-- The underlying simple quotient models in all six cases of 1.1.5(3).
Each alternative specifies an actual isomorphism, including both cover
quotients and the exact Fermat/Mersenne and sporadic restrictions. -/
inductive SimpleModel115 (K : Type*) [Group K] : Prop
  | lie (model : LieTypeTwoModel K)
  | two_cover (model : ClassicalGroup.IsPSL K 3 4 ∨ IsG2At K 4)
  | six (model : Nonempty (K ≃* alternatingGroup (Fin 6)))
  | seven (model : Nonempty (K ≃* alternatingGroup (Fin 7)))
  | odd (model : ClassicalGroup.IsPSL K 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p)
  | sporadic (name : SporadicName) (not_j3 : name ≠ .j3)
      (model : Nonempty (K ≃* name.Carrier))

private theorem lieTypeTwoModel_transport {K H : Type*} [Group K] [Group H]
    (h : LieTypeTwoModel K) (e : H ≃* K) : LieTypeTwoModel H := by
  rcases h with h | h | ⟨n, hn, hm⟩
  · exact Or.inl (h.of_mulEquiv e)
  · apply Or.inr ∘ Or.inl
    cases h with
    | linear f hf hm => exact .linear f hf (hm.of_mulEquiv e)
    | symplectic f hf hm => exact .symplectic f hf (hm.of_mulEquiv e)
    | g2 f hf hm => exact .g2 f hf (hm.of_mulEquiv e)
    | triality f hf hm => exact .triality f hf (hm.of_mulEquiv e)
    | ree m hm hi =>
        obtain ⟨d, ⟨a⟩⟩ := hi
        exact .ree m hm ⟨d, ⟨e.trans a⟩⟩
    | symplectic_derived hi => exact .symplectic_derived ⟨e.trans hi.some⟩
    | g2_derived hi => exact .g2_derived ⟨e.trans hi.some⟩
    | tits hi => exact .tits ⟨e.trans hi.some⟩
  · exact Or.inr (Or.inr ⟨n, hn, hm.of_mulEquiv e⟩)

/-- Transport the complete simple-model list without changing any parameter. -/
theorem SimpleModel115.of_mulEquiv {K H : Type*} [Group K] [Group H]
    (h : SimpleModel115 K) (e : H ≃* K) : SimpleModel115 H := by
  cases h with
  | lie hm => exact .lie (lieTypeTwoModel_transport hm e)
  | two_cover hm =>
      exact .two_cover (hm.imp (fun h => h.of_mulEquiv e) (fun h => h.of_mulEquiv e))
  | six hm => exact .six ⟨e.trans hm.some⟩
  | seven hm => exact .seven ⟨e.trans hm.some⟩
  | odd hm =>
      apply SimpleModel115.odd
      rcases hm with hm | ⟨p, hp, hm⟩
      · exact Or.inl (hm.of_mulEquiv e)
      · exact Or.inr ⟨p, hp, hm.of_mulEquiv e⟩
  | sporadic name hn hm => exact .sporadic name hn ⟨e.trans hm.some⟩

private theorem simple_perfect_center {K : Type*} [Group K]
    [IsSimpleGroup K] [Group.IsPerfect K] : center K = ⊥ := by
  rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim

private noncomputable def centerlessQuotientEquiv {K : Type*} [Group K]
    (h : center K = ⊥) : K ⧸ center K ≃* K :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

private theorem alternating_quotient {K : Type*} [Group K] {α : MulAut K}
    {n : ℕ} (hn : 4 ≤ n) {σ : Equiv.Perm (Fin n)}
    (h : AlternatingAction α n σ) :
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n)) := by
  rcases h with ⟨e, _⟩ | ⟨_, _, e, _⟩
  · have hZ : center K = ⊥ := by
      apply bot_unique
      intro x hx
      have he := (centerCongr e ⟨x, hx⟩).property
      change e x ∈ center (alternatingGroup (Fin n)) at he
      have hZA := alternatingGroup.center_eq_bot (α := Fin n) (by simpa using hn)
      have he1 : e x = 1 := by simpa only [hZA, mem_bot] using he
      exact e.injective (he1.trans (map_one e).symm)
    exact ⟨(centerlessQuotientEquiv hZ).trans e⟩
  · exact ⟨e⟩

private theorem fermat_mersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hh : 2 ≤ 2 ^ (2 ^ k) := Nat.le_pow (by positivity)
    omega
  · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
    have hh := dvd_pow_self 2 hk0
    rw [← hk] at hh
    norm_num at hh

private theorem odd_model_center {K : Type*} [Group K] [IsQuasisimple K]
    (h : ClassicalGroup.IsPSL K 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p) : center K = ⊥ := by
  rcases h with ⟨F, _, _, _, ⟨e⟩⟩ | ⟨p, hp, F, _, _, hF, ⟨e⟩⟩
  · let : IsSimpleGroup PSL(3, F) := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup K := e.isSimpleGroup
    exact simple_perfect_center
  · let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    have hn : ¬ Group.IsSolvable PSL(2, F) := by
      intro hs
      let := hs
      exact Group.IsPerfect.not_isSolvable K
        (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    have hfour := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF ▸ fermat_mersenne_odd hp) hn
    let : IsSimpleGroup PSL(2, F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : IsSimpleGroup K := e.isSimpleGroup
    exact simple_perfect_center

/-- The source's six model alternatives give concrete models of the central
quotient. The odd-core conclusion of 15.3.33 supplies Z(K)=O₂(K), so the
sporadic two-core quotient is exactly the required central quotient. -/
theorem simpleModel115_centralQuotient {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hodd : pPrimeCore 2 K = ⊥) {α : MulAut K} (h : ModelAction115 K α) :
    SimpleModel115 (K ⧸ center K) := by
  have hcenter : center K = pCore 2 K := IsQuasisimple.center_eq_pCore hodd
  cases h with
  | lie hs hm _ =>
      let := hs
      exact .lie (lieTypeTwoModel_transport hm (centerlessQuotientEquiv simple_perfect_center))
  | two_cover _ hc hm _ =>
      exact (SimpleModel115.two_cover hm).of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hc)
  | six σ _ ha => exact .six (alternating_quotient (by decide) ha)
  | seven σ _ ha => exact .seven (alternating_quotient (by decide) ha)
  | odd hm _ =>
      exact (SimpleModel115.odd hm).of_mulEquiv (centerlessQuotientEquiv (odd_model_center hm))
  | sporadic name hn hm _ =>
      exact .sporadic name hn ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans hm.some⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo

end
