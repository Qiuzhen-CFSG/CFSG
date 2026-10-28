module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.DegreeBounds
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.Model
public import Theory.SpecificGroups.Tits.Presentation

/-!
# Transport for the twisted-family exclusions in G.9.3

The original elementary abelian actor embeds in the automorphism group of
the irreducible component. Perfectness makes descent to the component's
central quotient faithful, so estimates for that quotient bound the original
actor. In particular the already proved Suzuki estimate needs no additional
automorphism hypothesis.

For representations, an actual model isomorphism preserves faithfulness and
irreducibility. A surjection from the special unitary group preserves
irreducibility and nontriviality, but need not preserve faithfulness. This
distinction permits both SU₃ and PSU₃ in the universal-cover step.

The exclusion lemmas below still take universal model degree estimates as
explicit premises. Except for Suzuki, the automorphism estimates also remain
premises. This module does not claim that those representation-theoretic or
automorphism theorems have been proved. It supplies their connection to the
original G.9 hypotheses; final assembly must discharge every estimate.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed p.356
(PDF p.367), and the cover alternatives A.3.6(1),(2), printed p.43.
GLS3 §2.8 supplies the defining-characteristic representation argument still
needed. Suzuki and Ree have field exponent `2*k+1`, with `k ≥ 1`; the
smallest Ree derived group uses `Tits.ParrottGroup` separately. The unitary
exponent measures the fixed field; its matrix field has twice that degree.
Triality uses only the genuine D4 graph-field carrier.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

universe u v w

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

private theorem actor_rank_le
    (h : ComponentHypothesis K ρ A L L m) : m ≤ primeRank 2 (MulAut L) := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  apply h.toSetup.rank_le_automorphisms
  rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
  exact le_top

/-- The model estimate applies to automorphisms of the central quotient,
even when the component has a nontrivial center. -/
theorem actor_rank_le_of_central_quotient
    (h : ComponentHypothesis K ρ A L L m)
    {S : Type w} [Group S] [Finite S]
    (e : (L ⧸ center L) ≃* S) {r : ℕ}
    (hr : primeRank 2 (MulAut S) ≤ r) : m ≤ r := by
  let : IsQuasisimple L := h.component.2
  have hquot := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hquot
  exact (actor_rank_le h).trans (hquot.trans hr)

/-- The full Suzuki actor estimate is unconditional on representation theory
and applies to every perfect central cover with the stated quotient. -/
theorem suzuki_actor_rank_le
    (h : ComponentHypothesis K ρ A L L m) {k : ℕ} (hk : 1 ≤ k)
    (e : (L ⧸ center L) ≃* SuzukiMatrixGroup k) : m ≤ 2 * k + 1 :=
  actor_rank_le_of_central_quotient h e (suzuki_automorphism_two_rank k hk)

/-- A surjective covering action is nontrivial because the original component
acts faithfully and does not centralize the actor. No faithfulness of the
inflated representation is asserted. -/
theorem cover_action_nontrivial
    (h : ComponentHypothesis K ρ A L L m)
    {U : Type w} [Group U] (π : U →* L) (hπ : Function.Surjective π) :
    ∃ g : U, ((ρ.comp L.subtype).comp π) g ≠ 1 := by
  by_contra! hzero
  have hL : L = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    change x = 1
    obtain ⟨g, hg⟩ := hπ ⟨x, hx⟩
    apply h.faithful
    calc
      ρ x = ((ρ.comp L.subtype).comp π) g := by rw [MonoidHom.comp_apply, hg]; rfl
      _ = 1 := hzero g
      _ = ρ 1 := (map_one ρ).symm
  exact h.noncentral (by rw [hL, Subgroup.commutator_bot_left])

/-- Universal bounds for nontrivial irreducibles descend through a surjection.
This is the step needed for quotients of the special unitary group. -/
theorem degree_ge_of_cover
    (h : ComponentHypothesis K ρ A L L m)
    {U : Type w} [Group U] (π : U →* L) (hπ : Function.Surjective π)
    {b : ℕ}
    (hdegree : ∀ σ : Representation (ZMod 2) U V,
      σ.IsIrreducible → (∃ g, σ g ≠ 1) → b ≤ Module.finrank (ZMod 2) V) :
    b ≤ Module.finrank (ZMod 2) V := by
  apply hdegree ((ρ.comp L.subtype).comp π)
  · exact (Representation.irreducible_comp_surjective_iff π hπ
      (ρ.comp L.subtype)).mpr h.irreducible
  · exact cover_action_nontrivial h π hπ

/-- An actual family isomorphism transfers a bound for all faithful irreducibles
on the concrete carrier. The vector space and its binary degree are unchanged. -/
theorem degree_ge_of_model
    (h : ComponentHypothesis K ρ A L L m)
    {S : Type w} [Group S] (e : L ≃* S) {b : ℕ}
    (hdegree : ∀ σ : Representation (ZMod 2) S V,
      σ.IsIrreducible → Function.Injective σ → b ≤ Module.finrank (ZMod 2) V) :
    b ≤ Module.finrank (ZMod 2) V := by
  apply hdegree ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
  · exact (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective (ρ.comp L.subtype)).mpr h.irreducible
  · exact (h.faithful.comp L.subtype_injective).comp e.symm.injective

private theorem actor_rank_le_of_model
    (h : ComponentHypothesis K ρ A L L m)
    {S : Type w} [Group S] [Finite S] (e : L ≃* S) {r : ℕ}
    (hr : primeRank 2 (MulAut S) ≤ r) : m ≤ r := by
  have hh := actor_rank_le h
  rw [primeRank_equiv 2 (MulAut.congr e)] at hh
  exact hh.trans hr

/-- Both unitary alternatives in A.3.6 have a genuine central surjection
from the same special-unitary matrix group. No multiplier assertion is
needed to construct this map once the source supplies either isomorphism. -/
theorem exists_unitary_cover
    {D : Type*} [Group D] {F : Type w} [Field F] (J : HermitianForm 3 F)
    (model : Nonempty (D ≃* J.specialSubgroup) ∨
      Nonempty (D ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ π : J.specialSubgroup →* D,
      Function.Surjective π ∧ π.ker ≤ center J.specialSubgroup := by
  rcases model with hs | hp
  · obtain ⟨e⟩ := hs
    refine ⟨e.symm.toMonoidHom, e.symm.surjective, ?_⟩
    rw [e.symm.toMonoidHom.ker_eq_bot e.symm.injective]
    exact bot_le
  · obtain ⟨e⟩ := hp
    refine ⟨e.symm.toMonoidHom.comp J.specialToProjective,
      e.symm.surjective.comp J.specialToProjective_surjective, ?_⟩
    intro x hx
    apply J.specialToProjective_ker_le_center
    change e.symm (J.specialToProjective x) = 1 at hx
    exact e.symm.injective (hx.trans e.symm.map_one.symm)

/-- The Suzuki exclusion once its universal faithful binary minimum is proved.
Its automorphism estimate has already been discharged. -/
theorem not_suzuki_of_degree_bound
    (h : ComponentHypothesis K ρ A L L m) {k : ℕ} (hk : 1 ≤ k)
    (e : L ≃* SuzukiMatrixGroup k)
    (hdegree : ∀ σ : Representation (ZMod 2) (SuzukiMatrixGroup k) V,
      σ.IsIrreducible → Function.Injective σ →
        4 * (2 * k + 1) ≤ Module.finrank (ZMod 2) V) : False := by
  exact DegreeBounds.not_suzuki (by omega)
    (actor_rank_le_of_model h e (suzuki_automorphism_two_rank k hk))
    (degree_ge_of_model h e hdegree) h.degree_le

/-- The unitary exclusion uses the actual universal special-unitary cover and
the actual projective central quotient. Both representation and rank estimates
are explicit, still undischarged inputs. -/
theorem not_unitary_three_of_estimates
    (h : ComponentHypothesis K ρ A L L m)
    {F : Type w} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n)
    (_hcard : Nat.card F = (2 ^ n) ^ 2) (_hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (model : Nonempty (L ≃* J.specialSubgroup) ∨
      Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (e : (L ⧸ center L) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hdegree : ∀ σ : Representation (ZMod 2) J.specialSubgroup V,
      σ.IsIrreducible → (∃ g, σ g ≠ 1) → 6 * n ≤ Module.finrank (ZMod 2) V)
    (hrank : primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ n + 1) :
    False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective e e.surjective
  obtain ⟨π, hπ, _⟩ := exists_unitary_cover J model
  exact DegreeBounds.not_unitary_three hn
    (actor_rank_le_of_central_quotient h e hrank)
    (degree_ge_of_cover h π hπ hdegree) h.degree_le

/-- The triality exclusion uses the genuine standard graph-field carrier,
including the positive exponent one. -/
theorem not_triality_of_estimates
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 0 < n)
    (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) L)
    (hdegree : ∀ σ : Representation (ZMod 2) (Triality.Standard.BinaryCarrier n hn) V,
      σ.IsIrreducible → Function.Injective σ → 24 * n ≤ Module.finrank (ZMod 2) V)
    (hrank : primeRank 2 (MulAut (Triality.Standard.BinaryCarrier n hn)) ≤ 5 * n) :
    False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff L n hn).mp model
  exact DegreeBounds.not_triality hn (actor_rank_le_of_model h e hrank)
    (degree_ge_of_model h e hdegree) h.degree_le

/-- The Ree exclusion for the genuine odd exponents at least three.
The full nonsimple group at exponent one is not an admissible endpoint. -/
theorem not_ree_of_estimates
    (h : ComponentHypothesis K ρ A L L m) {k : ℕ} (hk : 1 ≤ k)
    (e : L ≃* ReeF4.Model k)
    (hdegree : ∀ σ : Representation (ZMod 2) (ReeF4.Model k) V,
      σ.IsIrreducible → Function.Injective σ →
        26 * (2 * k + 1) ≤ Module.finrank (ZMod 2) V)
    (hrank : primeRank 2 (MulAut (ReeF4.Model k)) ≤ 5 * (2 * k + 1)) : False := by
  exact DegreeBounds.not_ree (by omega) (actor_rank_le_of_model h e hrank)
    (degree_ge_of_model h e hdegree) h.degree_le

/-- The exponent-one derived endpoint uses the catalogue's Parrott carrier.
Its finiteness is inherited from the actual component isomorphism. -/
theorem not_tits_of_estimates
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* Tits.ParrottGroup)
    (hdegree : ∀ σ : Representation (ZMod 2) Tits.ParrottGroup V,
      σ.IsIrreducible → Function.Injective σ → 26 ≤ Module.finrank (ZMod 2) V)
    (hrank : primeRank 2 (MulAut Tits.ParrottGroup) ≤ 5) : False := by
  let : Finite Tits.ParrottGroup := Finite.of_surjective e e.surjective
  exact DegreeBounds.not_ree (n := 1) (by decide) (actor_rank_le_of_model h e hrank)
    (degree_ge_of_model h e hdegree) h.degree_le

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
