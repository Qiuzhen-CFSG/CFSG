module

public import Theory.Representation.BinaryOffender.Basic
public import CFSG.Quasithin.ChapterB.Section01.Restriction
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleInvariance

/-!
# The appendix to B.7

The source statements are exported in `ChapterB.Appendix`: B.7.1 restricts
best offenders to the faithful action image on an invariant subspace, preserves
minimality, and gives the faithful-span or nontrivial equal-weight-kernel
alternatives. The rank hypotheses below use the literal relative quotient
`A/C_A(W)` and the vector-space quotient `W/C_W(A)`. The non-strong-offender
consequence in B.7.1(2) is included.

The restriction proof compares the original and restricted weights for every
subgroup containing the kernel. B.7.2(1) then uses the faithful action on a
moved pair of irreducible sections, the residual and central-chief-factor
stabilizer argument, and a partition by the orbit and diagonal in the central
quotient. These proofs are imported from the narrow B.1 prerequisite modules,
without depending on the B.1 or B.6--B.7 umbrellas. The conclusion fixes each
member of the concrete `Irr⁺(H,V)` family, expressed as equality of subspaces.

The older declarations in `ChapterB` are retained for compatibility and labeled
as conditional algebraic helpers. Their source-numbered names do not assert
the source statements; use the exports in `ChapterB.Appendix` below or the
imported `ChapterB.source_lemma_B_7_*` theorems.

Source: *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), B.7.1--B.7.2, printed pp. 118--119.
 -/

namespace CFSG.Quasithin.ChapterB

open Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Faithfulness of a subgroup on a submodule. -/
public def faithfulOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (W : Submodule (ZMod 2) V) : Prop :=
  ∀ a ∈ A, (∀ w : V, w ∈ W → ρ a w = w) → a = 1

namespace Appendix

/-- The legacy faithfulness predicate is exactly triviality of the actual
pointwise action kernel. -/
public theorem faithfulOn_iff_kernel_eq_bot
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (W : Submodule (ZMod 2) V) :
    faithfulOn ρ A W ↔ subspaceKernel ρ W A = ⊥ :=
  (subspaceKernel_eq_bot_iff ρ W A).symm

/-- Translate the image rank and fixed codimension into the literal quotients
in B.7.1. Normality is relative to A, and Aut_G(W) is the stabilizer image. -/
public theorem restriction_rank_eq_iff
    (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (A : Subgroup G) (hW : A ≤ subspaceStabilizer ρ W) :
    letI := subspaceKernel_normal ρ W A hW
    (rank (restrictedSubgroup ρ W A) =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) ↔
    Nat.log 2 (Nat.card (A ⧸ (subspaceKernel ρ W A).subgroupOf A)) =
      Module.finrank (ZMod 2) (W ⧸ (fixedSpace ρ A).comap W.subtype) := by
  let := subspaceKernel_normal ρ W A hW
  rw [rank_restrictedSubgroup_eq_quotient ρ W A hW,
    fixedCodim, fixedSpace_restrictedSubgroup ρ W A hW]

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- B.7.1(1): Aut_A(W) is a best offender in the faithful action of Aut_G(W)
on W, where Aut_G(W) is the image of the stabilizer of W. -/
public theorem lemma_B_7_1_1
    (ρ : Representation (ZMod 2) G V) (hfaithful : Function.Injective ρ)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (W : Submodule (ZMod 2) V)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (hmove : subspaceCommutator ρ W A ≠ ⊥) :
    IsBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) :=
  source_lemma_B_7_1_1 ρ W hfaithful hA hW hmove

/-- B.7.1(2), including its final clause: minimality descends to Aut_A(W);
equality m(A/C_A(W)) = m(W/C_W(A)) forces faithfulness and V = W + C_V(A).
The same follows when the restricted offender is not strong. -/
public theorem lemma_B_7_1_2
    (ρ : Representation (ZMod 2) G V) (hfaithful : Function.Injective ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A) (W : Submodule (ZMod 2) V)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (hmove : subspaceCommutator ρ W A ≠ ⊥) :
    letI := subspaceKernel_normal ρ W A (le_subspaceStabilizer ρ W hW)
    IsMinimalBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) ∧
      (Nat.log 2 (Nat.card (A ⧸ (subspaceKernel ρ W A).subgroupOf A)) =
          Module.finrank (ZMod 2) (W ⧸ (fixedSpace ρ A).comap W.subtype) →
        faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤) ∧
      (¬ IsStrongOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) →
        faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤) := by
  let := subspaceKernel_normal ρ W A (le_subspaceStabilizer ρ W hW)
  obtain ⟨hmin, heq⟩ := source_lemma_B_7_1_2 ρ W hfaithful hA hW hmove
  refine ⟨hmin, ?_, (source_lemma_B_1_5_2 ρ W hfaithful hA hW hmove).2⟩
  intro hquot
  exact heq ((restriction_rank_eq_iff ρ W A (le_subspaceStabilizer ρ W hW)).mpr hquot)

/-- B.7.1(3): at equal quotient ranks, either A acts faithfully on W and
V = W + C_V(A), or its actual nontrivial kernel C_A(W) is an equal-weight
best offender on V. -/
public theorem lemma_B_7_1_3
    (ρ : Representation (ZMod 2) G V) (hfaithful : Function.Injective ρ)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (W : Submodule (ZMod 2) V)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (hmove : subspaceCommutator ρ W A ≠ ⊥) :
    letI := subspaceKernel_normal ρ W A (le_subspaceStabilizer ρ W hW)
    Nat.log 2 (Nat.card (A ⧸ (subspaceKernel ρ W A).subgroupOf A)) =
        Module.finrank (ZMod 2) (W ⧸ (fixedSpace ρ A).comap W.subtype) →
      (faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤) ∨
        (subspaceKernel ρ W A ≠ ⊥ ∧ IsBestOffender ρ (subspaceKernel ρ W A) ∧
          EqualWeightLE ρ (subspaceKernel ρ W A) A) := by
  let := subspaceKernel_normal ρ W A (le_subspaceStabilizer ρ W hW)
  intro hquot
  exact source_lemma_B_7_1_3 ρ W hfaithful hA hW hmove
    ((restriction_rank_eq_iff ρ W A (le_subspaceStabilizer ρ W hW)).mpr hquot)

/-- B.7.2(1): if 1 ≠ H = O²(H) = [H,A] has central 2-chief factors, then
every a ∈ A satisfying [V,a,A] = 0 fixes Irr⁺(H,V) pointwise: each individual
subspace I has Iᵃ = I. The quotient in IsIrrPlus is the actual I/C_I(H). -/
public theorem lemma_B_7_2_1
    (ρ : Representation (ZMod 2) G V) (hfaithful : Function.Injective ρ)
    {A H : Subgroup G} (hA : IsBestOffender ρ A) (hHne : H ≠ ⊥)
    (hres : pResidual 2 H = ⊤) (hHA : ⁅H, A⁆ = H)
    (hchief : Subgroup.HasCentralPChiefFactors 2 H)
    {a : G} (ha : a ∈ A)
    (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) :
    ∀ I : Submodule (ZMod 2) V, IsIrrPlus ρ H I → I.map (ρ a) = I := by
  intro I hI
  exact (subspace_map_eq_iff ρ I a).mpr
    (source_lemma_B_7_2_1 ρ hfaithful hA hHne hres hHA hchief ha hq hI)

end Appendix

/-! ### Legacy conditional helpers (not the source statements) -/

/-- Equal-weight inheritance inside the same representation. This helper does
not construct a restricted action or identify its kernel. -/
public theorem bestOffender_restriction
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hB : IsElementaryTwo B)
    (hBA : EqualWeightLE ρ B A) :
    IsBestOffender ρ B :=
  hA.of_equalWeightLE ρ hB hBA

/-- A minimal best offender has no distinct equal-weight best-offender subgroup.
With the retained `IsElementaryTwo B` premise, equal-weight inheritance makes
these hypotheses inconsistent. This is not restriction of minimality. -/
public theorem minimalBestOffender_restriction
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (_hB : IsElementaryTwo B)
    (hBA : EqualWeightLE ρ B A) (hneq : B ≠ A) :
    ¬ IsBestOffender ρ B := by
  intro hBbest
  exact hneq (hA.2 B hBbest hBA)

/-- Conditional case split for an arbitrary equal-weight subgroup B. The
kernel/span equivalence is assumed, and B is not identified with C_A(W).
Use `Appendix.lemma_B_7_1_3` for the source kernel alternatives. -/
public theorem bestOffender_restriction_alternatives
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G}
    (W : Submodule (ZMod 2) V)
    (hA : IsBestOffender ρ A) (hB : IsElementaryTwo B)
    (hBA : EqualWeightLE ρ B A)
    (kernel_span : B = ⊥ ↔
      faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤) :
    (faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤) ∨
      (IsBestOffender ρ B ∧ EqualWeightLE ρ B A) := by
  by_cases hbot : B = ⊥
  · left
    have h := kernel_span.mp hbot
    exact h
  · right
    exact ⟨bestOffender_restriction ρ hA hB hBA, hBA⟩

/-- Legacy conditional implication with inconsistent premises: an elementary
equal-weight subgroup B of a minimal best offender cannot differ from A.
It supplies neither the source kernel construction nor the rank comparison. -/
public theorem minimalBestOffender_restriction_alternatives
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G}
    (W : Submodule (ZMod 2) V)
    (hA : IsMinimalBestOffender ρ A) (hB : IsElementaryTwo B)
    (hBA : EqualWeightLE ρ B A) (hneq : B ≠ A)
    (kernel_span : B = ⊥ ↔
      faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤) :
    faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤ := by
  apply kernel_span.mp
  by_contra hbot
  have hbest := bestOffender_restriction ρ hA.1 hB hBA
  exact hneq (hA.2 B hbest hBA)

/-! ### Legacy finite-family arithmetic and setwise invariance -/

/-- An abstract finite family with assumed cardinal bounds. No action,
irreducible-section predicate, or diagonal geometry is encoded in this record. -/
public structure B72OrbitData (A I : Type*) [Fintype A] [Fintype I] where
  rank : ℕ
  family_nonempty : 0 < Fintype.card I
  family_bound : Fintype.card I ≤ 2 ^ rank + 1
  actor_bound : 2 ^ rank ≤ Fintype.card A

/-- The assumed bounds give a family size at most one more than the actor size.
This arithmetic implication does not prove the B.7.2 orbit or diagonal bounds. -/
public theorem b72_orbit_card_bound {A I : Type*} [Fintype A] [Fintype I]
    (d : B72OrbitData A I) : Fintype.card I ≤ Fintype.card A + 1 := by
  exact d.family_bound.trans (Nat.add_le_add_right d.actor_bound 1)

/-- An injective image of a finite family contained in that family equals it.
This establishes setwise invariance, not fixation of individual members. -/
public theorem b72_setwise_invariant_of_subset
    {A I : Type*} [Group A] [Finite A] [Finite I] [MulAction A I]
    (a : A) (S : Set I) (hS : S.Finite)
    (hsub : (MulAction.toPerm a : I → I) '' S ⊆ S) :
    (MulAction.toPerm a : I → I) '' S = S := by
  apply (hS.image (MulAction.toPerm a)).eq_of_subset_of_encard_le hsub
  rw [(MulAction.toPerm a).injective.encard_image]

/-! Legacy numbered aliases, preserved with their original types. The source
statements are the names in `ChapterB.Appendix`, not these aliases. -/

/-- Legacy alias for same-representation equal-weight inheritance. -/
public theorem lemma_B_7_1_1
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hB : IsElementaryTwo B)
    (hBA : EqualWeightLE ρ B A) : IsBestOffender ρ B :=
  bestOffender_restriction ρ hA hB hBA

/-- Legacy minimality implication; its elementary equal-weight premises are inconsistent. -/
public theorem lemma_B_7_1_2
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (_hB : IsElementaryTwo B)
    (hBA : EqualWeightLE ρ B A) (hneq : B ≠ A) : ¬ IsBestOffender ρ B :=
  minimalBestOffender_restriction ρ hA _hB hBA hneq

/-- Legacy conditional alternatives with an assumed kernel/span equivalence. -/
public theorem lemma_B_7_1_3
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G}
    (W : Submodule (ZMod 2) V)
    (hA : IsBestOffender ρ A) (hB : IsElementaryTwo B)
    (hBA : EqualWeightLE ρ B A)
    (kernel_span : B = ⊥ ↔
      faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤) :
    (faithfulOn ρ A W ∧ W ⊔ fixedSpace ρ A = ⊤) ∨
      (IsBestOffender ρ B ∧ EqualWeightLE ρ B A) :=
  bestOffender_restriction_alternatives ρ W hA hB hBA kernel_span

/-- Legacy setwise-invariance alias for an arbitrary finite family. It does not
prove pointwise fixation of Irr⁺; use `Appendix.lemma_B_7_2_1`. -/
public theorem lemma_B_7_2_1
    {A I : Type*} [Group A] [Finite A] [Finite I] [MulAction A I]
    (a : A) (S : Set I) (hS : S.Finite)
    (hsub : (MulAction.toPerm a : I → I) '' S ⊆ S) :
    (MulAction.toPerm a : I → I) '' S = S :=
  b72_setwise_invariant_of_subset a S hS hsub

end CFSG.Quasithin.ChapterB
