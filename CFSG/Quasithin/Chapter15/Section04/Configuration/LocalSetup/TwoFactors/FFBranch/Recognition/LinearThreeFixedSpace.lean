module

public import Theory.Representation.PSL3Two.SylowFixedSpace

/-!
# Binary L₃ fixed spaces in the mixed FF comparison

The natural three-space, its dual, and two identically marked copies of either
have a nonidentity cubic actor fixing every Sylow-fixed vector. The permitted
cores below are specified by actual intertwining linear equivalences to those
matrix representations; their definition contains no fixed-space assertion.

For B.4.8(2), the natural quotient has a trivial kernel. For B.4.8(3), the
natural submodule has a trivial quotient. Cubic lifting and odd Sylow-coset
averaging prove the desired fixed-space statement for both orientations,
including nonsplit extensions and arbitrary trivial summands. The final
central-section theorem permits both extensions at once and an actual
embedding into a larger actor, as needed for the product cases of B.5.6.
The exact section maps are allowed to be surjective, but the proof needs only
their equivariance and central kernel.

This is the concrete module calculation for Aschbacher–Smith, *The
Classification of Quasithin Groups*, combined 1 March 2004 manuscript,
B.4.8 and B.5.1, printed pp.91 and 99, and the B.5.6/F.6.18 comparison in
Lemma 15.4.18, printed p.1163. The natural-plus-dual sum is excluded from the
permitted doubled cases, in accordance with B.4.9(2)(ii). Exhaustiveness and
the final quotient identification belong to the recognition assembly.
-/

@[expose] public section

open Representation Representation.BinaryOffender Representation.BinarySylowFixedSpace
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.LinearThreeFixedSpace
open BinaryLinearThree

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Actual module equivalences, retaining the same actor on both summands.
There is deliberately no natural-plus-dual alternative. -/
def IsPermittedCore (σ : Representation (ZMod 2) Group V) : Prop :=
  Nonempty (Representation.Equiv σ BinaryLinearThree.W) ∨
  Nonempty (Representation.Equiv σ BinaryLinearThree.W.dual) ∨
  Nonempty (Representation.Equiv σ (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∨
  Nonempty (Representation.Equiv σ (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual))

private theorem enlargement_of_equiv
    (ρ : Representation (ZMod 2) Group V) (σ : Representation (ZMod 2) Group W)
    (E : Representation.Equiv ρ σ) (S : Sylow 2 Group)
    (h : ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ w ∈ fixedSpace σ (S : Subgroup Group), σ d w = w) :
    ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup Group), ρ d v = v := by
  apply sylow_fixedSpace_enlargement_of_cubic_quotient ρ σ E.toLinearMap
    E.toIntertwiningMap.isIntertwining _ S h
  intro g v hv
  have hz : v = 0 := E.toLinearEquiv.injective (hv.trans E.toLinearEquiv.map_zero.symm)
  rw [hz, map_zero]

/-- Every one of the four concrete core actions has a cubic fixed-space witness. -/
theorem core_enlargement (σ : Representation (ZMod 2) Group V)
    (hσ : IsPermittedCore σ) (S : Sylow 2 Group) :
    ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace σ (S : Subgroup Group), σ d v = v := by
  unfold IsPermittedCore at hσ
  rcases hσ with h | h | h | h
  · exact enlargement_of_equiv σ _ (Classical.choice h) S (SylowFixedSpace.exists_cubic_fixer_natural S)
  · exact enlargement_of_equiv σ _ (Classical.choice h) S (SylowFixedSpace.exists_cubic_fixer_dual S)
  · exact enlargement_of_equiv σ _ (Classical.choice h) S (SylowFixedSpace.exists_cubic_fixer_doubled_natural S)
  · exact enlargement_of_equiv σ _ (Classical.choice h) S (SylowFixedSpace.exists_cubic_fixer_doubled_dual S)

/-- A trivial kernel below the natural module, as in B.4.8(2).
In particular any trivial direct summands are retained. -/
theorem trivialKernel_enlargement
    (ρ : Representation (ZMod 2) Group V) (σ : Representation (ZMod 2) Group W)
    (hσ : IsPermittedCore σ) (q : ρ.IntertwiningMap σ)
    (hker : ∀ g v, q v = 0 → ρ g v = v) (S : Sylow 2 Group) :
    ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup Group), ρ d v = v :=
  sylow_fixedSpace_enlargement_of_cubic_quotient ρ σ q.toLinearMap
    q.isIntertwining hker S (core_enlargement σ hσ S)

/-- A natural submodule with trivial quotient, as in B.4.8(3).
The injection and displacement hypothesis are the honest extension data. -/
theorem trivialQuotient_enlargement
    (ρ : Representation (ZMod 2) Group V) (σ : Representation (ZMod 2) Group W)
    (hσ : IsPermittedCore σ) (i : σ.IntertwiningMap ρ) (hi : Function.Injective i)
    (hquot : ∀ g v, ρ g v - v ∈ i.toLinearMap.range) (S : Sylow 2 Group) :
    ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup Group), ρ d v = v := by
  obtain ⟨d, hd, hc, hf⟩ := core_enlargement σ hσ S
  exact ⟨d, hd, hc, fixes_of_trivial_quotient ρ σ i hi hquot S hf⟩

/-- Both extension orientations in B.4.8 and arbitrary trivial summands.
The central kernel and the quotient above U may both be nonsplit.
An actual embedding also allows an L₃(2) factor in a larger actor. -/
theorem centralSection_enlargement
    {D : Type*} [_root_.Group D] [Finite D]
    (ρ : Representation (ZMod 2) D V) (f : Group →* D) (hf : Function.Injective f)
    (σ : Representation (ZMod 2) Group W) (hσ : IsPermittedCore σ)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] W)
    (hq : ∀ g u, q (U.toRepresentation g u) = σ g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let T := FanoDecomposition.flagSylow
  obtain ⟨d, hd, hc, hfix⟩ := sylow_fixedSpace_enlargement_of_central_section
    (ρ.comp f) σ U q hq hker hquot T (core_enlargement σ hσ T)
  exact sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf
    (T : Subgroup Group) T.isPGroup' d hc (fun he => hd (he ▸ T.one_mem)) hfix S

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.LinearThreeFixedSpace
