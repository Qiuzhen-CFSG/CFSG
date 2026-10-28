module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates

/-!
# Transport of marked actions on the literal two-node subgroups

Relabeling the two nodes gives subgroup inclusions, including reversal and
repetition. Restricting a marked action along these inclusions preserves both
signs and the original parameter. A faithful matrix model also gives a marked
action: pull the literal subgroup back into the model, then apply its linear
representation. The model's two generator comparisons remain explicit.

These are construction tools, not assertions that the required models exist.
The finite-case assembly is in `PairActions`. The concrete comparisons needed
for the folded inclusion use the common-lattice construction of GLS3 §2.6
(`refs/KGroup/GLS3/chapter2.tex`) and Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open WordDescent

variable (F : Type*) [Field F]

/-- Data to be constructed on the actual subgroup, with its exact marking. -/
structure PairAction (i j : Fin 4) where
  hom : pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F)
  map_generator : ∀ (s k : Bool) (t : F),
    hom (pairGenerator F i j s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t)

/-- Relabeling generators gives containment of the literal matrix subgroups. -/
theorem pairSubgroup_le_of_relabel {i j a b : Fin 4} (f : Bool → Bool)
    (hf : ∀ k, pairNode i j k = pairNode a b (f k)) :
    pairSubgroup F i j ≤ pairSubgroup F a b := by
  rw [pairSubgroup_eq_closure, Subgroup.closure_le]
  rintro _ ⟨⟨s, k, t⟩, rfl⟩
  change coverSimple F s (pairNode i j k) t ∈ pairSubgroup F a b
  rw [hf k]
  simpa only [pairGenerator_val] using (pairGenerator F a b s (f k) t).property

/-- The inclusion is the identity on the original cover elements. -/
def pairRelabel {i j a b : Fin 4} (f : Bool → Bool)
    (hf : ∀ k, pairNode i j k = pairNode a b (f k)) :
    pairSubgroup F i j →* pairSubgroup F a b :=
  Subgroup.inclusion (pairSubgroup_le_of_relabel F f hf)

@[simp] theorem pairRelabel_generator {i j a b : Fin 4} (f : Bool → Bool)
    (hf : ∀ k, pairNode i j k = pairNode a b (f k)) (s k : Bool) (t : F) :
    pairRelabel F f hf (pairGenerator F i j s k t) =
      pairGenerator F a b s (f k) t := by
  apply Subtype.ext
  change (pairGenerator F i j s k t).val = (pairGenerator F a b s (f k) t).val
  simp only [pairGenerator_val, hf]

namespace PairAction

variable {F}

/-- Restriction along a relabeling; no quotient or parameter change is made. -/
def relabel {i j a b : Fin 4} (ρ : PairAction F a b) (f : Bool → Bool)
    (hf : ∀ k, pairNode i j k = pairNode a b (f k)) : PairAction F i j where
  hom := ρ.hom.comp (pairRelabel F f hf)
  map_generator s k t := by
    rw [MonoidHom.comp_apply, pairRelabel_generator, ρ.map_generator, hf]

def reverse {i j : Fin 4} (ρ : PairAction F i j) : PairAction F j i :=
  ρ.relabel Bool.not (by intro k; cases k <;> rfl)

def repeatLeft {i j : Fin 4} (ρ : PairAction F i j) : PairAction F i i :=
  ρ.relabel (fun _ => true) (by intro k; cases k <;> rfl)

def repeatRight {i j : Fin 4} (ρ : PairAction F i j) : PairAction F j j :=
  ρ.relabel (fun _ => false) (by intro k; cases k <;> rfl)

end PairAction

section FaithfulModel
variable {G : Type*} [Group G] (i j : Fin 4)
  (ι : G →* Cover F) (hι : Function.Injective ι)
  (x : Bool → Bool → F → G)
  (hx : ∀ s k t, ι (x s k t) = coverSimple F s (pairNode i j k) t)

include x hx in
/-- The two pinned model curves suffice for containment in the model's range. -/
theorem pairSubgroup_le_model_range : pairSubgroup F i j ≤ ι.range := by
  rw [pairSubgroup_eq_closure, Subgroup.closure_le]
  rintro _ ⟨⟨s, k, t⟩, rfl⟩
  exact ⟨x s k t, hx s k t⟩

/-- Pull the actual subgroup into a faithful model. Surjectivity onto the whole
model is unnecessary for constructing the action. -/
def pairModelLift : pairSubgroup F i j →* G :=
  (MonoidHom.ofInjective hι).symm.toMonoidHom.comp
    (Subgroup.inclusion (pairSubgroup_le_model_range F i j ι x hx))

@[simp] theorem pairModelLift_generator (s k : Bool) (t : F) :
    pairModelLift F i j ι hι x hx (pairGenerator F i j s k t) = x s k t := by
  apply hι
  change ι ((MonoidHom.ofInjective hι).symm _) = _
  rw [MonoidHom.apply_ofInjective_symm]
  exact (pairGenerator_val F i j s k t).trans (hx s k t).symm

/-- A faithful concrete model and its marked linear action descend to the
literal subgroup, without any global word-descent assumption. -/
def pairActionOfFaithfulModel
    (σ : G →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hσ : ∀ s k t, σ (x s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t)) : PairAction F i j where
  hom := σ.comp (pairModelLift F i j ι hι x hx)
  map_generator s k t := by
    rw [MonoidHom.comp_apply, pairModelLift_generator, hσ]

/-- Original E6 column differences verify the target half of a model comparison.
This criterion does not require irreducibility, including in characteristic three. -/
def pairActionOfFaithfulModelOnColumns (htwo : (2 : F) ≠ 0)
    (σ : G →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hσ : ∀ (s k : Bool) (t : F) (c r : Index),
      (σ (x s k t) (antiVector F c) : Space F) r =
        foldedMatrix F (f4Simple F s (pairNode i j k) t) r c -
          foldedMatrix F (f4Simple F s (pairNode i j k) t) r
            (Theory.AlgebraicGroup.StandardRootSystem.typeE6PinnedIndexEquiv c)) :
    PairAction F i j :=
  pairActionOfFaithfulModel F i j ι hι x hx σ fun s k t =>
    linearEquiv_eq_eigenspaceAction F htwo _ _ (hσ s k t)

end FaithfulModel
end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
