module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Coordinates

/-!
# Checked multiplication paths in the local matrix image

Every step records an actual right multiplication by smallX or smallY and the
resulting eight packed rows. The checker uses only packed arithmetic; its
soundness theorem supplies membership in the literal generated subgroup.
Recording each intermediate matrix avoids repeated reduction of long products.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
open Packed
abbrev Rows := Fin 8 → ℕ
abbrev Step := Bool × Rows

def generator (b : Bool) : SmallAmbient := if b then smallY else smallX
def generatorRows (b : Bool) : Rows := if b then Matrices.smallYRows else Matrices.smallXRows

theorem generator_val (b : Bool) : (generator b).val = decode (generatorRows b) := by
  cases b <;> rfl

theorem generator_mem (b : Bool) : generator b ∈ smallGenerated := by
  cases b
  · exact Subgroup.subset_closure (by simp [generator])
  · exact Subgroup.subset_closure (by simp [generator])

def Valid : Rows → List Step → Prop
  | _, [] => True
  | a, s :: ss => product a (generatorRows s.1) = s.2 ∧ Valid s.2 ss

instance (a : Rows) (ss : List Step) : Decidable (Valid a ss) := by
  induction ss generalizing a with
  | nil => exact isTrue trivial
  | cons s ss ih => exact instDecidableAnd

def lastRows : Rows → List Step → Rows
  | a, [] => a
  | _, s :: ss => lastRows s.2 ss

theorem valid_mem (a : Rows) (ss : List Step) (h : Valid a ss)
    (ha : ∃ g ∈ smallGenerated, g.val = decode a) :
    ∃ g ∈ smallGenerated, g.val = decode (lastRows a ss) := by
  induction ss generalizing a with
  | nil => exact ha
  | cons s ss ih =>
    obtain ⟨g, hg, hv⟩ := ha
    apply ih s.2 h.2
    refine ⟨g * generator s.1, smallGenerated.mul_mem hg (generator_mem _), ?_⟩
    change g.val * (generator s.1).val = decode s.2
    rw [hv, generator_val]
    exact mul_eq_of_certificate _ _ _ h.1

theorem word_mem (ss : List Step) (h : Valid (Matrices.identityRows 8) ss) :
    ∃ g ∈ smallGenerated, g.val = decode (lastRows (Matrices.identityRows 8) ss) :=
  valid_mem _ _ h ⟨1, smallGenerated.one_mem, (Matrices.decode_identity 8).symm⟩

end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
