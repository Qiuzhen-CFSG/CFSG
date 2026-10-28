module

public import Theory.SpecificGroups.Symplectic.FundamentalPlane
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer

/-!
# Split symplectic parabolic sections

The complementary hyperbolic-plane embeddings are retained at the level of
the actual symplectic matrix groups.  Iterating the tail map embeds `Sp₆(F)`
in the literal projective group of every larger rank.  Its range therefore
has a quotient which is the literal `PSp₆(F)`, giving the numerator and map
for the rank-three symplectic parabolic argument.  The proposed parabolic is
the normalizer of the explicit long-root subgroup; its two-local certificate
is the root subgroup. Properness and containment of the numerator are
separate geometric inputs to the consumer in `EvenLie.SplitSections`.

Source: Aschbacher--Smith A.2.18, printed p.40; GLS3 §2.6.
-/

@[expose] public section

noncomputable section
open scoped MatrixGroups
open Theory.GroupTheory
namespace Theory.SpecificGroups.Symplectic

open Theory.SpecificGroups.SymplecticRoot
open Theory.SpecificGroups.Symplectic.FundamentalPlane

variable {F : Type*} [Field F]

/- The first tail is `Sp₃ → Sp₄`; subsequent tails add one hyperbolic plane. -/
def tailIterSp : (n : ℕ) → Matrix.PSp4Three.Sp 3 F →*
    Matrix.PSp4Three.Sp (4 + n) F
  | 0 => tailHom 3
  | n + 1 => (tailHom (4 + n)).comp (tailIterSp n)

@[simp] theorem tailIterSp_zero : tailIterSp (F := F) 0 = tailHom 3 := rfl

@[simp] theorem tailIterSp_succ (n : ℕ) :
    tailIterSp (F := F) (n + 1) = (tailHom (4 + n)).comp (tailIterSp n) := rfl

/- The final projective map is injective because the first tail already kills
   the scalar kernel, and every later tail is projectively injective. -/
theorem tailIterProjective_injective (n : ℕ) :
    Function.Injective (Matrix.PSp4Three.projection.comp
      (tailIterSp (F := F) n)) := by
  induction n with
  | zero =>
      simpa only [tailIterSp_zero, projectTail] using
        (projectTail_injective (F := F) 3)
  | succ n ih =>
      intro x y hxy
      apply ih
      have hprev : tailIterSp (F := F) n x = tailIterSp n y := by
        apply projectTail_injective (F := F) (4 + n)
        simpa only [tailIterSp_succ, MonoidHom.comp_apply, projectTail] using hxy
      exact congrArg (fun z => Matrix.PSp4Three.projection z) hprev

/- The actual embedding of the rank-three symplectic group in the larger
   projective matrix group. -/
def symplecticSixHom (n : ℕ) : Matrix.PSp4Three.Sp 3 F →*
    Matrix.PSp4Three.PSp (4 + n) F :=
  Matrix.PSp4Three.projection.comp (tailIterSp (F := F) n)

theorem symplecticSixHom_injective (n : ℕ) :
    Function.Injective (symplecticSixHom (F := F) n) :=
  tailIterProjective_injective n

def symplecticSixRange (n : ℕ) : Subgroup (Matrix.PSp4Three.PSp (4 + n) F) :=
  (symplecticSixHom (F := F) n).range

/- The root-normalizer parabolic in the literal ambient quotient. -/
def symplecticParabolic (n : ℕ) (i : Fin (4 + n)) :
    Subgroup (Matrix.PSp4Three.PSp (4 + n) F) :=
  Subgroup.normalizer (rootSubgroup (F := F) i :
    Set (Matrix.PSp4Three.PSp (4 + n) F))

theorem symplecticParabolic_isTwoLocal [CharP F 2]
    (n : ℕ) (i : Fin (4 + n)) :
    IsTwoLocal (symplecticParabolic (F := F) n i) :=
  rootNormalizer_isTwoLocal i

/-- The numerator is identified by the original embedding, not by its order. -/
def symplecticSixRangeEquiv (n : ℕ) :
    Matrix.PSp4Three.Sp 3 F ≃* symplecticSixRange (F := F) n :=
  MonoidHom.ofInjective (symplecticSixHom_injective n)

/-- The section map is the central quotient of the embedded Sp₆ factor. -/
def symplecticSixRangeProjection (n : ℕ) :
    symplecticSixRange (F := F) n →* Matrix.PSp4Three.PSp 3 F :=
  Matrix.PSp4Three.projection.comp (symplecticSixRangeEquiv n).symm.toMonoidHom

theorem symplecticSixRangeProjection_surjective (n : ℕ) :
    Function.Surjective (symplecticSixRangeProjection (F := F) n) :=
  (QuotientGroup.mk'_surjective _).comp (symplecticSixRangeEquiv n).symm.surjective

end Theory.SpecificGroups.Symplectic
end
