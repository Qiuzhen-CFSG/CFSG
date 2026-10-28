module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerChosenCover
public import Theory.Representation.G2NaturalExtensions.DerivedFixedSpaces

/-!
# Fixed vectors lifted through the chosen G₂ central cover

The central six-dimensional marking of the chosen module has the literal
cover supplied by `ChosenCover.projection`.  The universal binary G₂ cover
then lifts a fixed natural vector to a fixed vector in the chosen section.
Transporting the resulting quotient equality through `spaceEquiv` gives the
original conjugation equality in `V`; the actor remains the specified
`L / O₂(L)` quotient.

Source: Aschbacher--Smith B.4.6(7), I.2.3(1), and 12.2.16, pp.88, 413, 800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.OneCohomology
open Atlas.G2.Natural

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

local notation "F" => ZMod 2
namespace ChosenCover

variable (D : ChosenModule T L V)
  (e : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
    (g2DerivedNatural F))

/-- A fixed natural image lifts to a fixed vector in the chosen section. -/
theorem derived_fixed_of_natural_fixed
    (l : L) (v : V)
    (hv : g2DerivedNatural F
      (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
      ((point D e v).toAdd) = (point D e v).toAdd) :
    D.chosenAction l (D.spaceEquiv.symm v).toAdd =
      (D.spaceEquiv.symm v).toAdd := by
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hcover : IsCover (ChosenCover.projection D e) :=
      ChosenCover.isCover D e
  have hnat : g2DerivedNatural F
      (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
      ((ChosenCover.projection D e) w) =
      (ChosenCover.projection D e) w := by
    simpa only [point_toAdd] using hv
  have hfix := Atlas.G2.Natural.Extensions.derived_fixed_of_natural_fixed
    (σ := ChosenCover.action D e) (V := D.space)
    (p := ChosenCover.projection D e) hcover
    (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) w hnat
  have hquot : D.quotientAction (QuotientGroup.mk' (pCore 2 L) l) w = w := by
    rw [← ChosenCover.action_apply D e]
    exact hfix
  simpa only [D.quotientAction_mk] using hquot

/-- The lifted equality is the literal ambient conjugation equality. -/
theorem ambient_derived_fixed_of_natural_fixed
    (l : L) (v : V)
    (hv : g2DerivedNatural F
      (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
      ((point D e v).toAdd) = (point D e v).toAdd) :
    V.normalizerMonoidHom ⟨l, D.normalizes l.property⟩ v = v := by
  have hfix := derived_fixed_of_natural_fixed D e l v hv
  have hcoord := congrArg
    (fun w : D.space => D.spaceEquiv (Multiplicative.ofAdd w)) hfix
  have hact : D.spaceEquiv
      (Multiplicative.ofAdd (D.chosenAction l (D.spaceEquiv.symm v).toAdd)) =
      V.normalizerMonoidHom ⟨l, D.normalizes l.property⟩ v := by
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    have he := (D.spaceEquiv_apply (D.spaceEquiv.symm v).toAdd).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
    change (l : G) * ((D.spaceEquiv.symm v).toAdd.val.toMul.val : G) *
      (l : G)⁻¹ = _
    rw [he]
    rfl
  rw [hact] at hcoord
  exact hcoord.trans (by simp)

end ChosenCover
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
