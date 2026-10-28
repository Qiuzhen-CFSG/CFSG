module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Parabolics
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan

/-!
# Constructing the flag input for the Sylow-normalizer reduction

The completed marked SL₃, Sp₄ and G₂ flag theorem supplies the two literal
residual quotients and their generation of L. These are exactly FlagInput,
so minimal-parabolic uniqueness and the proper component enlargement now
apply without a separate flag-existence or local-model premise. The
exceptional-component recognition and exclusion remain with the line-action
assembly owner, qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, 3.3.15--16, printed pp.590--591, and the
marked natural flag in 11.0.2 and the opening of 11.1, pp.759--761.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The actual marked flags construct the exact residual-model input. -/
theorem exists_flagInput (c : Coordinates D S.field) :
    ∃ f : InvariantFlag c, f.IsUnique ∧ f.IsInnerUnique ∧ FlagInput S f := by
  obtain ⟨f,hf,hi,hq,hg⟩ := exists_unique_marked_flag D S c
  refine ⟨f,hf,hi,?_,hg.symm⟩
  intro i
  exact ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,hq i⟩

/-- Uniqueness identifies every supplied invariant flag with the constructed
marked flag, including its inner uniqueness and residual models. -/
theorem invariantFlag_geometry {c : Coordinates D S.field} (f : InvariantFlag c) :
    f.IsUnique ∧ f.IsInnerUnique ∧ FlagInput S f := by
  obtain ⟨g,hg,hi,P⟩ := exists_flagInput D S c
  have hs : f.space = g.space :=
    funext fun i => hg i (f.space i) (f.dimension i) (f.invariant i)
  have he : f = g := by cases f; cases g; cases hs; rfl
  exact he.symm ▸ ⟨hg,hi,P⟩

/-- The hXU input of the literal 11.2.3 action-step consumer, with the
preceding flag uniqueness supplied by the marked-family theorem. -/
theorem cartan_le_line_normalizer {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X) :
    X ≤ normalizer (f.Vi 0 : Set G) :=
  f.cartan_normalizes (invariantFlag_geometry D S f).2.1 hX 0

/-- The original escape produces a proper normal component at a constructed
flag residual; no FlagInput or minimal-parabolic callback remains. -/
theorem exists_moved_component_of_escape
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ (f : InvariantFlag (coordinates D S)) (A : OddSupplement T)
      (i : Fin 2) (K : Subgroup G),
      FlagInput S f ∧
      Order.HasUniqueMaximalOver (T : Subgroup G) (f.Li i ⊔ (T : Subgroup G)) ∧
      ¬ A.subgroup ≤ normalizer (f.Li i : Set G) ∧
      Source.NormalComponentIn ((f.Li i ⊔ (T : Subgroup G)) ⊔ A.subgroup) K ∧
      f.Li i < K := by
  obtain ⟨f,_,_,P⟩ := exists_flagInput D S (coordinates D S)
  obtain ⟨A⟩ := oddSupplement_nonempty T
  obtain ⟨i,K,hm,hK,hlt⟩ := P.moved_component_source A hescape
  exact ⟨f,A,i,K,P,P.parabolic i,hm,hK,hlt⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
