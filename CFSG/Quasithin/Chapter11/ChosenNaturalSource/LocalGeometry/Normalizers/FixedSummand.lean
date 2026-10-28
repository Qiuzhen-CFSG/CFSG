module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Alternatives
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PlaneOrbit

/-!
# Reduction of the fixed-summand step to the two source constructions

The actual Sylow subgroup preserves C_{Z₁}(L), so its image in Y/C_Y(Z₁)
excludes both even-orbit GO cases. The invariant case gives the desired
ambient normalization. In the exceptional case, normalization of V in the
linear block, or of V₃ and L₁ in the symplectic block, contradicts escape
by maximal-local uniqueness or the proved 11.1.4 reduction.

The TI/Cartan construction and the exceptional block actions are explicit
remaining premises. This module does not assert that 11.1.5 is complete.
Source: Aschbacher--Smith, 11.1.5, printed p.766.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- On the actual source quotient, Sylow invariance leaves only the
singleton fixed-space orbit and the genuine order-21 action. -/
theorem chosen_invariant_or_exceptional
    (D : ChosenModule T L V) {F : BinaryField} {c : Coordinates D F}
    (f : InvariantFlag c) (X : Subgroup G)
    (hpair : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) ∨
      ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) := by
  let P : Sylow 2 (normalizer (f.Ri 0 : Set G)) := T.subtype (sylow_normalizes_Ri f 0)
  let Pstar : Sylow 2 (Actor (f.Ri 0)) :=
    P.mapSurjective (f := projection (f.Ri 0)) (QuotientGroup.mk'_surjective _)
  have hP : (Pstar : Subgroup (Actor (f.Ri 0))) ≤
      subspaceStabilizer (representation (f.Ri 0))
        (fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) := by
    rw [hfixed]
    change (P : Subgroup _).map (projection (f.Ri 0)) ≤ _
    rw [map_le_iff_le_comap, stabilizer_comap]
    intro y hy
    exact sylow_normalizes_fixed D f hy
  rcases invariant_or_exceptional_of_sylow hpair Pstar hP with hi | he
  · rw [hfixed] at hi
    exact Or.inl (normalizes_fixed_of_invariant _ _ hi)
  · exact Or.inr he

/-- Either literal block action supplies the terminal contradiction.
The hypotheses concern the original seed/flag, not an unrelated model. -/
theorem exceptional_escape_contradiction
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcontrol : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G)))
    (haction : normalizer (f.Ri 0 : Set G) ≤ normalizer (V : Set G) ∨
      normalizer (f.Ri 0 : Set G) ≤
        normalizer (f.Vi 2 : Set G) ⊓ normalizer (f.Li 0 : Set G)) : False := by
  apply hescape
  rcases haction with hv | h₃
  · exact hv.trans (chosen_seed_normalizer_le D S)
  · exact h₃.trans hcontrol.2

/-- Conditional completion of the GO step, retaining only the Cartan/TI
construction and the exceptional block action as new source obligations.
Their hypotheses are discharged by separate source producers, not here. -/
theorem chosen_fixed_of_pair_and_block_action
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcontrol : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G)))
    (hpair : radicalFixedCenter (f.Ri 0) L ≠ ⊥ →
      ∃ X : Subgroup G, IsCartan T L X ∧ X ≤ normalizer (f.Ri 0 : Set G) ∧
        Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) ∧
        fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
          fixedSubspace (f.Ri 0) L)
    (hblock : ∀ X : Subgroup G, IsCartan T L X → X ≤ normalizer (f.Ri 0 : Set G) →
      Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) →
      fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
        fixedSubspace (f.Ri 0) L →
      ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (V : Set G) ∨
        normalizer (f.Ri 0 : Set G) ≤
          normalizer (f.Vi 2 : Set G) ⊓ normalizer (f.Li 0 : Set G)) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) := by
  by_cases hz : radicalFixedCenter (f.Ri 0) L = ⊥
  · rw [hz, Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))]
    exact le_top
  obtain ⟨X, hX, hXY, hp, hf⟩ := hpair hz
  rcases chosen_invariant_or_exceptional D f X hp hf with hn | he
  · exact hn
  · exact (exceptional_escape_contradiction D S f hescape hcontrol
      (hblock X hX hXY hp hf he)).elim

/-- The outstanding Cartan/TI construction, stated on the literal source
objects. The earlier block, center and seed-span results may be inputs. -/
def PairConstruction (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) : Prop :=
  (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
  V = Source.conjugateSpan (normalizer (L : Set G)) V →
  (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
  radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
  radicalFixedCenter (f.Ri 0) L ≠ ⊥ →
  ∃ X : Subgroup G, IsCartan T L X ∧ X ≤ normalizer (f.Ri 0 : Set G) ∧
    Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) ∧
    fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L

/-- The outstanding exceptional block calculation. Its output names the
literal V or the literal V₃ and L₁; a family tag cannot supply it. -/
def ExceptionalBlockActions (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) : Prop :=
  (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
  V = Source.conjugateSpan (normalizer (L : Set G)) V →
  (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
  radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
  ∀ X : Subgroup G, IsCartan T L X → X ≤ normalizer (f.Ri 0 : Set G) →
    Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) →
    fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L →
    ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) →
    normalizer (f.Ri 0 : Set G) ≤ normalizer (V : Set G) ∨
      normalizer (f.Ri 0 : Set G) ≤
        normalizer (f.Vi 2 : Set G) ⊓ normalizer (f.Li 0 : Set G)

/-- Application to the original radical-alternative assembly. This
discharges its hfixed slot conditionally on the two named source tasks;
all remaining inputs must still be supplied by their assembly owners. -/
theorem chosen_radicalAlternative_of_constructions
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hcontrol : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G)))
    (hblocks : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L))
    (hcenter : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hpair : PairConstruction D S f) (hblock : ExceptionalBlockActions D S f) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  apply chosen_radicalAlternative_of_source_steps D S f hblocks hcenter
  intro he hb hc
  exact chosen_fixed_of_pair_and_block_action D S f he hcontrol
    (hpair he (hblocks he).1 hb hc) (hblock he (hblocks he).1 hb hc)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
