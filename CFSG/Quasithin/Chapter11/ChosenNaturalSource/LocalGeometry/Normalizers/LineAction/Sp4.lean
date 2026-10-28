module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Sp4Movement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.MSInputs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2

/-!
# The symplectic line-normalizer reduction

For the actual Sp₄ marking, an escaping Sylow normalizer yields both the
literal MS-pair (L,T) and the J₁ terminal configuration. Shortness of L
then gives the bound on [X,T]; the marked residual moves this subgroup,
contradicting the J₁ action obstruction. The original Frattini consumer
now proves both 11.2.3 conclusions from shortness.

The input IsShort L is not asserted here: the intrinsic nonbinary
symplectic MS theorem is owned by qt-c132-nonbinary-symplectic, and its
application and final discharge stay with qt-d-1222-natural-line-action.
The authorized radical alternative stays with the final source assembly
qt-d-1222-natural-normalizer-source. No field-four case is discarded.

Source: Aschbacher--Smith 3.3.16, p.591; 11.2.3, pp.768--769.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- The escaping source branch has all literal MS inputs and the actual J₁ configuration. -/
theorem sp4_ms_janko_of_escape (f : InvariantFlag (Coordinates.sp4 m))
    (A : SylowNormalizer.OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    PointBlocks.NonbinaryMSPair S.field L (T : Subgroup G) ∧
      Nonempty (SylowNormalizer.JankoConfiguration S f A) :=
  ⟨SylowNormalizer.sylow_msPair_of_escape D S (Coordinates.sp4 m) hescape,
    SylowNormalizer.exists_janko_configuration f A hescape⟩

include D S m in
/-- The complete displacement argument for the symplectic short branch. -/
theorem sp4_sylow_normalizer_le_of_short (hb : ChapterC.IsShort L) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  obtain ⟨A⟩ := SylowNormalizer.oddSupplement_nonempty T
  obtain ⟨_,⟨E⟩⟩ := sp4_ms_janko_of_escape D S m (Sp4.flag m S) A hescape
  exact SylowNormalizer.Sp4Terminal.false_of_short D S m E hb

/-- Both original 11.2.3 conclusions once the symplectic MS output gives shortness. -/
theorem chosen_sp4_source_11_2_3_of_short
    (f : InvariantFlag (Coordinates.sp4 m)) {X : Subgroup G} (hX : IsCartan T L X)
    (hb : ChapterC.IsShort L)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_source_11_2_3_of_sylow_normalizer D S f hX
    (sp4_sylow_normalizer_le_of_short D S m hb) hradical

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
