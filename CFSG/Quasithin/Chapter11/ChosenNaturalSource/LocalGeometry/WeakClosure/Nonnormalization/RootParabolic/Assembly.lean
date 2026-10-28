module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Offenders
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Cover

/-!
# Conditional assembly for the first two stages of 11.2.4

Field-line recognition is connected to the genuine ambient alignment theorem.
Uniform exclusion, including every replacement inside L₂, turns the four
parabolic action calculations into the literal output used by the published
nonnormalization reduction. These calculations remain unproved premises here;
this module does not establish source 11.2.4.

Source: Aschbacher--Smith, 11.2.4, printed p.769.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The precise remaining root-recognition output. The line is in the same
marked quotient, pulled back in V and then conjugated to A. -/
@[expose] def SmallRootRecognition {c : Coordinates D S.field}
    (f : InvariantFlag c) : Prop :=
  ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
    ∀ W : Subgroup G, SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W →
    W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
    ∃ U : Submodule S.field.Carrier c.Space,
      Module.finrank S.field.Carrier U = 1 ∧
      ⁅W, V.map (MulAut.conj g).toMonoidHom⁆ =
        (c.preimage U).map (MulAut.conj g).toMonoidHom

/-- The four separate action calculations in the middle of printed p.769.
This is a specification for the missing offender calculation, not a source
hypothesis. Its construction remains with the parabolic-action prerequisite. -/
structure ParabolicCalculations {c : Coordinates D S.field}
    (f : InvariantFlag c) (A : Subgroup G) : Prop where
  outside : ¬ A ≤ f.Ri 1 → SmallSymmetricAction f A (f.Vi 1)
  proper : A ≤ f.Ri 1 →
    ⁅V, A⁆ ⊔ (V ⊓ centralizer (L : Set G)) ≠ f.Vi 1 →
    ∃ l ∈ f.Li 1,
      SmallSymmetricAction f (A.map (MulAut.conj l).toMonoidHom) V
  fixed : A ≤ f.Ri 1 →
    ⁅V, A⁆ ⊔ (V ⊓ centralizer (L : Set G)) = f.Vi 1 →
    V ⊓ centralizer (A : Set G) = f.Vi 1
  span : A ≤ f.Ri 1 → CentralizerSpan V A (2 * S.field.degree)

variable (D S)

/-- Apply uniform exclusion to the original actor and to its L₂-replacements.
In particular the proper-image branch does not assume that L₂ fixes V₁. -/
theorem parabolic_of_calculations {c : Coordinates D S.field}
    (f : InvariantFlag c) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hsmall : NoSmallActions f)
    (hcalc : ParabolicCalculations f (V.map (MulAut.conj g).toMonoidHom)) :
    ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom) := by
  have hR : V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 := by
    by_contra hn
    exact hsmall g hg hne (f.Vi 1) (hcalc.outside hn)
  have hplane : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ⊔
      (V ⊓ centralizer (L : Set G)) = f.Vi 1 := by
    by_contra hn
    obtain ⟨l, hl, hs⟩ := hcalc.proper hR hn
    exact no_smallAction_after_replacement D S f hsmall g hR hne hl V hs
  exact ⟨hR, hplane, hcalc.fixed hR hplane, hcalc.span hR⟩

/-- The checked application to the published 11.2.4 assembly. Root
recognition and offender calculations are still explicit, unproved inputs;
this declaration does not certify the source theorem. The independent
normalized-plane producer supplies `hplane`. -/
theorem conclusions_of_recognition_and_calculations {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (hW : ⁅V, Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥)
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (hparameters : (S.field.degree : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hK : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (P : Sylow 2 (f.Li 1))
    (hfix : f.Vi 0 = f.Vi 1 ⊓ centralizer ((P : Subgroup (f.Li 1)).map
      (f.Li 1).subtype : Set G))
    (hrecognition : SmallRootRecognition f)
    (hcalculations : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ParabolicCalculations f (V.map (MulAut.conj g).toMonoidHom))
    (hplane : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      NoSmallActions f →
      ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom) →
      V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Alignment (f.Vi 1) V g) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) := by
  apply conclusions_of_geometry D S f hab hW hSL3 hparameters hK P hfix
  · intro g hg hne W hs hn
    exact alignment_of_small_commutator_line f hG2 g hs (hrecognition g hg hne W hs hn)
  · intro g hg hne hs
    exact parabolic_of_calculations D S f g hg hne hs (hcalculations g hg hne)
  · exact hplane

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
