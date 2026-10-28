module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.Branches
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.SmallCommutator

/-!
# Reciprocal small-action recognition in the SL₃ row

Conjugating the small action back to the original V gives a nonzero
commutator of order q. The exact SL₃ cover has trivial central kernel, and
the existing small-displacement calculation proves that this commutator is
an original field-line preimage. Conjugating forward and applying line
transitivity gives the first alignment and the abelian-span contradiction.

Only the actual marking and flag are used. The reused small-commutator theorem
has an independent proof from the normalizer action; it does not assume the
later weak-closure or classification conclusions. The Sp₄ recognition and
parabolic calculations remain with `qt-d-1222-natural-conjugate-nonnormalization`.

Source: Aschbacher--Smith, 11.2.4, refs/quasithin.pdf, printed p.769.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

omit [Finite G] in
private theorem inverse_conjugate_cancel (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = B := by
  rw [offender_map_conj_map, inv_mul_cancel]
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext; simp
  rw [he,map_id]

/-- Small reciprocal action in the SL₃ row is the full original field-line
preimage. The central kernel vanishes by the proved SL₃ cover theorem. -/
theorem sl3_smallRootRecognition
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) : SmallRootRecognition f := by
  intro g _ _ W hs hn
  have hfixed := Preliminary.sl3_centralizer_eq_bot D S m
  have he : ⁅W,V.map (MulAut.conj g).toMonoidHom⁆ = f.Vi 0 := by
    simpa only [hfixed,sup_bot_eq] using hs.quotient_line
  let B := W.map (MulAut.conj g⁻¹).toMonoidHom
  have hcomm : ⁅B,V⁆ = (⁅W,V.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj g⁻¹).toMonoidHom := by
    rw [map_commutator,inverse_conjugate_cancel]
  have hBV : B ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [hcomm]
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (le_normalizer_iff_commutator_le_right.mp hn)
    rwa [inverse_conjugate_cancel] at hh
  have hne : ⁅B,V⁆ ≠ ⊥ := by
    rw [hcomm,he]
    exact fun hz => f.V_ne_bot 0
      ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp hz)
  have hsq : ∀ b : B, b ^ 2 = 1 := by
    let := D.elementary
    intro b
    obtain ⟨w,hw,he⟩ := b.property
    apply Subtype.ext
    change (b : G)^2=1
    rw [←he,←map_pow,elemPow_eq_one_of_isElementaryAbelian w (hs.le_seed hw),map_one]
  have hcard : Nat.card (⁅B,V⁆ : Subgroup G) ≤ Nat.card S.field.Carrier := by
    rw [hcomm,he,card_map_of_injective (MulAut.conj g⁻¹).injective]
    change Nat.card ((Coordinates.sl3 m).preimage (f.space 0)) ≤ _
    rw [Closure.Nonabelian.card_preimage (.sl3 m) hfixed, f.dimension]
    simpa using S.field.card_eq.ge
  let E : Closure.Geometry D :=
    { input := S
      point := (Coordinates.sl3 m).binarySubspace (f.space 0)
      plane := (Coordinates.sl3 m).binarySubspace (f.space 1)
      threeSpace := (Coordinates.sl3 m).binarySubspace (f.space 2)
      X := ⊥, z := g, H := ⊥ }
  obtain ⟨U,hU,hUeq⟩ := Closure.Amalgam.Even.Linear.commutator_isFieldLine_of_card_le
    (E := E) m hfixed B hBV hsq hne hcard
  refine ⟨U,hU,?_⟩
  have hh := congrArg (map (MulAut.conj g).toMonoidHom) hUeq
  rw [hcomm] at hh
  have hc : ((⁅W,V.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      ⁅W,V.map (MulAut.conj g).toMonoidHom⁆ := by
    simpa only [inv_inv] using inverse_conjugate_cancel
      ⁅W,V.map (MulAut.conj g).toMonoidHom⁆ g⁻¹
  rw [hc] at hh
  exact hh.symm

/-- Actual application of SL₃ reciprocal recognition to the first alignment
claim in source 11.2.4. -/
theorem sl3_small_alignment
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (W : Subgroup G) (hs : SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W)
    (hn : W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Alignment (f.Vi 0) V g :=
  alignment_of_small_commutator_line f hG2 g hs
    (sl3_smallRootRecognition m f g hg hne W hs hn)

/-- The SL₃ row excludes every small symmetric action under the genuine
abelian-span and preceding numerical hypotheses of source 11.2.4. -/
theorem sl3_noSmallActions
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (hr : (S.field.degree : ℕ∞) < globalR V) : NoSmallActions f := by
  intro g hg hne
  exact no_smallAction_of_alignment f hab hr g hne
    (sl3_small_alignment m f hG2 g hg hne)

/-- In the SL₃ row, the middle parabolic calculation is the only remaining
local input to all three conclusions of 11.2.4. The source numerical and
relative-component inputs are retained. The nonnormalization owner must still
construct `hcalculations`; this is not the unconditional source theorem. -/
theorem sl3_conclusions_of_calculations
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
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
    (hcalculations : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ParabolicCalculations f (V.map (MulAut.conj g).toMonoidHom)) :
    Source.weakClosureZero (T : Subgroup G) V ≤ f.Ri 1 ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      globalR V ≤ (2 * S.field.degree : ℕ) := by
  apply conclusions_of_recognition_and_calculations D S f hab hW hSL3 hparameters
    hG2 hK P hfix (sl3_smallRootRecognition m f) hcalculations
  intro g _ hne hsmall hp hn
  apply NormalizedPlane.alignment_of_equal_commutator f
    (fun k hk hkne => parabolic_of_calculations D S f k hk hkne hsmall
      (hcalculations k hk hkne)) g hne hn
  simpa only [Preliminary.sl3_centralizer_eq_bot D S m, sup_bot_eq] using hp.quotient_plane

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
