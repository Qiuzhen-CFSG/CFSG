module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.SL3
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction

/-!
# The actual reciprocal flag-line orbit

A displacement recognized as a field line in V^g belongs to the orbit of
V₁^g under L^g. Transport the original component's line transitivity by the
same g: if l carries the original line to the recognized line, the correction
is x=g*l*g⁻¹, so left conjugation gives x*g=g*l. This proves precisely the
geometry premise of Transvection.Source, and the SL₃ recognition theorem
discharges it in that branch for every natural multiplicity.

The field-line premise for the original V₁ in the V_H coordinates remains
explicit, with producer qt-d-1222-shadow-transvection-marked-line (or
source_one_copy_line for multiplicity one). The Sp₄ displacement recognition
and common-axis multiplicity alternatives are separate unfinished obligations.
Source: Aschbacher--Smith, 11.3.7(4), refs/quasithin.pdf, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
  {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Construct the normalizer correction from a displacement line, retaining g. -/
theorem displacement_transporter_of_component
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (g : G) (U : Submodule S.field.Carrier c.Space)
    (horbit : ∃ l : L, (c.preimage (f.space 0)).map (MulAut.conj (l : G)).toMonoidHom =
      c.preimage U) :
    ∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      (c.preimage U).map (MulAut.conj g).toMonoidHom =
        (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom := by
  obtain ⟨l, hl⟩ := horbit
  have hn : (l : G) ∈ normalizer (V : Set G) := D.normalizes l.property
  refine ⟨g * l * g⁻¹, ?_, ?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (g * (l : G) * g⁻¹)).toMonoidHom = _
    rw [CFSG.Quasithin.ChapterE.offender_map_conj_map]
    have heq : g * (l : G) * g⁻¹ * g = g * l := by group
    rw [heq, ← CFSG.Quasithin.ChapterE.offender_map_conj_map]
    have hlV : V.map (MulAut.conj (l : G)).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp hn
    rw [hlV]
  · have heq : g * (l : G) * g⁻¹ * g = g * l := by group
    rw [heq, ← CFSG.Quasithin.ChapterE.offender_map_conj_map, hline]
    change (c.preimage U).map _ = ((c.preimage (f.space 0)).map _).map _
    rw [hl]

/-- The surviving marked models provide the component orbit used in transport. -/
theorem displacement_line_transporter
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) (U : Submodule S.field.Carrier c.Space)
    (hU : Module.finrank S.field.Carrier U = 1) :
    ∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      (c.preimage U).map (MulAut.conj g).toMonoidHom =
        (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom :=
  displacement_transporter_of_component c f hline g U
    (WeakClosure.Nonnormalization.RootParabolic.field_line_orbit
      c hG2 (f.space 0) U (f.dimension 0) hU)

/-- The exact geometry premise consumed by the published source assembly,
proved for the actual SL₃ action without either multiplicity restriction. -/
theorem sl3_commutator_line_geometry
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (hline : U₁ = (Coordinates.sl3 a).binarySubspace (f.space 0))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H)
    (hw : (w : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      ⁅V.map (MulAut.conj g).toMonoidHom, zpowers (w : G)⁆ =
        (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom := by
  obtain ⟨U, hU, hc⟩ := sl3_commutator_field_line a f hfixed g n hN w hw
  obtain ⟨x, hx, he⟩ := displacement_transporter_of_component (.sl3 a) f hline g U
    (SL3.PlaneAction.field_lines_transitive D S a (f.space 0) U (f.dimension 0) hU)
  exact ⟨x, hx, hc.trans he⟩

/-- Apply reciprocal SL₃ recognition to the published source consumer.
Only the original-line identification in V_H's coordinates remains explicit. -/
theorem source_seed_eq_sl3
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (hline : U₁ = (Coordinates.sl3 a).binarySubspace (f.space 0))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (U : Submodule S.field.Carrier (Fin m → Fin 2 → S.field.Carrier))
    (hU : Module.finrank S.field.Carrier U = 1) (hfix : U ≤ n.fixedSpace)
    (hmarked : n.liftSpace U = D.centralQuotientPreimage U₁) :
    (∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom =
        D.centralQuotientPreimage U₁) ∧ V.map (MulAut.conj g).toMonoidHom = V :=
  source_seed_eq_of_commutator_line_geometry s p hcounter halt g n U hU hfix hmarked
    (sl3_commutator_line_geometry a f hline hfixed g n hN)

/-- In one copy, the original source containment already discharges the
remaining field-line premise. -/
theorem source_seed_eq_sl3_one_copy
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (hline : U₁ = (Coordinates.sl3 a).binarySubspace (f.space 0))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field 1)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    V.map (MulAut.conj g).toMonoidHom = V :=
  (source_seed_eq_sl3 s p hcounter halt a f hline hfixed g n hN
    n.fixedSpace n.finrank_fixedSpace le_rfl
    (source_one_copy_line (.sl3 a) f hline hfixed g n hcontain)).2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
