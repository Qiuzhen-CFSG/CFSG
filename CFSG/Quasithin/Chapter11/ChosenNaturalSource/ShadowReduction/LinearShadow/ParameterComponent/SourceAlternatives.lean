module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Statements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Dimensions

/-!
# The source marking and parameter alternatives

Apply the proved E.3.20 lower bound to the original global parameter and
combine it with the exact preceding 11.2.1 alternative. The G₂ marking
would force k ≥ 2n, while the resulting doubled SL₃ marking would give
two different dimensions for the same central quotient. Thus the actual
marking is SL₃ or Sp₄, s(G,V)=n, and either k=n or every doubled clause
of 11.2.1 holds. The existing offender selection and line-normalizer
argument supply all four parts of 11.3.4. The Sp₄ marking already forces
k=n, independently of component recognition.

The exact generation alternative and the earlier global-s value remain
explicit. They are produced by the existing natural local-geometry and
weak-closure owners; no conclusion of 11.3.5 or 11.3.6 is assumed here.
Final earlier-source discharge remains with qt-d-1222-shadow-linear-geometry.
Source: Aschbacher--Smith, 11.3.4, printed p.771, using 11.2.1--2,
printed pp.766--768.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H K : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

private theorem central_corank (c : LocalGeometry.Coordinates D S.field) :
    ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) =
      S.field.degree * Module.finrank S.field.Carrier c.Space := by
  rw [←c.preimage_bot,WeakClosure.Parameters.NaturalDimensions.pullback_corank D S c]
  rw [(Submodule.quotEquivOfEqBot (⊥ : Submodule S.field.Carrier c.Space) rfl).finrank_eq]

/-- The exact preceding 11.2.1 and 11.2.2 clauses give the actual marking and
parameter alternatives; the full central quotient excludes the G₂ row. -/
theorem source_marking_and_parameter
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (c : LocalGeometry.Coordinates D S.field)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hgen : WeakClosure.Generation.Conclusion D S H) :
    (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))) ∧
    @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ) ∧
    (ChapterE.generationParameter H = S.field.degree ∨
      (S.field.degree < ChapterE.generationParameter H ∧
        Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        WeakClosure.Generation.DoubledNatural D S ∧ V ⊓ centralizer (H : Set G) = ⊥ ∧
        L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
        ChapterE.generationParameter H ≤ 2 * S.field.degree)) := by
  have hlo := counterexample_parameter_lower h pr hc
  rw [hs] at hlo
  have hlo' := ENat.natCast_le_natCast.mp hlo
  have hdim := central_corank c
  rw [WeakClosure.Parameters.NaturalDimensions.field_dimension] at hdim
  have hnon := S.nonbinary
  have hmatch :
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
        Nonempty (ActionEquiv D.centralQuotientAction
          (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))) ∧
      WeakClosure.Parameters.naturalParameter D S c = S.field.degree := by
    cases c with
    | sl3 m => exact ⟨.inl ⟨m⟩,rfl⟩
    | sp4 m => exact ⟨.inr ⟨m⟩,rfl⟩
    | g2 m =>
      change 2 * S.field.degree ≤ ChapterE.generationParameter H at hlo'
      rcases hgen with hu | ⟨_,⟨a,_⟩,_,_,_⟩
      · omega
      · have hd := central_corank (LocalGeometry.Coordinates.sl3 a)
        rw [WeakClosure.Parameters.NaturalDimensions.field_dimension] at hd
        change ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) =
          S.field.degree * 3 at hd
        change ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) =
          S.field.degree * 6 at hdim
        omega
  refine ⟨hmatch.1,hs.trans (congrArg (fun n : ℕ => (n : ℕ∞)) hmatch.2),?_⟩
  rw [hmatch.2] at hlo'
  by_cases he : ChapterE.generationParameter H = S.field.degree
  · exact .inl he
  · rcases hgen with hu | hd
    · omega
    · exact .inr ⟨by omega,hd⟩

/-- Source 11.3.4 on the original chosen module: an actual conjugate and its
fixed-space family, the SL₃/Sp₄ alternative, every strict-parameter clause
of 11.2.1, and the normalizer of the original line preimage. -/
theorem source_1134
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (c : LocalGeometry.Coordinates D S.field)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hgen : WeakClosure.Generation.Conclusion D S H) :
    letI := D.elementary
    letI := omegaOrbit_elementary h
    (∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      actorImage T H (V.map (MulAut.conj g).toMonoidHom) ∈
        ChapterE.fixedSpaceFamily (orbitRepresentation h) (ChapterE.globalS V).toNat) ∧
    (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)) ∧
    (ChapterE.generationParameter H = S.field.degree ∨
      (S.field.degree < ChapterE.generationParameter H ∧
        Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        WeakClosure.Generation.DoubledNatural D S ∧ V ⊓ centralizer (H : Set G) = ⊥ ∧
        L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
        ChapterE.generationParameter H ≤ 2 * S.field.degree)) ∧
    normalizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (V : Set G) := by
  let := D.elementary
  let := omegaOrbit_elementary h
  obtain ⟨hmark,_,hparam⟩ := source_marking_and_parameter h pr hc c hs hgen
  have halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) := by
    rcases hmark with hm | hm
    · obtain ⟨m⟩ := hm
      exact .inl ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩
    · obtain ⟨m⟩ := hm
      exact .inr ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩
  exact ⟨exists_source_offender h pr hc,halt,hparam,
    line_normalizer_le_of_counterexample h pr hc halt⟩

/-- In the symplectic marking, the source generation alternative already
forces k=n; no component model or rank-one reduction is needed. -/
theorem parameter_eq_of_symplectic_source
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ))
    (hgen : WeakClosure.Generation.Conclusion D S H) :
    ChapterE.generationParameter H = S.field.degree := by
  have hp := (source_marking_and_parameter h pr hc (.sp4 m) hs hgen).2.2
  rcases hp with he | ⟨_,_,⟨a,_⟩,_,_,_⟩
  · exact he
  · have hd := central_corank (LocalGeometry.Coordinates.sl3 a)
    have hd' := central_corank (LocalGeometry.Coordinates.sp4 m)
    rw [WeakClosure.Parameters.NaturalDimensions.field_dimension] at hd hd'
    change ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) =
      S.field.degree * 3 at hd
    change ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) =
      S.field.degree * 4 at hd'
    have := S.field.degree_pos
    omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
