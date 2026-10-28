module
public import CFSG.Quasithin.Chapter10.SourceA5PointFFModels.Sieve
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedEquivalence

/-!
# The A₇ rows with their irreducibility and cohomology data

This strengthens the six-way point-component selector without changing its
published interface. Both A₇ rows retain the original Irr⁺, faithful,
irreducible and outer-extension fields needed by the proved Chapter B
cohomology theorem. Only the identical A₇ constructors are reconstructed
in that theorem's older catalogue; the triple-cover convention is never
converted or used in this reconstruction.

The four-dimensional and odd deleted A₇ cohomology calculations make the
moved space complementary to the component-fixed space. For a fully moved
module this forces the fixed space to vanish. The canonical projection
therefore identifies the original module with its central quotient. The
final consumers give a faithful original four-dimensional action or the
original deleted action with precisely the marked actor equivalence.
No identification of the original group's two-core quotient is assumed.

Source: Aschbacher–Smith B.5.1(2), printed pp.99–103, and 10.2.9,
printed pp.751–752 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5PointFFModels
open ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ProjectiveLine
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open ChapterA.Section03.SourceEmbeddings.FiveLocalFF
universe u v
variable {D : Type u} [Group D] [Finite D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) D V) (L : Subgroup D)

/-- The six surviving literal action models. Quotient-action models and the
repeated model on the original moved space retain their different carriers. -/
inductive SixWayWithIrreducible (s : MovedSection ρ L) : Prop
  | linearThree (F : BinaryField) (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (linearNatural F 3))
  | doubleThree (F : BinaryField)
      (action : ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2))
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F))
  | g2 (F : BinaryField) (large : 1 < F.degree)
      (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (binaryG2 F))
  | alternatingSevenFour (irreducible : ExtensionConsequences.IrreducibleAlternative L s)
      (actor : L ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2)
        (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
  | alternatingSevenDeleted (irreducible : ExtensionConsequences.IrreducibleAlternative L s)
      (action : MarkedActionEquiv s.action (offenderSubgroup s.action) L
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)))

private theorem rank_one_excluded {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (R : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (F : BinaryField) (e : A ≃* SL(2,F.Carrier)) : False := by
  have ht : (⊤ : Subgroup A).IsCComponent :=
    (show IsComponent A ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact hp (eq_of_solvable_sylow_overgroups R hB ht le_top
    (SolvableSylowOvergroups.of_equiv (topEquiv.trans e)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup))

private theorem binary_linear_excluded {A : Type*} [Group A] [Finite A]
    (R : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents R)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : A ≃* SL(d,ZMod 2)) : False := by
  apply BinaryLinear.not_section_binary_linear R B hB eB hd
  exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨e.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩

private theorem binary_g2_excluded {A : Type*} [Group A] [Finite A]
    (B : Subgroup A) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (e : A ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let d := B.equivMapOfInjective e.toMonoidHom e.injective
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  exact G2.binary_derived_excluded (by simp) (B.map e.toMonoidHom) (dq.symm.trans eB)

/-- The actual full-Sylow local A₅ section removes every other B.5.1 row.
The quasisimple instance belongs to the original component hypothesis. -/
theorem sixWayWithIrreducible_of_source_case [IsQuasisimple L]
    (s : MovedSection ρ L)
    (hc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s)
    (R : Sylow 2 L) (B : Subgroup L) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    SixWayWithIrreducible ρ L s := by
  cases hc with
  | irreducible irrPlus faithful irreducible source extension =>
    cases source with
    | linearTwo F _ a _ _ => exact (rank_one_excluded R B hB hp F a.groupEquiv).elim
    | linearThree F _ a _ => exact .linearThree F faithful a
    | symplectic F large _ a _ => exact .symplectic F large faithful a
    | symplecticTwo a _ =>
      exact (AlternatingSmall.not_proper_symplectic_two_derived R B hB hp a.subgroupEquiv).elim
    | g2 F large _ a _ _ => exact .g2 F large faithful a
    | g2Two a _ _ => exact (binary_g2_excluded B eB a.subgroupEquiv).elim
    | symmetric n hn a offenders ratio =>
      rcases hn with rfl | rfl
      · exact (AlternatingSmall.not_proper_five R B hB hp a.subgroupEquiv).elim
      · exact .alternatingSevenDeleted
          ⟨irrPlus,faithful,irreducible,.symmetric 7 (Or.inr rfl) a offenders ratio,extension⟩ a
    | alternatingSix _ a _ _ =>
      exact (AlternatingSmall.not_proper_six R B hB hp a.groupEquiv).elim
    | alternatingSeven generated whole a dim offenders ratio =>
      exact .alternatingSevenFour
        ⟨irrPlus,faithful,irreducible,.alternatingSeven generated whole a dim offenders ratio,extension⟩ a dim
    | tripleSix _ a _ =>
      exact (AlternatingSmall.not_proper_central_six R B hB hp a.quotientEquiv).elim
    | binaryLinear d hd _ a _ => exact (binary_linear_excluded R B hB eB hd a.groupEquiv).elim
    | orthogonalSix _ _ a _ _ =>
      exact (AlternatingSmall.not_section_eight R B hB eB a.groupEquiv).elim
    | symmetricEight _ a _ =>
      exact (AlternatingSmall.not_section_eight R B hB eB a.subgroupEquiv).elim
    | exteriorFive _ _ a _ _ _ =>
      exact (binary_linear_excluded R B hB eB (Or.inr rfl) a).elim
  | doubleThree F _ a _ _ => exact .doubleThree F a
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (binary_linear_excluded R B hB eB hd a.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (binary_linear_excluded R B hB eB hd a.groupEquiv).elim

/-- The full source conclusion supplies the literal clause used by the sieve,
so later consumers retain all its remaining clauses on the same moved section. -/
theorem sixWayWithIrreducible_of_source [IsQuasisimple L]
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (R : Sylow 2 L) (B : Subgroup L) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    SixWayWithIrreducible ρ L h.sectionData :=
  sixWayWithIrreducible_of_source_case ρ L h.sectionData h.clause_one R B hB hp eB

omit [Finite D] in
/-- The strengthened result preserves the previously published six-way API. -/
theorem SixWayWithIrreducible.toSixWay {s : MovedSection ρ L}
    (h : SixWayWithIrreducible ρ L s) : SixWay ρ L s := by
  cases h with
  | linearThree F hf a => exact .linearThree F hf a
  | doubleThree F a => exact .doubleThree F a
  | symplectic F hl hf a => exact .symplectic F hl hf a
  | g2 F hl hf a => exact .g2 F hl hf a
  | alternatingSevenFour hi a hd => exact .alternatingSevenFour hi.faithful a hd
  | alternatingSevenDeleted hi a => exact .alternatingSevenDeleted hi.faithful a

variable [FiniteDimensional (ZMod 2) V]

/-- The faithful four-dimensional A₇ section has no fixed attachment when
the actual original module is fully moved. -/
theorem alternatingSevenFour_fixedSpace_eq_bot
    (s : MovedSection ρ L) (hm : moved ρ L = ⊤)
    (hi : ExtensionConsequences.IrreducibleAlternative L s)
    (e : L ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
    fixedSpace ρ L = ⊥ := by
  have hc := ExtensionConsequences.alternatingSeven_isCompl s hi e hd
  simpa only [s.space_eq,hm,top_inf_eq] using hc.disjoint.eq_bot

/-- The actual marked deleted A₇ section likewise has no central fixed
attachment on a fully moved module. -/
theorem alternatingSevenDeleted_fixedSpace_eq_bot
    (s : MovedSection ρ L) (hm : moved ρ L = ⊤)
    (hi : ExtensionConsequences.IrreducibleAlternative L s)
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) L
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) :
    fixedSpace ρ L = ⊥ := by
  have hc := ExtensionConsequences.symmetricOdd_isCompl s hi.irrPlus (Or.inr rfl) e
  simpa only [s.space_eq,hm,top_inf_eq] using hc.disjoint.eq_bot

/-- The original module in the four-dimensional row itself has dimension
four and carries a faithful action; no original-head identification is used. -/
theorem alternatingSevenFour_original_model
    (s : MovedSection ρ L) (hm : moved ρ L = ⊤)
    (hi : ExtensionConsequences.IrreducibleAlternative L s)
    (e : L ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
    fixedSpace ρ L = ⊥ ∧ Function.Injective ρ ∧ Module.finrank (ZMod 2) V = 4 := by
  have hc := alternatingSevenFour_fixedSpace_eq_bot ρ L s hm hi e hd
  refine ⟨hc,?_,(s.fullProjectionEquiv hm hc).finrank_eq.trans hd⟩
  intro a b hab
  apply hi.faithful
  apply LinearMap.ext
  intro y
  obtain ⟨x,rfl⟩ := s.fullProjection_surjective hm y
  rw [←s.fullProjection_intertwines hm,←s.fullProjection_intertwines hm,hab]

/-- The original component action is the deleted A₇ model with the very
same actor equivalence as the marked quotient action. -/
theorem alternatingSevenDeleted_original_model
    (s : MovedSection ρ L) (hm : moved ρ L = ⊤)
    (hi : ExtensionConsequences.IrreducibleAlternative L s)
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) L
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) :
    fixedSpace ρ L = ⊥ ∧ ∃ a : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7),
      a.groupEquiv = e.subgroupEquiv := by
  have hc := alternatingSevenDeleted_fixedSpace_eq_bot ρ L s hm hi e
  let b := ExtensionConsequences.markedRestriction e
  refine ⟨hc,⟨e.subgroupEquiv,(s.fullProjectionEquiv hm hc).trans b.linearEquiv,?_⟩,rfl⟩
  intro g v
  change b.linearEquiv (s.fullProjection hm (ρ g v)) = _
  rw [s.fullProjection_intertwines]
  exact b.intertwines g (s.fullProjection hm v)

end CFSG.Quasithin.Chapter10.SourceA5PointFFModels
