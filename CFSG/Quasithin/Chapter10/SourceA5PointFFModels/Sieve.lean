module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2

/-!
# The six remaining point-component FF actions

A proper C-component with alternating-five two-core quotient, local at a
full Sylow two-subgroup of the quasisimple actor, restricts the genuine
B.5.1 action list to six possibilities. Solvable proper Sylow overgroups
exclude rank one and the small alternating actors and central covers.
The higher binary linear and binary G₂ exclusions remove the remaining
exceptional and nonhomogeneous rows. The surviving linear-three, double
linear-three, symplectic and G₂ actions retain their exact natural-model
coordinates. Both alternating-seven actions retain the faithful quotient
action, and the deleted case retains its marked subgroup inside the full
symmetric action.

The moved-space and central-quotient carriers remain distinct. The full
source conclusion is accepted directly by the final consumer, so its
other five clauses remain available on exactly the same moved section.
No additional classification or model-action premise is introduced.

Source: Aschbacher–Smith B.4.2 and B.5.1, printed pp.86 and 99–103,
as applied in 10.2.9, printed pp.751–752 (combined manuscript, 1 March 2004).
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
inductive SixWay (s : MovedSection ρ L) : Prop
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
  | alternatingSevenFour (faithful : Function.Injective s.action)
      (actor : L ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2)
        (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
  | alternatingSevenDeleted (faithful : Function.Injective s.action)
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
theorem sixWay_of_source_case [IsQuasisimple L]
    (s : MovedSection ρ L)
    (hc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s)
    (R : Sylow 2 L) (B : Subgroup L) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    SixWay ρ L s := by
  cases hc with
  | irreducible _ faithful _ source _ =>
    cases source with
    | linearTwo F _ a _ _ => exact (rank_one_excluded R B hB hp F a.groupEquiv).elim
    | linearThree F _ a _ => exact .linearThree F faithful a
    | symplectic F large _ a _ => exact .symplectic F large faithful a
    | symplecticTwo a _ =>
      exact (AlternatingSmall.not_proper_symplectic_two_derived R B hB hp a.subgroupEquiv).elim
    | g2 F large _ a _ _ => exact .g2 F large faithful a
    | g2Two a _ _ => exact (binary_g2_excluded B eB a.subgroupEquiv).elim
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact (AlternatingSmall.not_proper_five R B hB hp a.subgroupEquiv).elim
      · exact .alternatingSevenDeleted faithful a
    | alternatingSix _ a _ _ =>
      exact (AlternatingSmall.not_proper_six R B hB hp a.groupEquiv).elim
    | alternatingSeven _ _ a dim _ _ => exact .alternatingSevenFour faithful a dim
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
theorem sixWay_of_source [IsQuasisimple L]
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (R : Sylow 2 L) (B : Subgroup L) (hB : B ∈ localCComponents R)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    SixWay ρ L h.sectionData :=
  sixWay_of_source_case ρ L h.sectionData h.clause_one R B hB hp eB

end CFSG.Quasithin.Chapter10.SourceA5PointFFModels
