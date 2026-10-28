module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryLinearActions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.CoreModules

/-!
# Original-source U5 linear sections and their scalar-field consumer

The original linear actor quotient of DGS (11.8)(b), with its exact two-core
kernel, identifies the full root-generated SL2(q squared) actor. The two
honest full-Borel indices give the literal linear radical order q to the
eighth. The unitary local marking and source reflection then prove both
linear sections irreducible, with order q to the fourth, without assuming
the mixed commutators or a radical-module realization.

The arbitrary amalgam marking preserves both endpoints and the full
overlap. Its original specialization retains Q.q on every actor lift and
applies the irreducibility to CoreModules' actual commuting-field and
cyclicity constructions. No compatible field labels or Hermitian realization
are asserted. The earlier profile, local-kernel and marking inputs remain
explicit for the commuting-one-profile and source-assembly owners.

These are the two R1 action clauses of Fong--Seitz I (6A)(c). The full SU3
actor and the R2 section action remain with this structural family; the
later field pinning and model equations remain unitary-source-owned.

Source: DGS (11.8), pp.175--176; Fong--Seitz I (6A)(c), p.37;
Fong--Seitz II (8C), p.203, for the commuting-field consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The original linear actor and honest panel indices prove both linear
section actions, for the same marking and both endpoint orientations. -/
theorem marked_unitary_linear_actions
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1) :
    ∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      frattini (simpleRemainder Q split i) = _root_.commutator (simpleRemainder Q split i) ∧
      (∃ he : IsElementaryAbelian 2
          (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)),
        letI := he
        Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) = (2^n)^4 ∧
        (elementaryRepresentation (p := 2) (remainderDerivedAction Q split i hVi)).IsIrreducible) ∧
      Nat.card (frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)).IsIrreducible ∧
      (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreActorRepresentation Q split i hVi).IsIrreducible := by
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal := marked_sylow_factor_normal Q e h split i
  obtain ⟨μ,_,_,hμ⟩ := marked_linear_localGroup Q e h split i s hVi _
    (subgroupOf_mono _ le_sup_left) f hf hk
  have hcardV := (marked_unitary_root_orders Q e h split hm i j hij (2^n)
    (pow_pos (by decide) _) hindexi hindexj).2.2.1
  obtain ⟨hphi,hd⟩ := unitary_linear_derived_irreducible Q split J hn hK hE hfixed hJ
    hm i j hij hVi hVj s μ ν
  obtain ⟨hp,hq,hi⟩ := unitary_linear_frattini_irreducible Q split J hn hK hE hfixed hJ
    hm i j hij hVi hVj s μ ν hcardV
  exact ⟨μ,hμ,hphi,hd,hp,hq,hi,unitary_linear_coreActor_irreducible Q split J hn hK hE hfixed hJ
    hm i j hij hVi hVj s μ ν hcardV⟩

include h in
omit Q e split in
/-- Original quotient application, retaining Q.q on all actor lifts and
supplying the actual CoreModules scalar-field and cyclicity consumers. -/
theorem original_unitary_linear_actions
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q₀ = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (s : RootReflection Q₀ split₀ i)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q₀ split₀ j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1) :
    ∃ μ : rankOne Q₀ split₀ i ≃* SL(2,K),
      (∀ r : rankOne Q₀ split₀ i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q₀.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a) ∧
      frattini (simpleRemainder Q₀ split₀ i) = _root_.commutator (simpleRemainder Q₀ split₀ i) ∧
      (∃ he : IsElementaryAbelian 2
          (⁅simpleRemainder Q₀ split₀ i,simpleRemainder Q₀ split₀ i⁆ : Subgroup _),
        letI := he
        Nat.card (⁅simpleRemainder Q₀ split₀ i,simpleRemainder Q₀ split₀ i⁆ : Subgroup _) = (2^n)^4 ∧
        (elementaryRepresentation (p := 2) (remainderDerivedAction Q₀ split₀ i hVi)).IsIrreducible) ∧
      Nat.card (frattini (simpleRemainder Q₀ split₀ i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q₀ split₀ i) ⧸ frattini (simpleRemainder Q₀ split₀ i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2) (remainderFrattiniAction Q₀ split₀ i hVi)).IsIrreducible ∧
      (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreActorRepresentation Q₀ split₀ i hVi).IsIrreducible ∧
      IsCyclic (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreCartan Q₀ i) ∧
      Nat.card (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreCartan Q₀ i) ∣
        Nat.card (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.CoreEnd Q₀ split₀ i hVi) - 1 := by
  obtain ⟨μ,hμ,hphi,hd,hp,hq,hi,hcore⟩ := marked_unitary_linear_actions Q₀ (originalMarkedIso Q₀) h split₀
    J hn hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν hindexi hindexj
  let := hcore
  refine ⟨μ,?_,hphi,hd,hp,hq,hi,hcore,
    UnitarySource.original_core_cartan_isCyclic Q₀ split₀ i hVi h,
    UnitarySource.original_core_scalar_field_order Q₀ split₀ i hVi h⟩
  intro r
  obtain ⟨a,ha,he⟩ := hμ r
  exact ⟨a,(original_endpointMap_apply Q₀ i a.val).symm.trans ha,he⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
