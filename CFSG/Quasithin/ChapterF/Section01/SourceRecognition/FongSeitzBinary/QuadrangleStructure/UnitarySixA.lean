module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryActor

/-!
# The assembled U₅ branch of (6A)(c)

This module only assembles already proved source adapters.  The DGS full
SU₃ actor remains an explicit `UnitaryActorProfile`; the faithful projective
marking is never used to manufacture a covering lift.  The two mixed
commutators and the two linear-section irreducibility statements are the
literal quotient results from the preceding modules, with both endpoint
maps and the original source hypotheses retained.

Source: DGS (11.8)(a,b,f), pp.175--176; Fong--Seitz I (6A)(c), p.37.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
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

include e h
/-- All structural clauses of the U₅ row, retaining the actual source actor
map as a premise and keeping the two actor markings separate.  The first
actor marking is the one used by the commutator theorem; the second is the
one used by the irreducible-section theorem.  No equality between these
chosen equivalences is asserted or needed by the source consumers. -/
theorem marked_unitary_sixA
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
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
      ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q split j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (d : UnitaryActorProfile Q split j J hVj ν)
    (hZ : center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = ⊥)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (_hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    (∃ κ : rankOne Q split j ≃* J.specialSubgroup,
      (∀ r : rankOne Q split j,
        ν (rankOneLocalEquiv Q split j hVj (QuotientGroup.mk r)) =
          J.specialToProjective (κ r)) ∧
      J.specialToProjective.ker = center J.specialSubgroup ∧
      center (rankOne Q split j) =
        (center J.specialSubgroup).comap κ.toMonoidHom) ∧
    (∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ =
        rootAt Q split i (Q.simple j) ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (center (rootAt Q split j (Q.simple i))).map
          (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (frattini (simpleRemainder Q split j)).map
          (simpleRemainder Q split j).subtype) ∧
    (∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      frattini (simpleRemainder Q split i) =
        _root_.commutator (simpleRemainder Q split i) ∧
      (∃ he : IsElementaryAbelian 2
          (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
            Subgroup (X ⧸ Q.D)),
        letI := he
        Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
          Subgroup (X ⧸ Q.D)) = (2^n)^4 ∧
        (elementaryRepresentation (p := 2)
          (remainderDerivedAction Q split i hVi)).IsIrreducible) ∧
      Nat.card (frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q split i) ⧸
        frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split i hVi)).IsIrreducible ∧
      Representation.IsIrreducible
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreActorRepresentation
          Q split i hVi)) := by
  obtain ⟨κ,hκ,hker⟩ := marked_unitary_full_actor Q split j J hn hE hfixed hJ ν d hZ
  have hcenter := marked_unitary_full_actor_center Q split j J ν d κ hκ hZ
  obtain ⟨μc,hμc,hcross,hcenterCross,hphiCross⟩ :=
    marked_unitary_commutators Q e h split J hn hK hE hfixed hJ hm i j hij
      hVi hVj s f hf hk ν hderived hfrattini
  obtain ⟨μa,hμa,hphi,hderivedAction,hfrattiniCard,hfrattiniQuot,
      hfrattiniIrred,hcoreIrred⟩ :=
    marked_unitary_linear_actions Q e h split J hn hK hE hfixed hJ hm i j hij
      hVi hVj s f hf hk ν hindexi hindexj
  exact ⟨⟨κ,hκ,hker,hcenter⟩,
    ⟨μc,hμc,hcross,hcenterCross,hphiCross⟩,
    ⟨μa,hμa,hphi,hderivedAction,hfrattiniCard,hfrattiniQuot,
      hfrattiniIrred,hcoreIrred⟩⟩

include h
omit Q e split
/-- The same assembled clauses on the literal original `SourceQuotient`.
Every actor representative is retained through `Q₀.q`; no descent from a
geometric completion is used. -/
theorem original_unitary_sixA
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
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
      ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q₀ split₀ j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (d : UnitaryActorProfile Q₀ split₀ j J hVj ν)
    (hZ : center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = ⊥)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (_hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    (∃ κ : rankOne Q₀ split₀ j ≃* J.specialSubgroup,
      (∀ r : rankOne Q₀ split₀ j,
        ν (rankOneLocalEquiv Q₀ split₀ j hVj (QuotientGroup.mk r)) =
          J.specialToProjective (κ r)) ∧
      J.specialToProjective.ker = center J.specialSubgroup ∧
      center (rankOne Q₀ split₀ j) =
        (center J.specialSubgroup).comap κ.toMonoidHom) ∧
    (∃ μ : rankOne Q₀ split₀ i ≃* SL(2,K),
      (∀ r : rankOne Q₀ split₀ i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q₀.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a) ∧
      ⁅simpleRoot Q₀ split₀ j,rootAt Q₀ split₀ j (Q₀.simple i)⁆ =
        rootAt Q₀ split₀ i (Q₀.simple j) ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (center (rootAt Q₀ split₀ j (Q₀.simple i))).map
          (rootAt Q₀ split₀ j (Q₀.simple i)).subtype ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (frattini (simpleRemainder Q₀ split₀ j)).map
          (simpleRemainder Q₀ split₀ j).subtype) ∧
    (∃ μ : rankOne Q₀ split₀ i ≃* SL(2,K),
      (∀ r : rankOne Q₀ split₀ i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q₀.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a) ∧
      frattini (simpleRemainder Q₀ split₀ i) =
        _root_.commutator (simpleRemainder Q₀ split₀ i) ∧
      (∃ he : IsElementaryAbelian 2
          (⁅simpleRemainder Q₀ split₀ i,simpleRemainder Q₀ split₀ i⁆ : Subgroup _),
        letI := he
        Nat.card (⁅simpleRemainder Q₀ split₀ i,simpleRemainder Q₀ split₀ i⁆ :
          Subgroup _) = (2^n)^4 ∧
        (elementaryRepresentation (p := 2)
          (remainderDerivedAction Q₀ split₀ i hVi)).IsIrreducible) ∧
      Nat.card (frattini (simpleRemainder Q₀ split₀ i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q₀ split₀ i) ⧸
        frattini (simpleRemainder Q₀ split₀ i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q₀ split₀ i hVi)).IsIrreducible ∧
      Representation.IsIrreducible
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreActorRepresentation
          Q₀ split₀ i hVi)) := by
  obtain ⟨ha,hc,hh⟩ := marked_unitary_sixA Q₀ (originalMarkedIso Q₀) h split₀
    J hn hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν d hZ
      hindexi hindexj _hQi hderived hfrattini
  rcases ha with ⟨κ,hκ,hker,hcenter⟩
  rcases hc with ⟨μc,hμc,hcross,hcenterCross,hphiCross⟩
  rcases hh with ⟨μa,hμa,hphi,hderivedAction,hfrattiniCard,hfrattiniQuot,
    hfrattiniIrred,hcoreIrred⟩
  refine ⟨⟨κ,hκ,hker,hcenter⟩, ⟨μc,?_,hcross,hcenterCross,hphiCross⟩,
    ⟨μa,?_,hphi,hderivedAction,hfrattiniCard,hfrattiniQuot,
      hfrattiniIrred,hcoreIrred⟩⟩
  · intro r
    obtain ⟨a,ha,he⟩ := hμc r
    exact ⟨a,(original_endpointMap_apply Q₀ i a.val).symm.trans ha,he⟩
  · intro r
    obtain ⟨a,ha,he⟩ := hμa r
    exact ⟨a,(original_endpointMap_apply Q₀ i a.val).symm.trans ha,he⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
