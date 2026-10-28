module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.SmallUnitaryIrreducibility

/-!
# The original-profile unitary quadrangle branch in every binary field

The full SU3 actor and its irreducible unitary Frattini section are now
constructed from the same original source action and covering transport,
including q = 2. The (6A)(c) assembly retains the scalar kernel, the full
linear actor, both actual root commutators, both linear section actions,
and either endpoint orientation. The original adapter keeps the literal
quotient representatives and endpoint maps.

The original Chapter 11 profile and the generic covering transport remain
inputs from their independent producers. No full SU3 bijection, target
actor profile, or unitary-side irreducibility is an input. Subsequent
natural/Hermitian realization remains with the unitary-source consumer.

Sources: Fong--Seitz I (6A)(c), pp.37--38; DGS (11.8), pp.175--176.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
include e h

/-- The complete marked (6A)(c) structural output, including the nonperfect
field-two actor and its actual irreducible unitary Frattini section. -/
theorem marked_unitary_sixA_all_of_cover
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i) (t : RootReflection Q split j)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
      ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q split j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
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
          Q split i hVi)) ∧
    (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  obtain ⟨⟨d⟩,hi⟩ := marked_unitary_profile_irreducible_all_of_cover Q split e h J hn hE hconj hJ
    hm i j hij hVi hVj t ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hZ := HermitianForm.EvenProjectiveComparison.center_eq_bot J
    (by omega : 0 < n) hE hconj
  obtain ⟨ha,hc,hl⟩ := marked_unitary_sixA Q e h split J (by omega) hK hE hfixed hJ
    hm i j hij hVi hVj s f hf hk ν d hZ hindexi hindexj hQi hderived hfrattini
  exact ⟨ha,hc,hl,hi⟩

omit Q split e in
/-- The constructed cover profile feeds the original SourceQuotient assembly,
retaining the literal quotient representatives and both original endpoint maps. -/
theorem original_unitary_sixA_all_of_cover
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q₀ = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (s : RootReflection Q₀ split₀ i) (t : RootReflection Q₀ split₀ j)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
      ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q₀ split₀ j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q₀ split₀ j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q₀ split₀ j (π a)) = J.specialToProjective a)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
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
          Q₀ split₀ i hVi)) ∧
    (elementaryRepresentation (p := 2) (remainderFrattiniAction Q₀ split₀ j hVj)).IsIrreducible := by
  obtain ⟨⟨d⟩,hi⟩ := marked_unitary_profile_irreducible_all_of_cover Q₀ split₀ (originalMarkedIso Q₀) h J hn hE hconj hJ
    hm i j hij hVi hVj t ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hZ := HermitianForm.EvenProjectiveComparison.center_eq_bot J
    (by omega : 0 < n) hE hconj
  obtain ⟨ha,hc,hl⟩ := original_unitary_sixA h Q₀ split₀ J (by omega) hK hE hfixed hJ
    hm i j hij hVi hVj s f hf hk ν d hZ hindexi hindexj hQi hderived hfrattini
  exact ⟨ha,hc,hl,hi⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
