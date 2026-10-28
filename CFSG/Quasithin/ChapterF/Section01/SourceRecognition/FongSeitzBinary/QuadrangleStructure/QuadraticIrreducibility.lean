module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearIrreducibility
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.QuadraticLinearActors

/-!
# The original U4 radical is an irreducible module

Use the same original Chapter 11 actor quotients, core clauses, full
Borel indices and amalgam marking as QuadraticLinearActors. Its proved
full larger actor, exact mixed commutator and order |k|⁴ discharge the
minimum-degree irreducibility theorem for the actual complementary
section. The actor is R_i, acting by conjugation in the same finite
quotient. Both endpoint orientations and |k|=2 are retained.

The result supplies the irreducibility part of Fong--Seitz I (6A)(b).
It does not construct the compatible tensor coordinates required by
II (8B); those remain the later UnitarySource realization input.
Original DGS (11.7) quotient maps, radical clauses and section 2/5
kernel containments remain named earlier-source hypotheses.

Source: DGS (11.3), (11.7), pp.169,174--175;
Fong--Seitz I (4B), (6A)(b), pp.19--22,37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {K k : Type*} [Field K] [Finite K] [CharP K 2] [Field k] [Finite k] [CharP k 2]
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
include Q e h split

/-- The genuine original quadratic profile makes the actual complementary section irreducible. -/
theorem marked_quadratic_remainder_irreducible
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,k))
    (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
    (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
    (hfields : Nat.card K = Nat.card k ^ 2)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card K + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1)
    (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥) :
    let := marked_remainder_elementary Q e split i hVi helem
    (Representation.elementaryRepresentation (p := 2)
      (remainderRankOneAction Q split i hVi)).IsIrreducible := by
  let := marked_remainder_elementary Q e split i hVi helem
  obtain ⟨μ,ν,hμ,hri,hrj,he,hc,hzero,hcross,hphi,hS⟩ :=
    marked_quadratic_linear_sixA Q e h split hm i j hij hVi hVj si sj fi fj hfi hfj
      hki hkj hfields hindexi hindexj helem hQi hQj hne
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨n,_,hn⟩ := FiniteField.card k 2
  have hk : Nat.card k = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  have hK : Nat.card K = 2 ^ (2*(n : ℕ)) := by
    rw [hfields,hk,←pow_mul,Nat.mul_comm]
  apply quadratic_remainder_irreducible Q split hm i j hij hVi
    (μ.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm) (by have := n.pos; omega) hK
  · rw [hc,hfields]; ring
  · exact hcross

omit Q e split in
/-- The same irreducible full-root action on the literal original SourceQuotient. -/
theorem original_quadratic_remainder_irreducible
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm : rotationOrder Q₀ = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (si : RootReflection Q₀ split₀ i) (sj : RootReflection Q₀ split₀ j)
    (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,k))
    (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
    (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
    (hfields : Nat.card K = Nat.card k ^ 2)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card K + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1)
    (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥) :
    let := marked_remainder_elementary Q₀ (originalMarkedIso Q₀) split₀ i hVi helem
    (Representation.elementaryRepresentation (p := 2)
      (remainderRankOneAction Q₀ split₀ i hVi)).IsIrreducible :=
  marked_quadratic_remainder_irreducible Q₀ (originalMarkedIso Q₀) h split₀ hm i j hij
    hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
