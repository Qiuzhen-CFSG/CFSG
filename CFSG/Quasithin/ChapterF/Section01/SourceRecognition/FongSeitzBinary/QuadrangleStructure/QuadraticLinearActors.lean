module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.QuadraticLinearAction

/-!
# Full original linear actors in the quadratic quadrangle branch

The actual Chapter 11 quotient maps identify both full root-generated
linear actors, retaining an original lift and its quotient value for
every element. In particular the larger actor is the FULL PSL2(K),
and the smaller faithful panel group is PSL2(k). The smaller marking
now supplies the Cartan irreducibility used in QuadraticLinearAction.
Consequently the nonzero original core-derived clause gives the exact
opposite-root commutator, while the elementary original core gives the
other commuting clause and the complementary section of order |k|^4.

The profile's quadratic field-order ratio is retained as an earlier
input. It is not a compatible scalar labeling. The irreducibility of
the full complementary section and the later equivariant tensor
realization are separate obligations; neither is claimed here.
The arbitrary marked amalgam preserves both endpoint squares and may
be the independently marked geometric quotient. Both orientations and
all finite binary fields, including orders two and four, are allowed.

Source: DGS (11.3), (11.5)--(11.7), pp.169--175;
Fong--Seitz I (6A)(b), pp.37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
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
include Q e h split

/-- The actual Chapter 11 actor quotients supply the full larger actor and the
small faithful local group; hence they discharge the previously explicit local
marking in the U4 commutator theorem. -/
theorem marked_quadratic_linear_sixA
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
    ∃ μ : rankOne Q split i ≃* PSL(2,K), ∃ _ν : localGroup Q split j ≃* PSL(2,k),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧
        μ r = Atlas.RankOneFieldAutomorphisms.slEquivPSL (fi a)) ∧
      Nat.card (simpleRoot Q split i) = Nat.card k ^ 2 ∧
      Nat.card (simpleRoot Q split j) = Nat.card k ∧
      IsElementaryAbelian 2 (simpleRemainder Q split i) ∧
      Nat.card (simpleRemainder Q split i) = Nat.card k ^ 4 ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = rootAt Q split j (Q.simple i) ∧
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        rootAt Q split j (Q.simple i) ∧ Nat.card S = Nat.card k ^ 6 := by
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal := marked_sylow_factor_normal Q e h split i
  let : ((S ⊔ L j).subgroupOf (parabolic L S j)).Normal := marked_sylow_factor_normal Q e h split j
  obtain ⟨μ,hμ⟩ := marked_linear_rankOne Q e h split i si hVi _
    (subgroupOf_mono _ le_sup_left) fi hfi hki
  obtain ⟨_,ν,_,_⟩ := marked_linear_localGroup Q e h split j sj hVj _
    (subgroupOf_mono _ le_sup_left) fj hfj hkj
  refine ⟨μ.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL,ν,?_,?_⟩
  · intro r
    obtain ⟨a,ha,he⟩ := hμ r
    exact ⟨a,ha,congrArg Atlas.RankOneFieldAutomorphisms.slEquivPSL he⟩
  · exact marked_quadratic_linear_roots_of_nonzero_derived Q e h split hm i j hij
      (Nat.card k) Nat.card_pos hVi hVj ν (hfields ▸ hindexi) hindexj helem hQi hQj hne

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
