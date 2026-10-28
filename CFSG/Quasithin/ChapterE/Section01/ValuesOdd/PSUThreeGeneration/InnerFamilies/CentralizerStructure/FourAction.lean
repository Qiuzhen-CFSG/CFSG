module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.LargePrime
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.FactorPosition.TorusAction.MatrixReduction
public import Theory.Representation.RankThreeDeterminantCentralizer

/-!
# Inner four-groups act nontrivially on the centralizer component

An elementary four-group is noncyclic. Its actual projective unitary
centralizer is abelian: lift the four-group through the scalar kernel of
exponent three, then apply the determinant-one degree-three centralizer
theorem. Noncyclicity forces three distinct character lines.

The residual of C_G(z)^∞T is quasisimple for p > 3 and lies in L, since G/L
is a two-group. The solvable radical centralizes this component. If the inner
four-group lay in that radical, the component would lie in its abelian
centralizer in L, contradicting perfectness and nontriviality.
This uses the original inclusions and works in every ambient two-extension.

Source: Aschbacher--Smith A.3.21(a),(c), pp.55--56; E.1.2(E2) and
E.1.14(7), pp.210,214. The degree-three argument supplies the cross-characteristic
four-group case directly, without an odd-prime subgroup assumption.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration

/-- The literal centralizer of an inner four-group is abelian. -/
theorem inner_four_centralizer_isMulCommutative {M : Type*} [Group M] [Finite M]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU M 3 p)
    (B : Subgroup M) [IsElementaryAbelian 2 B] (hB : Nat.card B = 4) :
    IsMulCommutative (centralizer (B : Set M)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : (2 : ℕ) ≠ p := by intro h; subst p; norm_num at hodd
  have hn : ¬ IsCyclic B :=
    IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hB
  apply (isPSU_centralizer_bound_of_matrix_centralizers (p := 2) (q := p)
    (by decide) hp2 hmodel B (IsElementaryAbelian.isPGroup 2 B) hn ?_).1
  intro F _ _ R hcomm horder hnR hdet
  let : IsMulCommutative R := hcomm
  exact Representation.rankThreeDeterminantCentralizer R horder hnR hdet

private theorem quasisimple_of_sl2_equiv {D : Type*} [Group D]
    {p : ℕ} [Fact p.Prime] (hlarge : 3 < p)
    (e : D ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) : IsQuasisimple D := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p) (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hlarge)
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using Nat.succ_le_of_lt hlarge)⟩
  exact IsQuasisimple.of_mulEquiv e.symm

private theorem not_le_radical_of_solvable_relative_centralizer {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] [Group.IsSolvable (G ⧸ L)]
    (A K : Subgroup G) (hAK : A ≤ K)
    [IsQuasisimple (solvableResidual K)]
    [Group.IsSolvable (centralizer (A.subgroupOf L : Set L))] :
    ¬ A.subgroupOf K ≤ solvableRadical K := by
  let D := solvableResidual K
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hcomp : IsComponent K D := ⟨(inferInstance : D.Normal).isSubnormal, inferInstance⟩
  have hDR : ⁅D, solvableRadical K⁆ = ⊥ := by
    rcases hcomp.normal_dichotomy (solvableRadical K) with hle | hc
    · let : Group.IsSolvable D :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
      exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
    · exact hc
  intro hA
  have hDA : ⁅D, A.subgroupOf K⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono le_rfl hA).trans hDR.le)
  let : Group.IsPerfect (D.map K.subtype) := Group.IsPerfect.map K.subtype
  have hDL : D.map K.subtype ≤ L := le_of_isPerfect_of_solvable_quotient _ L
  let j : D →* centralizer (A.subgroupOf L : Set L) :=
    { toFun := fun x => ⟨⟨x.val.val, hDL (mem_map_of_mem K.subtype x.property)⟩, by
        intro a ha
        exact Subtype.ext (congrArg (fun y : K => (y : G))
          ((commutator_eq_bot_iff_le_centralizer.mp hDA) x.property
            (⟨a, hAK ha⟩ : K) ha))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) h))
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective hj
  exact Group.IsPerfect.not_isSolvable D inferInstance

/-- An inner four-group survives the radical quotient of the actual residual supplement. -/
theorem inner_four_not_le_centralizerResidual_radical {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlarge : 3 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hfour : Nat.card A = 4)
    (hAT : A ≤ (T : Subgroup G)) (hAL : A ≤ L)
    (z : G) (hz : orderOf z = 2) (hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ¬ A.subgroupOf (centralizerResidualOvergroup T z) ≤
      solvableRadical (centralizerResidualOvergroup T z) := by
  let : Fact p.Prime := ⟨hp⟩
  let K := centralizerResidualOvergroup T z
  have hq := isPGroup_quotient_of_sup_eq_top L T T.isPGroup' hLT
  let : Group.IsNilpotent (G ⧸ L) := hq.isNilpotent
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv L T hLT hp hodd hlarge hmodel z (hAL hzA) hz
  let e := (centralizerResidualOvergroup_residualEquiv hTz).trans ec
  let : IsQuasisimple (solvableResidual K) := quasisimple_of_sl2_equiv (p := p) hlarge e
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hcard : Nat.card (A.subgroupOf L) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv).trans hfour
  let hc := inner_four_centralizer_isMulCommutative hp hodd hmodel (A.subgroupOf L) hcard
  let : IsMulCommutative (centralizer (A.subgroupOf L : Set L)) := hc
  let : Group.IsSolvable (centralizer (A.subgroupOf L : Set L)) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp hc)
  exact not_le_radical_of_solvable_relative_centralizer L A K (hAT.trans le_sup_right)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
