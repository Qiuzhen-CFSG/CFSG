module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.OneAbelian.Complement
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SecondRecognition
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.WreathedSylow
public import ABG.ChapterII.Section1.WreathedRegularModel
public import Theory.GroupTheory.Amalgam.SylowRigidity
/-!
# The original abelian vertex and its entire Sylow overlap

The original core is C₄ × C₄ and the original vertex has order 96.
The intrinsic vertex recognition identifies it with the second parabolic
of the actual G₂(2)′ model. Sylow conjugacy adjusts this isomorphism to
mark the original overlap exactly, and transports the concrete wreathed
presentation to that same original Sylow subgroup.

Source: Aschbacher–Smith F.1.12(I)(8), printed p.263.
-/
public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
/-- The abelian original vertex is the actual second G₂(2)′ parabolic. -/
theorem left_vertex
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    Nonempty (A≃*derivedSecond) := by
  obtain ⟨e⟩ := abelian_core_equiv_c4_square h hcore hA hB S hS hlarge hns
  have hQ : Nat.card (pCore 2 A)=16 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]
    decide
  apply equiv_derivedSecond_of_c4_square (pCore 2 A) e
  · rw [SymmetricThreeTwoCore.card_eq h.quotient_left.some,hQ]
  · exact h.local_core_selfCentralizing hA
  · exact h.quotient_left.some

/-- The adjusted vertex isomorphism retains the original overlap embedding. -/
theorem left_marked_vertex
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    ∃e : A≃*derivedSecond, ∃u : (A⊓B : Subgroup G)≃*derivedSylow,
      ∀x, e (inclusion (show A⊓B≤A from inf_le_left) x)=
        inclusion derivedSylow_le_second (u x) := by
  obtain ⟨e⟩ := left_vertex h hcore hA hB S hS hlarge hns
  let P := S.subtype (hS.symm.le.trans inf_le_left)
  have hp : (P : Subgroup A)=(inclusion (show A⊓B≤A from inf_le_left)).range := by
    ext x
    change (x:G)∈(S : Subgroup G) ↔ _
    rw [←hS]
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩
  let U := derivedSylow.subtype derivedSylow_le_second
  have hu : (U : Subgroup derivedSecond)=(inclusion derivedSylow_le_second).range := by
    ext x
    change (x:DerivedModel)∈(derivedSylow : Subgroup DerivedModel) ↔ _
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩
  exact exists_normalized_endpoint (inclusion inf_le_left) (inclusion derivedSylow_le_second)
    (inclusion_injective inf_le_left) (inclusion_injective derivedSylow_le_second) P hp U hu e

/-- The entire original Sylow group is the literal C₄ wreath C₂ carrier. -/
theorem common_sylow_wreathed
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    Nonempty (S≃*RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) := by
  obtain ⟨_,u,_⟩ := left_marked_vertex h hcore hA hB S hS hlarge hns
  obtain ⟨w⟩ := derivedSylow_isWreathedOfHeight.nonempty_mulEquiv_regularWreath
  exact ⟨((MulEquiv.subgroupCongr hS.symm).trans u).trans w⟩
end CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
