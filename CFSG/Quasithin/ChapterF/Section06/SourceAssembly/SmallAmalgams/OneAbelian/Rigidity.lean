module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.OneAbelian.OppositeCore
public import Theory.GroupTheory.WreathedThirtyTwoVertex.Recognition
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.G2
/-!
# The original order-thirty-two one-abelian amalgam

The original faithful Goldschmidt pair determines both whole vertices and
its common wreathed Sylow subgroup. The abelian endpoint is the actual second
parabolic of G₂(2)′; the opposite endpoint is the actual first parabolic.
The finite parabolic rigidity theorem then makes their three identifications
compatible with both original inclusion maps. No local model or compatibility
hypothesis is added to the source assumptions.

Source: Aschbacher–Smith F.1.12(I)(8), printed p.263.
-/
public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

/-- The unchanged opposite vertex is the nonabelian-core derived parabolic. -/
theorem right_vertex
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    Nonempty (B≃*derivedFirst) := by
  obtain ⟨hb,_,hn,⟨e⟩⟩ := opposite_vertex_parameters h hcore hA hB S hS hlarge hns
  exact WreathedVertex.equiv_derivedFirst_of_card96 hb
    (h.symm.local_core_selfCentralizing hB) hn
    (S.subtype (hS.symm.le.trans inf_le_right)) e

/-- Source case (8), with both original inclusion maps and the required orientation. -/
theorem derived_amalgam
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    GreenBook.ExceptionalModels.G2.IsDerivedAmalgam
      (ofSubgroups B (B⊓A) A inf_le_left inf_le_right) := by
  obtain ⟨eB⟩ := right_vertex h hcore hA hB S hS hlarge hns
  obtain ⟨eA,u,_⟩ := left_marked_vertex h hcore hA hB S hS hlarge hns
  let e : ParabolicEquiv (ofSubgroups B (B⊓A) A inf_le_left inf_le_right)
      GreenBook.ExceptionalModels.G2.simpleAmalgam := {
    left := eB
    middle := (MulEquiv.subgroupCongr (inf_comm B A)).trans u
    right := eA }
  exact GreenBook.ExceptionalRigidity.G2.simple_iso_of_parabolicEquiv
    (sylowEmbedded_ofSubgroups S B (B⊓A) A inf_le_left inf_le_right
      ((inf_comm B A).trans hS)) (h.symm.amalgam_faithful hcore) e
end CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
