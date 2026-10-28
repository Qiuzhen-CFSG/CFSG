module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.TopDihedralSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.PGLComponent
public import Theory.PGL2.FieldTransport

/-!
# The proper-component dihedral source alternative

The lower source theorem selects one prime and supplies the residual PSL₂
model, ambient PGL₂ model and compatible original S₄--D₂₄ amalgam. Transport
through the actual residual–Fitting equality and field maps constructs every
field, component, Sylow and local clause of row (5), with its correct orientation.
Source: Aschbacher–Smith, F.6.18(5), printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open Theory.GroupTheory.RankTwoAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G} {κ : GroupClass.{u}}
theorem proper_dihedral_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4)
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G)) (ht : pResidual 2 G ≠ ⊤) :
    Alternative G₁ G₂ S ∨ Alternative G₂ G₁ S := by
  let := q.coverGroup
  let := q.coverFinite
  obtain ⟨p,hp,_,h24,hm,⟨eG⟩,hpair⟩ :=
    ChapterF.SourceAssembly.source_proper_dihedral_eight_pgl_row_with_component
      (hA _) (hC _) q.sqtk q.equiv.symm h hF hq eT ht
  let : Fact p.Prime := ⟨hp⟩
  let field : FieldParameter.{u} :=
    { Carrier := ULift.{u} (ZMod p)
      prime := p
      prime_isPrime := hp
      degree := 1
      degree_pos := by decide
      card := by simp }
  let jp : ZMod p ≃+* field.Carrier := ULift.ringEquiv.symm
  obtain ⟨F,_,_,hFc,⟨eL⟩⟩ := hm
  let := Fintype.ofFinite F
  let jf : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hFc)).symm
  let jL : generalizedFitting G ≃* PSL(2,field.Carrier) :=
    ((MulEquiv.subgroupCongr hF.symm).trans eL).trans
      (Atlas.fieldEquivPSL 2 (jf.trans jp))
  let jG : G ≃* PGL2 field.Carrier := eG.trans (Matrix.ProjGenLinGroup.mapEquiv jp)
  let : IsQuasisimple (pResidual 2 G) := hq
  have hqF : IsQuasisimple (generalizedFitting G) :=
    IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hF)
  have hs : Nonempty (S ≃* DihedralGroup 4) :=
    ⟨(MulEquiv.subgroupCongr hS.symm).trans eT⟩
  rcases hpair with hh | hh
  · obtain ⟨e⟩ := hh
    exact Or.inr (.five field rfl h24 jG jL hqF hs
      ⟨e.right.trans MixedEight.reflectionVertexEquiv⟩ ⟨e.left⟩)
  · obtain ⟨e⟩ := hh
    exact Or.inl (.five field rfl h24 jG jL hqF hs
      ⟨e.right.trans MixedEight.reflectionVertexEquiv⟩ ⟨e.left⟩)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
