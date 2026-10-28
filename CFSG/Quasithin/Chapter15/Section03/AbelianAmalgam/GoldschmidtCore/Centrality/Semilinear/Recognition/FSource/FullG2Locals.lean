module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.G2
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullSquareSylow
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# All literal local extensions for the marked full binary G₂ case

The original compatible amalgam maps transport the actual quaternion-product
first core and the original C₄² radical of the second vertex. The latter gives
the D₁₂ vertex quotient and E₄ common-Sylow quotient already proved below.
Thus every local field of row eleven is supplied from the genuine F.1.12
marking, with no extension-shape or local-recognition premise.

Source: Aschbacher–Smith F.1.12(I)(3) and F.6.18(11), pp.263 and 310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open ChapterF.GreenBook.ExceptionalModels
open Atlas.G2.BinaryParabolicPair

private theorem extension_transport {A M U W : Type*}
    [Group A] [Group M] [Group U] [Group W]
    (e : M ≃* A) (N : Subgroup M) [N.Normal]
    (jN : N ≃* U) (jQ : (M ⧸ N) ≃* W) : Extension A U W := by
  let N' := N.map e.toMonoidHom
  let : N'.Normal := (inferInstance : N.Normal).map e.toMonoidHom e.surjective
  exact ⟨N',inferInstance,⟨(e.subgroupMap N).symm.trans jN⟩,
    ⟨(QuotientGroup.congr N N' e rfl).symm.trans jQ⟩⟩

/-- The three original row-eleven local clauses from the exact full-G₂ marking. -/
theorem full_g2_marked_extensions {G : Type*} [Group G] {G₁ G₂ : Subgroup G}
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hM : G2.IsFullAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    Extension S C4Square E4 ∧
      QuaternionExtension G₁ (Equiv.Perm (Fin 3)) ∧
      Extension G₂ C4Square (DihedralGroup 6) := by
  obtain ⟨j⟩ := hM
  let eS : S ≃* G2.fullB := (MulEquiv.subgroupCongr hS.symm).trans j.middle
  let eQ := (LocalCoreTransport.coreEquiv 2 j.left).trans G2.fullFirstCoreEquiv
  let eL := (j.toParabolicEquiv.leftCoreQuotientEquiv 2).trans
    (G2.fullFirstQuotientEquiv.trans
      (Atlas.G2.ExceptionalLocalQuotients.dihedralEquivPSL.symm.trans
        nonempty_dihedralThreeEquivPerm.some))
  refine ⟨extension_transport (FullSquare.sylowEquiv.trans eS.symm)
      FullSquare.sylowRadical FullSquare.sylowRadicalEquiv FullSquare.sylowQuotientEquiv,
    ⟨pCore 2 G₁,inferInstance,⟨Atlas.G2.BinaryCore.coreQuaternionData.map eQ.symm⟩,⟨eL⟩⟩,
    extension_transport j.right.symm FullSquare.radical FullSquare.radicalEquiv
      FullSquare.quotientEquiv⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
