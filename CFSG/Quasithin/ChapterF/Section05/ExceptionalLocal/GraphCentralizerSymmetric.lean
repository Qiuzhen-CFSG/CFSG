module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerEndpointGeneration
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerEndpointResidual
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerRootComplement
/-!
# The actual endpoint join is S₆

The endpoint residual equality and the original root outside the centralizer
residual discharge the two inputs of endpoint generation. The resulting
literal subgroup is the root complement already identified with S₆.

Source: Aschbacher--Smith F.5.5, printed p.302.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_D_generated_by_residual_root (R : Sylow 2 (C c i)) (hR : Tf c i≤R) :
    D c i=(pResidual 2 (C c i)).map (C c i).subtype⊔zpowers (rootElement c i z) :=
  source_D_eq_residual_sup_root c i z h
    (source_DtwoResidual_eq_centralizer_residual c i z h R hR)
    (source_root_not_mem_centralizer_residual c i z h R hR)

theorem source_D_eq_rootComplement_image (R : Sylow 2 (C c i)) (hR : Tf c i≤R) :
    D c i=(sourceRootComplement c i z h).map (C c i).subtype := by
  rw [source_D_generated_by_residual_root c i z h R hR]
  rw [sourceRootComplement_eq,Subgroup.map_sup,MonoidHom.map_zpowers]
  rfl

theorem source_D_symmetric (R : Sylow 2 (C c i)) (hR : Tf c i≤R) :
    Nonempty (D c i≃*Equiv.Perm (Fin 6)) := by
  obtain ⟨e⟩ := source_rootComplement_symmetric c i z h R hR
  exact ⟨(MulEquiv.subgroupCongr (source_D_eq_rootComplement_image c i z h R hR)).trans
    (((sourceRootComplement c i z h).equivMapOfInjective (C c i).subtype
      (C c i).subtype_injective).symm.trans e)⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
