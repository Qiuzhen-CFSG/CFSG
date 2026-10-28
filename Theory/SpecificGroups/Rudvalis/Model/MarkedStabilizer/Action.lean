module
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.FullModel
/-!
# The full stabilizer comparison retains the Tits marking

The conjugation equivalence intertwines the original marked Tits embedding.
Thus a native parabolic calculation can identify the actual Rudvalis local
subgroups, rather than merely comparing their group orders.
-/
@[expose] public section
noncomputable section
namespace Rudvalis.MarkedStabilizer
open Tits.ExceptionalParabolics

theorem conjugation_apply (g : pointStabilizer) (x : Tits.Atlas1600Group) :
    atlasMap (conjugation g x)=(g:Model)*atlasMap x*(g:Model)⁻¹ := by
  change (((atlasEquiv (atlasEquiv.symm
    (MulAut.conjNormal g (atlasEquiv x))) : K) : pointStabilizer) : Model)=_
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem fullEquiv_action (g : pointStabilizer) :
    FullRee.atlasAction (fullEquiv g)=conjugation g := by
  change FullRee.atlasAutEquiv (FullRee.atlasAutEquiv.symm (conjugation g))=conjugation g
  exact MulEquiv.apply_symm_apply _ _

theorem conjugation_titsHom (x : Tits.Atlas1600Group) :
    conjugation (titsHom x)=MulAut.conj x := by
  ext y
  apply atlasMap_injective
  rw [conjugation_apply,MulAut.conj_apply,map_mul,map_mul,map_inv]
  rfl

theorem fullEquiv_titsHom (x : Tits.Atlas1600Group) :
    fullEquiv (titsHom x)=FullRee.atlasEmbedding x := by
  apply FullRee.atlasAutEquiv.injective
  rw [FullRee.atlasAutEquiv_embedding]
  exact (fullEquiv_action _).trans (conjugation_titsHom x)
end Rudvalis.MarkedStabilizer
