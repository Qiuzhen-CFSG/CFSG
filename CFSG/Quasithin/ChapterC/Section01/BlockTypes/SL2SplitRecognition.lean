module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverCoordinates
public import Theory.GroupTheory.SplitExtensionCoordinates
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.SplitModel
public import Theory.SpecificGroups.SL2.Affine
/-!
# Recognition of split extremal rank-one blocks

The original core quotient and the literal conjugation coordinates
identify a split block with the affine natural plane or the split maximal
binary cover. The subsequent Chapter 2 source constructs the splitting
and determines which center occurs.
Source: Aschbacher–Smith, Lemma 2.4.8(4), printed p.530.
-/
public section
namespace CFSG.Quasithin.ChapterC
open Subgroup Representation
open scoped IsMulCommutative
variable {L F : Type*} [Group L] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable (h : IsShort L)
variable [Finite L] [IsElementaryAbelian 2 (blockU L)] [IsElementaryAbelian 2 (BlockModule L)]
variable {r : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F))}
variable (m : BlockModuleModel L r)
variable (hm : ∀ g v, (r g v).toAdd = specialLinearNatural 2 g v.toAdd)

omit [Finite F] [CharP F 2] [Finite L] in
include h m hm in
lemma split_natural_model (hcore : pCore 2 L = blockU L)
    (hsplit : ∃ K : Subgroup L, (pCore 2 L).IsComplement' K)
    (hz : center L = ⊥) : Nonempty (L ≃* Matrix.SL2.Affine F) := by
  obtain ⟨K,hK⟩ := hsplit
  have hfixed : blockFixed L = ⊥ := by
    change (center L).subgroupOf (blockU L) = ⊥
    rw [hz,bot_subgroupOf]
  obtain ⟨e,he⟩ := modelCover_natural_equiv h m hm hfixed
  let eQ := (MulEquiv.subgroupCongr hcore).trans e
  apply exists_semidirect_equiv_of_split_coordinates (pCore 2 L) K hK m.quotientIso eQ
    (Matrix.SL2.naturalAction F)
  intro l u
  apply Multiplicative.toAdd.injective
  have hec : MulEquiv.subgroupCongr hcore (MulAut.conjNormal l u) =
      blockConjugate L l (MulEquiv.subgroupCongr hcore u) := Subtype.ext rfl
  change (e (MulEquiv.subgroupCongr hcore (MulAut.conjNormal l u))).toAdd = _
  rw [hec,he]
  rfl

include h m hm in
lemma split_orthogonal_model {n : ℕ} (hn : 1<n) (hF : Nat.card F = 2^n)
    (hcore : pCore 2 L = blockU L)
    (hsplit : ∃ K : Subgroup L, (pCore 2 L).IsComplement' K)
    (hcent : center L ≤ blockU L) (hz : Nat.card (center L) = 2^n) :
    Nonempty (L ≃* SL2OrthogonalCover.SplitGroup F) := by
  obtain ⟨K,hK⟩ := hsplit
  have hfixed : Nat.card (blockFixed L) = 2^n :=
    (Nat.card_congr (subgroupOfEquivOfLe hcent).toEquiv).trans hz
  obtain ⟨e,he⟩ := modelCover_orthogonal_equiv h m hm hn hF hfixed
  let eQ := (MulEquiv.subgroupCongr hcore).trans e
  apply exists_semidirect_equiv_of_split_coordinates (pCore 2 L) K hK m.quotientIso eQ
    SL2OrthogonalCover.multiplicativeAction
  intro l u
  apply Multiplicative.toAdd.injective
  have hec : MulEquiv.subgroupCongr hcore (MulAut.conjNormal l u) =
      blockConjugate L l (MulEquiv.subgroupCongr hcore u) := Subtype.ext rfl
  change (e (MulEquiv.subgroupCongr hcore (MulAut.conjNormal l u))).toAdd = _
  rw [hec,he]
  rfl
end CFSG.Quasithin.ChapterC
