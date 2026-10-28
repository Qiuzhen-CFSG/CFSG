module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.Models

/-!
# Transport of the actual exchanged block model

A multiplicative equivalence preserves O₂, its commutator layer U(L), and
the fixed layer C_U(L). Transport both quotient isomorphisms through these
identities; their intertwining remains the literal conjugation action.
Applied to ambient conjugation, this constructs the model on the second
block over exactly the same field as the first. The external product action
in `Models` can therefore use both actual blocks. An internal product
identification, if needed, still requires a proof from the source geometry.

Source: Aschbacher–Smith, C.1.7 and C.1.12, printed pp.123–124, and the
exchanged-block case of 15.4.20, printed p.1164.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
open Subgroup CFSG.Quasithin.ChapterC
variable {L L' : Type*} [Group L] [Group L']

/-- Isomorphisms preserve the intrinsic commutator layer. -/
theorem map_blockU (e : L ≃* L') : (blockU L).map e.toMonoidHom = blockU L' := by
  rw [blockU, map_commutator, pCore_map_iso,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

/-- The induced equivalence of the intrinsic commutator layers. -/
def blockUEquiv (e : L ≃* L') : blockU L ≃* blockU L' :=
  (e.subgroupMap (blockU L)).trans (MulEquiv.subgroupCongr (map_blockU e))

@[simp] theorem blockUEquiv_val (e : L ≃* L') (u : blockU L) :
    (blockUEquiv e u : L') = e u := rfl

/-- The induced equivalence preserves the central fixed layer. -/
theorem map_blockFixed (e : L ≃* L') :
    (blockFixed L).map (blockUEquiv e).toMonoidHom = blockFixed L' := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    change e w ∈ center L'
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    exact (map_mul e y (w : L)).symm.trans ((congrArg e (mem_center_iff.mp hw y)).trans
      (map_mul e (w : L) y))
  · intro hu
    refine ⟨(blockUEquiv e).symm u, ?_, (blockUEquiv e).apply_symm_apply u⟩
    change ((blockUEquiv e).symm u : L) ∈ center L
    apply mem_center_iff.mpr
    intro x
    apply e.injective
    simp only [map_mul]
    have he : e ((blockUEquiv e).symm u : L) = (u : L') :=
      congrArg Subtype.val ((blockUEquiv e).apply_symm_apply u)
    rw [he]
    exact mem_center_iff.mp hu (e x)

/-- The actual module quotients are transported through their fixed layers. -/
def blockModuleEquiv (e : L ≃* L') : BlockModule L ≃* BlockModule L' :=
  QuotientGroup.congr _ _ (blockUEquiv e) (map_blockFixed e)

@[simp] theorem blockModuleEquiv_mk (e : L ≃* L') (u : blockU L) :
    blockModuleEquiv e (QuotientGroup.mk' (blockFixed L) u) =
      QuotientGroup.mk' (blockFixed L') (blockUEquiv e u) := rfl

theorem blockUEquiv_conjugate (e : L ≃* L') (l : L) (u : blockU L) :
    blockUEquiv e (blockConjugate L l u) =
      blockConjugate L' (e l) (blockUEquiv e u) := by
  apply Subtype.ext
  exact (map_mul e (l * u) l⁻¹).trans (by rw [map_mul, map_inv]; rfl)

/-- Transport both intrinsic quotients and the intertwining, using the same acting model. -/
def transportModel {A V : Type*} [Group A] [Group V] {ρ : A →* MulAut V}
    (e : L ≃* L') (m : BlockModuleModel L ρ) : BlockModuleModel L' ρ where
  quotientIso := (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans m.quotientIso
  moduleIso := (blockModuleEquiv e.symm).trans m.moduleIso
  intertwining l u := by
    change m.moduleIso (blockModuleEquiv e.symm
      (QuotientGroup.mk' (blockFixed L') (blockConjugate L' l u))) = _
    rw [blockModuleEquiv_mk, blockUEquiv_conjugate, m.intertwining]
    rfl

/-- The quotient projection after transport is the original projection composed
with the inverse isomorphism. -/
@[simp] theorem transportModel_projection {F : Type*} [Field F]
    (e : L ≃* L') (m : BlockModuleModel L (Matrix.SL2.naturalAction F)) (l : L') :
    projection (transportModel e m) l = projection m (e.symm l) := rfl

/-- The second block's model uses its actual ambient conjugation equivalence. -/
def conjugateModel {G : Type*} [Group G] (L : Subgroup G) (r : G)
    {A V : Type*} [Group A] [Group V] {ρ : A →* MulAut V}
    (m : BlockModuleModel L ρ) :
    BlockModuleModel (L.map (MulAut.conj r).toMonoidHom) ρ :=
  transportModel ((MulAut.conj r).subgroupMap L) m

/-- Corresponding conjugate elements have exactly the same matrix coordinate. -/
@[simp] theorem conjugateModel_projection {G F : Type*} [Group G] [Field F]
    (L : Subgroup G) (r : G)
    (m : BlockModuleModel L (Matrix.SL2.naturalAction F)) (l : L) :
    projection (conjugateModel L r m) ((MulAut.conj r).subgroupMap L l) = projection m l := by
  change projection m (((MulAut.conj r).subgroupMap L).symm
    ((MulAut.conj r).subgroupMap L l)) = projection m l
  rw [MulEquiv.symm_apply_apply]

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
