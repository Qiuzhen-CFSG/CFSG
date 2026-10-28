module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.AffineModule

/-!
# Transport of affine block modules

An isomorphism with the concrete affine group transports O₂, its commutator
layer U, the fixed subgroup C_U, and conjugation. Thus the natural model on
the original block carrier has the actual quotient and intertwining required
by C.1.12. Shortness comes from the given block; no classification is hidden
in this transport.

The private quotient transport follows the same construction as
`ChapterE/Section06/Hyperplanes/Enlargement/BlockInspection/Lifting/CharacteristicTwoBlocks/Factors.lean`.
It is kept here to avoid importing that later source argument into Chapter 2.
The public model definition keeps its implementation private.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526, and C.1.7/C.1.12,
printed pp.123–124.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes
open Subgroup ChapterC
variable {A B : Type*} [Group A] [Group B]

private theorem transport_blockU (e : A ≃* B) :
    (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective, blockU]

private def blockUEquiv (e : A ≃* B) : blockU A ≃* blockU B :=
  (e.subgroupMap (blockU A)).trans (MulEquiv.subgroupCongr (transport_blockU e))

private theorem transport_blockFixed (e : A ≃* B) :
    (blockFixed A).map (blockUEquiv e).toMonoidHom = blockFixed B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr e ⟨x, hx⟩).property
  · intro x hx
    exact ⟨(blockUEquiv e).symm x,
      (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property,
      (blockUEquiv e).apply_symm_apply x⟩

private def coreQuotientEquiv (e : A ≃* B) :
    (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private def blockModuleEquiv (e : A ≃* B) : BlockModule A ≃* BlockModule B :=
  QuotientGroup.congr _ _ (blockUEquiv e) (transport_blockFixed e)

private theorem blockUEquiv_conjugate (e : A ≃* B) (a : A) (u : blockU A) :
    blockUEquiv e (blockConjugate A a u) =
      blockConjugate B (e a) (blockUEquiv e u) := by
  apply Subtype.ext
  change e (a * (u : A) * a⁻¹) = e a * e (u : A) * (e a)⁻¹
  simp only [map_mul, map_inv]

private def pullbackModel {X V : Type*} [Group X] [Group V]
    {rho : X →* MulAut V} (model : BlockModuleModel A rho) (e : B ≃* A) :
    BlockModuleModel B rho where
  quotientIso := (coreQuotientEquiv e).trans model.quotientIso
  moduleIso := (blockModuleEquiv e).trans model.moduleIso
  intertwining b u := by
    change model.moduleIso (QuotientGroup.mk' (blockFixed A)
      (blockUEquiv e (blockConjugate B b u))) =
      rho (model.quotientIso (QuotientGroup.mk' (pCore 2 A) (e b)))
        (model.moduleIso (QuotientGroup.mk' (blockFixed A) (blockUEquiv e u)))
    rw [blockUEquiv_conjugate]
    exact model.intertwining (e b) (blockUEquiv e u)

/-- An affine group isomorphism determines both intrinsic quotients and their
compatible natural action on the original carrier. -/
noncomputable def affineModel_of_equiv {d : ℕ} (hd : 2 ≤ d) (e : B ≃* Affine d) :
    BlockModuleModel B (naturalAction d) :=
  pullbackModel (affineBlockModuleModel d hd) e

/-- The shortness of the actual block is retained while its quotient and module
are constructed from the affine identification. -/
theorem linearTwoBlock_of_affine_equiv {d : ℕ} (hd : 2 ≤ d)
    (hB : IsShort B) (e : B ≃* Affine d) : IsLinearTwoBlock B d := by
  let : NeZero d := ⟨by omega⟩
  let model := affineModel_of_equiv hd e
  refine ⟨hd, hB, ?_, naturalAction d, ⟨model⟩, fun _ _ => rfl⟩
  exact ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
    ⟨model.quotientIso.trans (slEquivPSL d)⟩⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes
end
