module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.CoverDuality
public import Theory.Representation.ElementaryAbelianAction.Commutator
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Full short-block covers and marked commutator generation

The whole elementary abelian U(L) carries conjugation by L/O₂(L), since
shortness makes O₂(L) centralize U(L). Using the original quotient marking,
the given U(L)/C_U(L)(L) identification therefore yields a linear cover of
the coefficient representation. Two-perfection and commutator idempotence
prove [U(L),L] = U(L); the entire fixed kernel remains in this cover.

Detection on the dual coefficient module forces marked coinvariants of the
whole cover to vanish. Literal conjugation and the embedding L → G then
give Q = [Q,Y]. For the A₆ source configuration, the actual parabolic image
and O^{3′} residual discharge dual detection. The source normalization
reduction gives Q ≤ O₂(Y₊), centralization by D = C_I(Y₊), and exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7,
printed p.123; I.1.5–6, printed p.408; and the proof of 15.3.31,
printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover ChapterC
namespace ContainedCoreModels
variable {G : Type*} [Group G] [Finite G] {L Y : Subgroup G}
  {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) A V}

/-- Dual detection generates the actual short-block core, retaining its whole
fixed kernel and the original quotient actor. -/
theorem core_eq_commutator_of_short_detected_dual
    (hYL : Y ≤ L) (short : IsShort L)
    (model : BlockModuleModel L (BlockModels.multiplicativeAction ρ))
    (hdet : DetectedOn ρ.dual ((Y.subgroupOf L).map
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    extensionCore L = ⁅extensionCore L, Y⁆ := by
  let := short.elementary
  let actor : L →* A :=
    model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hactor : Function.Surjective actor :=
    model.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let action : A →* MulAut (blockU L) :=
    (QuotientGroup.lift (pCore 2 L) (MulAut.conjNormal (H := blockU L)) (by
      intro l hl
      change MulAut.conjNormal l = 1
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      change l * (u : L) * l⁻¹ = (u : L)
      rw [mem_centralizer_iff.mp (short.central u.property) l hl,
        mul_inv_cancel_right])).comp model.quotientIso.symm.toMonoidHom
  have haction (l : L) (u : blockU L) :
      action (actor l) u = blockConjugate L l u := by
    simp only [action, actor, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    rfl
  let : MulDistribMulAction A (blockU L) := MulDistribMulAction.compHom (blockU L) action
  let σ := ofElementaryAbelianAction (A := A) (G := blockU L) (p := 2)
  have hσ (l : L) (w : Additive (blockU L)) :
      (σ (actor l) w).toMul = blockConjugate L l w.toMul := haction l w.toMul
  let f : blockU L →* Multiplicative V :=
    model.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed L))
  have hf : Function.Surjective f :=
    model.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let p : σ.IntertwiningMap ρ :=
    { toLinearMap := f.toAdditiveLeft.toZModLinearMap 2
      isIntertwining' a := by
        ext w : 1
        obtain ⟨l, rfl⟩ := hactor a
        change (f (σ (actor l) w).toMul).toAdd = ρ (actor l) (f w.toMul).toAdd
        rw [hσ]
        exact congrArg Multiplicative.toAdd (model.intertwining l w.toMul) }
  have hp : IsCover p := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      obtain ⟨u, hu⟩ := hf (Multiplicative.ofAdd v)
      exact ⟨Additive.ofMul u, congrArg Multiplicative.toAdd hu⟩
    · intro w hw a
      obtain ⟨l, rfl⟩ := hactor a
      apply Additive.toMul.injective
      rw [hσ]
      apply Subtype.ext
      have hk : f w.toMul = 1 := congrArg Multiplicative.ofAdd hw
      have hk' : QuotientGroup.mk' (blockFixed L) w.toMul = 1 :=
        model.moduleIso.injective (hk.trans model.moduleIso.map_one.symm)
      have hz : (w.toMul : L) ∈ center L := (QuotientGroup.eq_one_iff w.toMul).mp hk'
      change l * (w.toMul : L) * l⁻¹ = (w.toMul : L)
      rw [mem_center_iff.mp hz l, mul_inv_cancel_right]
    · apply coinvariants_ker_eq_top_of_commutator_eq (blockU L) σ actor
        (fun l w => congrArg Subtype.val (hσ l w))
      exact commutator_isPPerfect_idempotent (⊤ : Subgroup L) (pCore 2 L)
        (short.twoPerfect.of_surjective (topEquiv (G := L)).symm.toMonoidHom
          (topEquiv (G := L)).symm.surjective)
        pCore_isPGroup (by rw [normalizer_eq_top])
  let B := (Y.subgroupOf L).map actor
  have hgen : Coinvariants.ker (σ.comp B.subtype) = ⊤ :=
    cover_coinvariants_of_detected_dual p hp B hdet
  let C : Subgroup (blockU L) := ⁅blockU L, Y.subgroupOf L⁆.subgroupOf (blockU L)
  let U : Submodule (ZMod 2) (Additive (blockU L)) :=
    AddSubgroup.toZModSubmodule 2 C.toAddSubgroup
  have hspan : Coinvariants.ker (σ.comp B.subtype) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, w⟩, rfl⟩
    obtain ⟨l, hl, he⟩ := a.property
    change ((σ a.val w).toMul : L) / (w.toMul : L) ∈ ⁅blockU L, Y.subgroupOf L⁆
    rw [← he, hσ, div_eq_mul_inv]
    change ⁅l, (w.toMul : L)⁆ ∈ ⁅blockU L, Y.subgroupOf L⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hl w.toMul.property
  have hUC : blockU L ≤ ⁅blockU L, Y.subgroupOf L⁆ := by
    intro u hu
    exact hspan (hgen ▸ (show Additive.ofMul (⟨u, hu⟩ : blockU L) ∈
      (⊤ : Submodule (ZMod 2) (Additive (blockU L))) from trivial))
  have hamb := map_mono (f := L.subtype) hUC
  rw [map_commutator, BlockModels.blockU_map, map_subgroupOf_eq_of_le hYL] at hamb
  exact le_antisymm hamb (le_normalizer_iff_commutator_le_left.mp
    (hYL.trans (normalizes_extensionCore L.le_normalizer)))

section AlternatingSource
variable {κ : GroupClass} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}
  (s : SourceData κ d c) (short : IsShort c.L)
  (model : BlockModuleModel c.L
    (BlockModels.multiplicativeAction BlockModels.Alternating.action))
  (plane : Submodule (ZMod 2) BlockModels.Alternating.Coefficients)
  (dimension : Module.finrank (ZMod 2) plane = 2)
  (invariant : ∀ g ∈ Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.T0,
    plane.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = plane)
  (parabolic : ((d.M ⊓ c.L).subgroupOf c.L).map
    (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
      BlockModels.planeStabilizer BlockModels.Alternating.action plane)
include s short model plane dimension invariant parabolic

/-- The marked A₆ residual generates the whole source core. -/
theorem alternating_core_eq_commutator :
    extensionCore c.L = ⁅extensionCore c.L, d.Yplus⁆ := by
  apply core_eq_commutator_of_short_detected_dual s.contains short model
  have hY : d.Yplus.subgroupOf c.L =
      (primeToResidual 3 ((d.M ⊓ c.L).subgroupOf c.L)).map
        ((d.M ⊓ c.L).subgroupOf c.L).subtype := by
    apply Subgroup.map_injective c.L.subtype_injective
    rw [map_subgroupOf_eq_of_le s.contains,
      map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le inf_le_right]
    exact s.component_residual
  rw [hY, map_embedded_primeToResidual_of_hom, parabolic]
  exact Alternating.dual_detected_on_parabolic plane dimension invariant

/-- The A₆ core lies in the two-core of the original Y₊. -/
theorem alternating_core_le_yplus_core :
    extensionCore c.L ≤ d.Yplus.pCoreIn 2 := by
  rw [alternating_core_eq_commutator s short model plane dimension invariant parabolic]
  exact core_commutator_le_yplus_core s

/-- The source D centralizes the entire A₆ core. -/
theorem alternating_centralizes_core :
    yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G) :=
  inf_le_right.trans (centralizer_le
    ((alternating_core_le_yplus_core s short model plane dimension invariant parabolic).trans
      (pCoreIn_le 2 d.Yplus)))

/-- Exclusion of the A₆ marked model using exactly the source inputs. -/
theorem alternating_excluded : False :=
  s.excluded_of_models (.alternating short model plane dimension invariant parabolic)
    (alternating_centralizes_core s short model plane dimension invariant parabolic)

end AlternatingSource

end ContainedCoreModels
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
