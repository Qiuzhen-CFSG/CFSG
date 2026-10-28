module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Configurations
public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# Marked commutators on full covering modules

A perfect central cover p : W → V becomes, after dualizing, a submodule
of the universal dual cover of V*. If restriction to B detects every
V*-valued cocycle, the dual W* has no B-fixed vectors. Annihilator duality
therefore proves [W,B] = W, including the entire central kernel of p.

For the A₆ marked parabolic we transport cocycles through the actual
self-duality of the natural permutation section and apply the checked
cubic tests. This establishes generation for every full covering module.
Transport from the actual short group's U(L) to such a linear cover is a
separate obligation; no whole-group containment is claimed here.

Source: Aschbacher–Smith, I.1.5–6, printed p.408, and the short-block
calculation in the proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Representation Representation.OneCohomology

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover
namespace ContainedCoreModels

variable {k A V W : Type*} [Field k] [Group A]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Contragradient cocycle detection generates the whole cover, including its kernel. -/
theorem cover_coinvariants_of_detected_dual
    {ρ : Representation k A V} {σ : Representation k A W}
    (p : σ.IntertwiningMap ρ) (hp : IsCover p) (B : Subgroup A)
    (hdet : DetectedOn ρ.dual B) :
    Coinvariants.ker (σ.comp B.subtype) = ⊤ := by
  have hinj := LinearMap.dualMap_injective_of_surjective hp.1
  have hfixed : fixed ρ.dual = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have hh : dualIntertwining p v ∈ fixed σ.dual := by
      intro a
      rw [← (dualIntertwining p).isIntertwining, hv a]
    have hz : dualIntertwining p v = 0 := by
      have hbot : dualIntertwining p v ∈ (⊥ : Submodule k (Module.Dual k W)) :=
        (fixed_dual_eq_bot_iff σ).mpr hp.2.2 ▸ hh
      exact hbot
    exact hinj (hz.trans (dualIntertwining p).map_zero.symm)
  obtain ⟨d,hd,_⟩ := exists_dualCoverEmbedding (dualIntertwining p)
    hinj (cover_dual_isDualCover p hp)
  apply (fixed_dual_eq_bot_iff (σ.comp B.subtype)).mp
  apply le_antisymm _ bot_le
  intro f hf
  have hh : d f = 0 := (detectedOn_iff_universal_fixed ρ.dual B hfixed).mp hdet (d f) (by
    intro b hb
    rw [← d.isIntertwining]
    exact congrArg d (hf ⟨b,hb⟩))
  exact hd (hh.trans d.map_zero.symm)

namespace Alternating
open BlockModels.Alternating
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-- Detection for the contragredient uses the genuine natural-section pairing. -/
theorem dual_detected_on_parabolic
    (plane : Submodule (ZMod 2) Coefficients)
    (dimension : Module.finrank (ZMod 2) plane = 2)
    (invariant : ∀ g ∈ T0,
      plane.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = plane) :
    DetectedOn action.dual
      ((Subgroup.primeToResidual 3 (BlockModels.planeStabilizer action plane)).map
        (BlockModels.planeStabilizer action plane).subtype) := by
  let e := BinaryPermutation.naturalDualEquiv (Fin 6)
  have he (a : Actor) (v : Module.Dual (ZMod 2) Coefficients) :
      e.symm (action.dual a v) = action a (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact ((BinaryPermutation.naturalDualEquiv_equivariant (Fin 6) a.val (e.symm v)).trans
      (congrArg (action.dual a) (e.apply_symm_apply v))).symm
  apply detectedOn_transport action.dual action (MulEquiv.refl Actor) e.symm he
  change DetectedOn action ((_ : Subgroup Actor).map (MonoidHom.id Actor))
  rw [Subgroup.map_id]
  exact BlockModels.Alternating.detectedOn_invariantPlane_residual plane dimension invariant

/-- The marked A₆ residual generates every perfect central cover of the natural section. -/
theorem cover_coinvariants
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {σ : Representation (ZMod 2) Actor U}
    (p : σ.IntertwiningMap action) (hp : IsCover p)
    (plane : Submodule (ZMod 2) Coefficients)
    (dimension : Module.finrank (ZMod 2) plane = 2)
    (invariant : ∀ g ∈ T0,
      plane.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = plane) :
    Coinvariants.ker (σ.comp
      ((Subgroup.primeToResidual 3 (BlockModels.planeStabilizer action plane)).map
        (BlockModels.planeStabilizer action plane).subtype).subtype) = ⊤ :=
  cover_coinvariants_of_detected_dual p hp _
    (dual_detected_on_parabolic plane dimension invariant)

end Alternating

end ContainedCoreModels
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
