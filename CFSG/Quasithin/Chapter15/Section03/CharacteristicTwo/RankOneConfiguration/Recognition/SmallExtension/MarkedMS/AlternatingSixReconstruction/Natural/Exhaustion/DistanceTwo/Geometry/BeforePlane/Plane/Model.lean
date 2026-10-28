module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.PointImage.Models
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed
public import Theory.Representation.BinaryOffender.RankOneCentralizer
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryPermutationSixCover.SeedPreimage

/-!
# The transposition-fixed hyperplane is moved by the point core

Four explicit displacements of one augmentation vector span the entire
transposition-fixed hyperplane. Conjugation and the natural-quotient lift
transport the calculation to both possible whole central covers, retaining
the fixed line. No hypothesis on the larger radical image is used.

Source: MS93 (3.6), printed p.871, the favorable-pair plane movement.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

private def seed : core (Fin 6) :=
  ⟨fun j => if j = 0 ∨ j = 4 then 1 else 0, by rw [mem_core]; decide +kernel⟩

private def actors : Fin 4 → Equiv.Perm (Fin 6)
  | 0 => Equiv.swap 0 1 * Equiv.swap 2 3
  | 1 => Equiv.swap 0 2 * Equiv.swap 1 3
  | 2 => Equiv.swap 0 3 * Equiv.swap 1 2
  | 3 => Equiv.swap 4 5

private theorem actor_mem (j : Fin 4) : actors j ∈ pointCore := by
  rw [ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional]
  apply (Six.mem_exceptional_iff _).mpr
  have cert : ∀ j : Fin 4, ∃ k : Fin 8, Six.exceptionalWords k = actors j := by decide +kernel
  exact cert j

private theorem fixed_span_table : ∀ v : Fin 6 → ZMod 2,
    (∑ j, v j) = 0 → representation (Fin 6) (Equiv.swap 4 5) v = v →
    v = v 1 • (representation (Fin 6) (actors 0) seed.val - seed.val) +
      v 2 • (representation (Fin 6) (actors 1) seed.val - seed.val) +
      v 3 • (representation (Fin 6) (actors 2) seed.val - seed.val) +
      v 4 • (representation (Fin 6) (actors 3) seed.val - seed.val) := by decide +kernel

theorem core_fixed_le_pointCore_moved :
    fixedSpace (coreRepresentation (Fin 6)) (zpowers (Equiv.swap 4 5)) ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ pointCore := by
  intro v hv
  have he : v = v.val 1 • (coreRepresentation (Fin 6) (actors 0) seed - seed) +
      v.val 2 • (coreRepresentation (Fin 6) (actors 1) seed - seed) +
      v.val 3 • (coreRepresentation (Fin 6) (actors 2) seed - seed) +
      v.val 4 • (coreRepresentation (Fin 6) (actors 3) seed - seed) := by
    apply Subtype.ext
    exact fixed_span_table v.val v.property
      (congrArg Subtype.val (hv ⟨_,mem_zpowers _⟩))
  rw [he]
  have hm (j : Fin 4) : coreRepresentation (Fin 6) (actors j) seed-seed ∈
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ pointCore :=
    Submodule.subset_span ⟨actors j,actor_mem j,seed,Submodule.mem_top,rfl⟩
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hm 0)) (Submodule.smul_mem _ _ (hm 1)))
    (Submodule.smul_mem _ _ (hm 2))) (Submodule.smul_mem _ _ (hm 3))

theorem cover_fixed_le_pointCore_moved
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hm : SixCover.IsNaturalOrCore ρ (MonoidHom.id _))
    (g t : Equiv.Perm (Fin 6))
    (ht : t ∈ pointCore.map (MulAut.conj g).toMonoidHom) (hs : t.IsSwap) :
    fixedSpace ρ (zpowers t) ≤
      subspaceCommutator ρ ⊤ (pointCore.map (MulAut.conj g).toMonoidHom) := by
  have ht0 := PointCoreTranspositionFixed.swap_eq_conjugate g t ht hs
  let B := pointCore.map (MulAut.conj g).toMonoidHom
  have transfer (f : core (Fin 6) →ₗ[ZMod 2] V)
      (hf : Function.Surjective f)
      (he : ∀ a v, f (coreRepresentation (Fin 6) a v) = ρ a (f v))
      (hfix : ∀ v, ρ t (f v) = f v → coreRepresentation (Fin 6) t v = v) :
      fixedSpace ρ (zpowers t) ≤ subspaceCommutator ρ ⊤ B := by
    intro v hv
    obtain ⟨w,rfl⟩ := hf v
    have hwt := hfix w (hv ⟨t,mem_zpowers t⟩)
    let z := coreRepresentation (Fin 6) g⁻¹ w
    have hz : z ∈ fixedSpace (coreRepresentation (Fin 6)) (zpowers (Equiv.swap 4 5)) := by
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      have hh := congrArg (coreRepresentation (Fin 6) g⁻¹) hwt
      rw [ht0] at hh
      simpa only [z,swap45,map_mul,Module.End.mul_apply,
        (coreRepresentation (Fin 6)).inv_self_apply] using hh
    have hzmov := core_fixed_le_pointCore_moved hz
    have hbound : subspaceCommutator (coreRepresentation (Fin 6)) ⊤ pointCore ≤
        (subspaceCommutator ρ ⊤ B).comap (f.comp (coreRepresentation (Fin 6) g)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,u,_,rfl⟩
      change f (coreRepresentation (Fin 6) g (coreRepresentation (Fin 6) a u-u)) ∈ subspaceCommutator ρ ⊤ B
      rw [map_sub,map_sub,he,he,he]
      have hconj : ρ g (ρ a (f u)) = ρ ((MulAut.conj g) a) (ρ g (f u)) := by
        simp only [MulAut.conj_apply,←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
      rw [hconj]
      exact Submodule.subset_span ⟨(MulAut.conj g) a,mem_map_of_mem _ ha,
        ρ g (f u),Submodule.mem_top,rfl⟩
    have hh := hbound hzmov
    change f (coreRepresentation (Fin 6) g z) ∈ subspaceCommutator ρ ⊤ B at hh
    simpa only [z,(coreRepresentation (Fin 6)).self_inv_apply] using hh
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩ <;> simp only [MonoidHom.id_apply] at hE
  · let f := E.symm.toLinearMap.comp (coreToNatural (Fin 6))
    apply transfer f (E.symm.surjective.comp coreToNatural_surjective)
    · intro a v
      apply E.injective
      simp only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
        hE,coreToNatural_equivariant]
    · intro v hv
      apply SixCover.six_core_fixed_of_natural_fixed
      have hh := congrArg E hv
      simpa only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,hE] using hh
  · apply transfer E.symm.toLinearMap E.symm.surjective
    · intro a v
      apply E.injective
      simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,hE]
    · intro v hv
      have hh := congrArg E hv
      simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,hE] using hh

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
