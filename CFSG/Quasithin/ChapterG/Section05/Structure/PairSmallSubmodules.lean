module
public import CFSG.Quasithin.ChapterG.Section05.Structure.PairQuotients

/-!
# Small submodules of the fifteen-pair module

Projecting away the fixed constant line places a pair submodule in the
even duad core. The complete G.5.3 flag puts every submodule of dimension
at most five in the annihilator of the line-complement nine-space.
The invariant pairing identifies that annihilator with the dual of the
five-dimensional augmentation cover. Thus a small pair submodule maps
to the dual cover with a fixed kernel; no central line is discarded.

Source: Aschbacher--Smith G.5.3, printed pp.344--345, as used for
Q/C_Q(U_L) in 13.8.33, printed p.968. The original quotient application
is in Chapter13 Section08, OriginalCentralizerCubic.
-/

public section
open Representation BinaryPermutation BinaryDuadModule BinaryDuadStructure
open Theory.SpecificGroups.SymmetricSix Representation.BinaryCoverSocle
namespace CFSG.Quasithin.ChapterG.Section05.Structure

private noncomputable def coreEvenProjection : Representation.IntertwiningMap alternatingPointAction coreAction where
  toLinearMap := (LinearMap.id - (augmentation Duad).smulRight (allOne Duad)).codRestrict
    (core Duad) (by
      intro v
      change augmentation Duad (v - augmentation Duad v • allOne Duad) = 0
      rw [map_sub, map_smul, augmentation_allOne]
      change augmentation Duad v - augmentation Duad v * 1 = 0
      simp)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change pointAction g.val v - augmentation Duad (pointAction g.val v) • allOne Duad =
      pointAction g.val (v - augmentation Duad v • allOne Duad)
    rw [map_sub,map_smul]
    change _ - augmentation Duad (representation Duad _ v) • _ =
      _ - _ • representation Duad _ (allOne Duad)
    rw [augmentation_permute,permute_allOne]

private theorem coreEvenProjection_kernel_fixed (v : Full Duad)
    (hv : coreEvenProjection v = 0) (g : S6) : pointAction g v = v := by
  have he : v = augmentation Duad v • allOne Duad := by
    apply sub_eq_zero.mp
    exact congrArg Subtype.val hv
  rw [he,map_smul]
  change _ • representation Duad _ (allOne Duad) = _
  rw [permute_allOne]

private theorem small_core_submodule_le (S : Subrepresentation coreAction)
    (hd : Module.finrank (ZMod 2) S.toSubmodule ≤ 5) :
    S ≤ perp coreSelfDual coreLines := by
  rcases core_subrepresentation_cases middleCoverData S with h | h | h | h | h | h
  · exact h ▸ bot_le
  · exact h ▸ (coreFlag_strictAnti middleCoverData (by decide : (3 : Fin 6) < 4)).le
  · exact h.le
  · rw [h,coreLines_finrank] at hd; omega
  · rw [h,coreNatural_perp_finrank] at hd; omega
  · rw [h,finrank_whole,core_finrank] at hd; omega

private noncomputable def corePerpQuotientDuality :
    Representation.Equiv (perp coreSelfDual coreLines).toRepresentation coreQuotientAction.dual :=
  Representation.Equiv.mk
    ((coreSelfDual.toLinearEquiv.ofSubmodule' coreLines.toSubmodule.dualAnnihilator).trans
      coreLines.toSubmodule.dualQuotEquivDualAnnihilator.symm)
    (by
      intro g
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      induction w using Submodule.Quotient.induction_on with
      | _ w => exact corePairing_invariant g v.val w)

/-- A small pair submodule maps to the dual augmentation cover with fixed kernel. -/
theorem small_pair_dual_cover_map
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) S6 X)
    (j : ρ.IntertwiningMap SixPairsQuadratic.action) (hj : Function.Injective j)
    (hd : Module.finrank (ZMod 2) X ≤ 5) :
    ∃ f : Representation.IntertwiningMap (ρ.comp A6.subtype) (alternatingCoreRepresentation (Fin 6)).dual,
      ∀ x, f x = 0 → ∀ g : S6, ρ g x = x := by
  let jD := pairCoordinates.symm.toLinearMap.comp j.toLinearMap
  have hjD (g : S6) (x : X) : jD (ρ g x) = pointAction g (jD x) := by
    apply pairCoordinates.injective
    change pairCoordinates (pairCoordinates.symm (j (ρ g x))) = _
    rw [pairCoordinates.apply_symm_apply,pairCoordinates_equivariant]
    change j (ρ g x) = SixPairsQuadratic.action g (pairCoordinates (pairCoordinates.symm (j x)))
    rw [pairCoordinates.apply_symm_apply,j.isIntertwining]
  let jA : Representation.IntertwiningMap (ρ.comp A6.subtype) alternatingPointAction :=
    jD.intertwiningMap_of_isIntertwiningMap _ _ (fun a x => hjD a.val x)
  let q := coreEvenProjection.comp jA
  have hr : q.range ≤ perp coreSelfDual coreLines := small_core_submodule_le q.range
    ((LinearMap.finrank_range_le q.toLinearMap).trans hd)
  let r : Representation.IntertwiningMap (ρ.comp A6.subtype) (perp coreSelfDual coreLines).toRepresentation :=
    (q.toLinearMap.codRestrict _ (fun x => hr ⟨x,rfl⟩)).intertwiningMap_of_isIntertwiningMap _ _
      (fun a x => Subtype.ext (IntertwiningMap.isIntertwining _ _ q a x))
  obtain ⟨E⟩ := duad_cover_coordinates
  let d := OneCohomology.dualIntertwining E.symm.toIntertwiningMap
  let f := d.comp (corePerpQuotientDuality.toIntertwiningMap.comp r)
  refine ⟨f,fun x hx g => ?_⟩
  have hq : q x = 0 := by
    have hi : Function.Injective d := LinearMap.dualMap_injective_of_surjective E.symm.toLinearEquiv.surjective
    have he : corePerpQuotientDuality (r x) = 0 := hi (hx.trans (map_zero d).symm)
    have he' : r x = 0 := corePerpQuotientDuality.toLinearEquiv.injective (he.trans (map_zero _).symm)
    exact congrArg Subtype.val he'
  apply hj
  apply pairCoordinates.symm.injective
  change jD (ρ g x) = jD x
  rw [hjD]
  exact coreEvenProjection_kernel_fixed (jD x) hq g

end CFSG.Quasithin.ChapterG.Section05.Structure
