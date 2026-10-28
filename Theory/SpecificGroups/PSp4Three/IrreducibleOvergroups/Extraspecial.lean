module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.Reduction
public import Theory.GroupTheory.SimpleSectionSolvableLayers.Permutation
public import Theory.GroupTheory.ExtraspecialThirtyTwoFivePointAction
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Alternating layers for the extraspecial-core branch

The involution geometry of a self-centralizing extraspecial two-core of
minus type and order 32 gives a five-point action with that core as kernel.
The central kernel of the symplectic projection lies in the core, so this
action descends to the actual projective subgroup with solvable kernel.
Adding a fixed sixth point and taking the inverse image of A₆ gives the
required normal layers and an injection from the actual inner quotient.

This proves the implication from `HasExtraspecialLiftCore`, without assuming
any maximal-subgroup classification. The five-point construction is from the
intrinsic extraspecial results in `ExtraspecialThirtyTwoFivePointAction`,
following Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three

open Theory.GroupTheory

/-- Any six-point action with solvable kernel yields the actual alternating
quotient embedding required by the section interface. -/
public theorem hasAlternatingLayers_of_sixPointAction {G : Type*} [Group G]
    (f : G →* Equiv.Perm (Fin 6)) [Group.IsSolvable f.ker] :
    HasAlternatingLayers G :=
  Or.inr (SolvableLayersEmbedding.of_permutation_solvable_kernel f)

/-- A faithful six-point action is a special case, with trivial inner kernel. -/
public theorem hasAlternatingLayers_of_faithful_sixPointAction {G : Type*} [Group G]
    (f : G →* Equiv.Perm (Fin 6)) (hf : Function.Injective f) :
    HasAlternatingLayers G := by
  have hs : Group.IsSolvable f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]
    infer_instance
  exact hasAlternatingLayers_of_sixPointAction f

/-- Extend by a fixed point; this changes neither the action kernel nor its
solvability. -/
public theorem hasAlternatingLayers_of_fivePointAction {G : Type*} [Group G]
    (f : G →* Equiv.Perm (Fin 5)) [Group.IsSolvable f.ker] :
    HasAlternatingLayers G := by
  let e : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 6) :=
    Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (by decide))
  have he : Function.Injective e := Equiv.Perm.viaEmbeddingHom_injective _
  have hk : (e.comp f).ker = f.ker := by
    ext x
    change e (f x) = 1 ↔ f x = 1
    rw [← map_one e, he.eq_iff]
  have hs : Group.IsSolvable (e.comp f).ker := hk.symm ▸ inferInstance
  exact hasAlternatingLayers_of_sixPointAction (e.comp f)

/-- The five-point action of the full inverse image descends through its
central kernel onto the actual projective subgroup. -/
public theorem HasExtraspecialLiftCore.exists_fivePointAction
    {U : Subgroup (PSp 2 (ZMod 3))} (hU : HasExtraspecialLiftCore U) :
    ∃ d : U →* Equiv.Perm (Fin 5), Group.IsSolvable d.ker := by
  obtain ⟨hspecial, hcard, hrank, hcentral⟩ := hU
  let := hspecial
  obtain ⟨f, hf⟩ := Subgroup.pCore_exists_five_point_action_of_extraspecial_card_thirty_two
    hrank hcard hcentral
  have hker : (preimageProjection U).ker ≤ f.ker := by
    rw [hf]
    intro x hx
    apply hcentral
    exact Subgroup.mem_centralizer_iff.mpr fun y _ =>
      Subgroup.mem_center_iff.mp (preimageProjection_ker_le_center U hx) y
  have hsolv : Group.IsSolvable f.ker := by
    rw [hf]
    let := pCore_isNilpotent (p := 2) (G := fullPreimage U)
    infer_instance
  obtain ⟨d, _, hd⟩ := exists_solvable_kernel_hom_of_surjective (preimageProjection U)
    (preimageProjection_surjective U) f hker
  exact ⟨d, hd⟩

/-- The structural extraspecial-core hypothesis supplies all normal layers
and the required quotient injection. -/
public theorem HasExtraspecialLiftCore.hasAlternatingLayers
    {U : Subgroup (PSp 2 (ZMod 3))} (hU : HasExtraspecialLiftCore U) :
    HasAlternatingLayers U := by
  obtain ⟨f, hf⟩ := hU.exists_fivePointAction
  let := hf
  exact hasAlternatingLayers_of_fivePointAction f

end Matrix.PSp4Three
