module

public import Stellmacher.SectionTwo.SL2CentralKernelLift
public import Stellmacher.SectionsOneToFourDefs
public import Mathlib.GroupTheory.Transfer

/-!
# Normal closure of a seed disjoint from a central SL₂(2) kernel

Suppose a finite group maps onto SL₂(2) with central two-group kernel `N`.
The normal closure of any two-subgroup `V` disjoint from `N` is still
disjoint from `N`. This is the central-kernel group-theoretic step used in
Stellmacher (8.6)(1), without any graph or generation assumptions.

For nontrivial image, the lift `N ⊔ V` is an abelian self-normalizing Sylow
two-subgroup. Burnside transfer to that Sylow sends the conjugate closure
into `V` and sends `N` into `N`. The original disjointness therefore puts
the intersection in the transfer kernel, which is disjoint from `N`.
-/

namespace Stellmacher.SectionEight

open scoped IsMulCommutative

universe u

/-- A seed disjoint from a central two-kernel over SL₂(2) has disjoint normal closure. -/
public theorem sl2_central_kernel_seed_closure_disjoint
    {H : Type u} [Group H] [Finite H]
    (N V : Subgroup H) [N.Normal] (hNtwo : IsPGroup 2 N)
    (hcentral : N ≤ Subgroup.center H)
    (projection : H →* Stellmacher.Later.SL2Two)
    (hsurj : Function.Surjective projection) (hker : projection.ker = N)
    (hVtwo : IsPGroup 2 V) (hinter : V ⊓ N = ⊥) :
    Stellmacher.conjugateClosure V (⊤ : Subgroup H) ⊓ N = ⊥ := by
  by_cases himage : V.map projection = ⊥
  · have hVN : V ≤ N := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff V (f := projection)).mp himage
    have hVbot : V = ⊥ := by
      simpa only [inf_eq_left.mpr hVN] using hinter
    subst V
    apply le_antisymm (le_trans inf_le_left ?_) bot_le
    rw [Stellmacher.conjugateClosure, Subgroup.closure_le]
    rintro element ⟨actor, seed, rfl⟩
    have hseed : (seed : H) = 1 := seed.property
    simp [hseed]
  obtain ⟨_, _, _, _, hindex, sylow, hsylow, habelian, _, hnorm⟩ :=
    SectionTwo.centralKernelLift projection hsurj N V hker hcentral hNtwo hVtwo
      hinter himage
  let : IsMulCommutative sylow := habelian
  have hVjoin : V ≤ N ⊔ V := le_sup_right
  have hNjoin : N ≤ N ⊔ V := le_sup_left
  let transfer : H →* sylow := MonoidHom.transferSylow sylow hnorm
  have hpow (element : H) (helement : element ∈ N ⊔ V) :
      (transfer element : H) = element ^ 3 := by
    have hmem : element ∈ sylow := by
      change element ∈ (sylow : Subgroup H)
      rwa [hsylow]
    have heq := congrArg Subtype.val
      (MonoidHom.transferSylow_eq_pow sylow hnorm element hmem)
    simpa only [transfer, hsylow, hindex] using heq
  have hclosure : Stellmacher.conjugateClosure V (⊤ : Subgroup H) ≤
      (V.comap (sylow : Subgroup H).subtype).comap transfer := by
    rw [Stellmacher.conjugateClosure, Subgroup.closure_le]
    rintro element ⟨actor, seed, rfl⟩
    change (transfer ((actor : H) * (seed : H) * (actor : H)⁻¹) : H) ∈ V
    have hconj : transfer ((actor : H) * (seed : H) * (actor : H)⁻¹) =
        transfer seed := by
      simp [map_mul, map_inv]
    rw [hconj, hpow seed (hVjoin seed.property)]
    exact V.pow_mem seed.property 3
  apply le_antisymm ?_ bot_le
  intro element helement
  have hV : (transfer element : H) ∈ V := hclosure helement.1
  have hN : (transfer element : H) ∈ N := by
    rw [hpow element (hNjoin helement.2)]
    exact N.pow_mem helement.2 3
  have hone : (transfer element : H) = 1 := by
    have hmem : (transfer element : H) ∈ V ⊓ N := ⟨hV, hN⟩
    rwa [hinter, Subgroup.mem_bot] at hmem
  have hkerMem : element ∈ transfer.ker := by
    exact Subtype.ext hone
  have hmem : element ∈ transfer.ker ⊓ N := ⟨hkerMem, helement.2⟩
  rwa [disjoint_iff.mp
    (MonoidHom.ker_transferSylow_disjoint sylow hnorm N hNtwo)] at hmem

end Stellmacher.SectionEight
