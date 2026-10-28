module

public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusControl
public import Theory.GroupTheory.PCoreImage


/-!
# Transport of the compatible PSL₃ root-torus calculation

An actual model isomorphism embeds the Borel, root group and chosen torus
in an ambient group. Actors normalizing the component and its Borel normalize
the Borel two-core. Conjugation therefore transports to Sylow-preserving
model automorphisms. If the cross commutator centralizes the embedded root
group, the matrix calculation puts it in the actual ambient Borel two-core.

The component need only be normalized by the actors, and the Borel core
is intrinsic to the Borel; no ambient normality is required.
Source: Aschbacher–Smith, E.6.25, printed p.255, using E.6.11(3b).
-/

public section

open scoped MatrixGroups commutatorElement
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.CartanActions.RootTorusControl
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G] [Finite G]

theorem commutator_le_core_of_model {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (L B A Y : Subgroup G) (e : L ≃* PSL(3,F))
    (hB : (borel F).map (L.subtype.comp e.symm.toMonoidHom) = B)
    (hY : Y ≤ (rootTorus F).range.map (L.subtype.comp e.symm.toMonoidHom))
    (hAL : A ≤ normalizer (L : Set G)) (hAB : A ≤ normalizer (B : Set G))
    (hc : ⁅A,Y⁆ ≤ centralizer ((projectiveCenter F).map
      (L.subtype.comp e.symm.toMonoidHom) : Set G)) :
    ⁅A,Y⁆ ≤ B.pCoreIn 2 := by
  let f : PSL(3,F) →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hk : IsPGroup 2 f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]
    exact IsPGroup.of_bot
  have hcore : (unipotent F).map f = B.pCoreIn 2 := by
    rw [← borel_core_eq F hF, map_pCoreIn_of_ker_isPGroup f hk (borel F), hB]
  have hAC : A ≤ normalizer (B.pCoreIn 2 : Set G) :=
    hAB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  apply commutator_le.mpr
  intro a ha y hy
  obtain ⟨z,hz,hzy⟩ := hY hy
  obtain ⟨t,rfl⟩ := hz
  let α : MulAut PSL(3,F) := (e.symm.trans (L.normalizerMonoidHom ⟨a,hAL ha⟩)).trans e
  have hα (x : PSL(3,F)) : f (α x) = a * f x * a⁻¹ := by
    change (e.symm (e ((L.normalizerMonoidHom ⟨a,hAL ha⟩) (e.symm x))) : G) = _
    rw [e.symm_apply_apply]
    rfl
  have hαU : (unipotent F).map α.toMonoidHom = unipotent F := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_map]
    have he : f.comp α.toMonoidHom = (MulAut.conj a).toMonoidHom.comp f := by
      ext x
      exact hα x
    rw [he,← Subgroup.map_map,hcore]
    exact mem_normalizer_iff_map_conj_eq.mp (hAC ha)
  have hd : f (α (rootTorus F t) * (rootTorus F t)⁻¹) = ⁅a,y⁆ := by
    rw [map_mul,map_inv,hα]
    change a * f (rootTorus F t) * a⁻¹ * (f (rootTorus F t))⁻¹ = _
    rw [hzy]
    rfl
  have hcent : α (rootTorus F t) * (rootTorus F t)⁻¹ ∈
      centralizer (projectiveCenter F : Set PSL(3,F)) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    apply hf
    simp only [map_mul,hd]
    exact mem_centralizer_iff.mp (hc (commutator_mem_commutator ha hy))
      (f x) (mem_map_of_mem f hx)
  have hu := displacement_mem_unipotent F hn hF α hαU t hcent
  rw [← hd,← hcore]
  exact mem_map_of_mem f hu

end Matrix.PSL3.CartanActions.RootTorusControl
