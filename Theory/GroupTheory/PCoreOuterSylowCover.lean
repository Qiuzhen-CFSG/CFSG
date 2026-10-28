module
public import Theory.GroupTheory.PCoreNormalizerAction
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow coverage through the full two-core section action

Let K be normal in H. If Out(K/O₂(K)) and the kernel of H's conjugation
action on K/O₂(K) are two-groups, then K and a Sylow two-subgroup generate H.
The inner-action preimage is exactly K times that full kernel; the Sylow
covers the outer image and contains the normal two-group kernel.

Normality is relative to H, and the quotient uses K's intrinsic two-core.
Source application: Aschbacher--Smith 8.3.10(2), printed p.726,
refs/quasithin.pdf, with K=K_z and H=C_G(z).
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal section with two-group outer action and full action kernel
is covered by the original subgroup and any Sylow two-subgroup. -/
theorem subgroup_sup_sylow_eq_top_of_twoCore_action_kernel
    (H K : Subgroup G) (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (S : Sylow 2 H)
    (houter : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)))
    (hker : IsPGroup 2 ((pCoreNormalizerAction 2 K).comp (inclusion hHK)).ker) :
    K.subgroupOf H ⊔ (S : Subgroup H) = ⊤ := by
  let f := (pCoreNormalizerAction 2 K).comp (inclusion hHK)
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup (K ⧸ pCore 2 K))).comp f
  have him : (K.subgroupOf H).map f = MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
    apply le_antisymm
    · rintro _ ⟨k,hk,rfl⟩
      exact ⟨QuotientGroup.mk' _ (⟨k,hk⟩ : K),
        (pCoreNormalizerAction_on_component 2 K ⟨k,hk⟩).symm⟩
    · rintro _ ⟨u,rfl⟩
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) u
      exact ⟨⟨k,hKH k.property⟩,k.property,pCoreNormalizerAction_on_component 2 K k⟩
  have hqk : q.ker = K.subgroupOf H ⊔ f.ker := by
    rw [show q.ker = ((QuotientGroup.mk' (MulAut.innerSubgroup (K ⧸ pCore 2 K))).ker).comap f
      from (MonoidHom.comap_ker _ _).symm,QuotientGroup.ker_mk',←him,comap_map_eq]
  let U := S.mapSurjective q.rangeRestrict_surjective
  have htop : ((S : Subgroup H).map q.rangeRestrict) = ⊤ :=
    (U.is_maximal' ((houter.to_subgroup q.range).to_subgroup ⊤) le_top).symm
  have hh := congrArg (Subgroup.comap q.rangeRestrict) htop
  rw [Subgroup.comap_map_eq,MonoidHom.ker_rangeRestrict,hqk,Subgroup.comap_top] at hh
  have hkS : f.ker ≤ (S : Subgroup H) := hker.le_sylow_of_normal S
  rw [sup_comm (S : Subgroup H),sup_assoc,sup_eq_right.mpr hkS] at hh
  exact hh

end Theory.GroupTheory
