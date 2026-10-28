module
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.GeneralizedFitting.CoreCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PCoreResidualFrattiniKernel
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Joint detection of a two-subgroup and a generalized Fitting lift

Let N be a normal perfect subgroup of a finite group H with H/N a two-group.
A surjection from H to a group with trivial two-core is assumed to have kernel
central on N modulo O₂(N). The image of the lift of F*(N/O₂(N)) contains the
target generalized Fitting subgroup. Consequently a two-subgroup whose
commutator with that lift is killed must itself lie in O₂(H).

Central covers preserve F*: lift components using the solvable residual and
lift their centralizers using perfectness. The residual Frattini kernel theorem
then detects two-subgroups, because the center of a perfect group lies in its
Frattini subgroup. This avoids assuming that the center of N is central in H.

Source application: Aschbacher--Smith, 11.5.8, printed p.784, simultaneous
movement on a chief section by V and the conjugated generalized Fitting lift.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {H J : Type*} [Group H] [Group J] [Finite H] [Finite J]

theorem generalizedFitting_map_of_central_kernel
    (f : H →* J) (hf : Function.Surjective f) (hk : f.ker ≤ center H) :
    (generalizedFitting H).map f = generalizedFitting J := by
  let r := f.subgroupComap (fittingSubgroup J)
  have hr : r.ker ≤ center ((fittingSubgroup J).comap f) := by
    intro x hx
    have hh : f (x : H) = 1 := congrArg Subtype.val hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hk hh) y)
  let : Group.IsNilpotent ((fittingSubgroup J).comap f) :=
    Subgroup.isNilpotent_of_ker_le_center r hr
  apply generalizedFitting_map_eq_of_component_lifts f hf
  intro L hL
  let : IsMulCommutative f.ker := ⟨⟨fun x y =>
    Subtype.ext ((mem_center_iff.mp (hk x.property) y).symm)⟩⟩
  obtain ⟨hC, hm⟩ := cComponent_residual_preimage f hf hL.isCComponent
  let C := (solvableResidual (L.comap f)).map (L.comap f).subtype
  let : Group.IsPerfect C := hC.perfect
  refine ⟨C, ⟨hC.subnormal, hC.isQuasisimple_of_fitting_centralizes ?_⟩, hm⟩
  rw [← comap_centralizer_map_eq_of_perfect f C (hk.trans (center_le_centralizer (C : Set H)))]
  rw [hm]
  apply map_le_iff_le_comap.mp
  have hfit : (fittingSubgroup H).map f ≤ fittingSubgroup J :=
    le_sSup ⟨Normal.map inferInstance f hf,
      Group.nilpotent_of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _)⟩
  exact hfit.trans (le_centralizer_iff.mp (hL.le_centralizer_of_solvable_normal _))

theorem generalizedFitting_le_normal_of_two_quotient (N : Subgroup H) [N.Normal]
    (hq : IsPGroup 2 (H ⧸ N)) (hc : pCore 2 H = ⊥) :
    generalizedFitting H ≤ (generalizedFitting N).map N.subtype := by
  apply generalizedFitting_le_map_of_le
  exact (generalizedFitting_le_pResidual_of_pCore_eq_bot hc).trans (sInf_le ⟨inferInstance, hq⟩)

end Theory.GroupTheory


open Subgroup
namespace Theory.GroupTheory
variable {H J : Type*} [Group H] [Group J] [Finite H]

theorem two_subgroup_le_core_of_central_residual_kernel
    (N : Subgroup H) [N.Normal] [Group.IsPerfect N]
    (hq : IsPGroup 2 (H ⧸ N)) (f : H →* J) (hf : Function.Surjective f)
    (hkill : pCore 2 H ≤ f.ker)
    (hk : N ⊓ f.ker ≤ ((center (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype)
    (A : Subgroup H) (hA : IsPGroup 2 A) (hAf : A ≤ f.ker) : A ≤ pCore 2 H := by
  let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hres : pResidual 2 H = N := le_antisymm (sInf_le ⟨inferInstance, hq⟩)
    (le_of_isPerfect_of_solvable_quotient N _)
  have hphi : pResidual 2 H ⊓ f.ker ≤
      ((frattini ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H))).comap
        (QuotientGroup.mk' (pCore 2 (pResidual 2 H)))).map (pResidual 2 H).subtype := by
    rw [hres]
    exact hk.trans (map_mono (comap_mono center_le_frattini_of_isPerfect))
  obtain ⟨S, hS⟩ := hA.exists_le_sylow
  rw [← f.sylow_inf_ker_eq_pCore_of_residual_frattini_kernel hf S hkill hphi]
  exact le_inf hS hAf

end Theory.GroupTheory

namespace Theory.GroupTheory
variable {H J : Type*} [Group H] [Group J] [Finite H] [Finite J]

/-- The source marker in a normal perfect subgroup covers the target F*. -/
theorem generalizedFitting_le_image_lift_of_central_kernel
    (N : Subgroup H) [N.Normal]
    (hq : IsPGroup 2 (H ⧸ N)) (f : H →* J) (hf : Function.Surjective f)
    (hkill : pCore 2 H ≤ f.ker) (hcore : pCore 2 J = ⊥)
    (hk : N ⊓ f.ker ≤ ((center (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype) :
    generalizedFitting J ≤
      (((generalizedFitting (N ⧸ pCore 2 N)).comap
        (QuotientGroup.mk' (pCore 2 N))).map N.subtype).map f := by
  let u := f.subgroupMap N
  have hkillN : pCore 2 N ≤ u.ker := by
    intro n hn
    apply Subtype.ext
    exact hkill ((show (pCore 2 N).map N.subtype ≤ pCore 2 H from
      le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩) (mem_map_of_mem N.subtype hn))
  let d := QuotientGroup.lift (pCore 2 N) u hkillN
  have hd : Function.Surjective d :=
    QuotientGroup.lift_surjective_of_surjective _ _ (f.subgroupMap_surjective N) _
  have hdker : d.ker ≤ center (N ⧸ pCore 2 N) := by
    intro z hz
    obtain ⟨n,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 N) z
    have hn : f (n : H) = 1 := congrArg Subtype.val hz
    obtain ⟨m,hm,he⟩ := hk ⟨n.property, hn⟩
    have hmn : m = n := Subtype.ext he
    exact hmn ▸ hm
  have hfg := generalizedFitting_map_of_central_kernel d hd hdker
  let : (N.map f).Normal := Normal.map inferInstance f hf
  let qf := QuotientGroup.map N (N.map f) f (le_comap_map f N)
  have hqf : Function.Surjective qf := by
    intro z
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (N.map f) z
    obtain ⟨x,rfl⟩ := hf j
    exact ⟨QuotientGroup.mk' N x,rfl⟩
  have hqJ : IsPGroup 2 (J ⧸ N.map f) := hq.of_surjective qf hqf
  have hle := generalizedFitting_le_normal_of_two_quotient (N.map f) hqJ hcore
  intro j hj
  obtain ⟨n,hn,hnj⟩ := hle hj
  rw [← hfg] at hn
  obtain ⟨z,hz,hzn⟩ := hn
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 N) z
  exact ⟨x, mem_map_of_mem N.subtype hz, (congrArg Subtype.val hzn).trans hnj⟩

/-- Killing the commutator with the marked F* forces any two-subgroup into O₂. -/
theorem two_subgroup_le_core_of_fitting_commutator_killed
    (N : Subgroup H) [N.Normal] [Group.IsPerfect N]
    (hq : IsPGroup 2 (H ⧸ N)) (f : H →* J) (hf : Function.Surjective f)
    (hkill : pCore 2 H ≤ f.ker) (hcore : pCore 2 J = ⊥)
    (hk : N ⊓ f.ker ≤ ((center (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype)
    (A : Subgroup H) (hA : IsPGroup 2 A)
    (hc : ⁅((generalizedFitting (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype, A⁆ ≤ f.ker) : A ≤ pCore 2 H := by
  have hFA := generalizedFitting_le_image_lift_of_central_kernel N hq f hf hkill hcore hk
  have hcomm := (Subgroup.map_eq_bot_iff _).mpr hc
  rw [map_commutator, commutator_comm] at hcomm
  have hAf : A.map f ≤ fittingSubgroup J :=
    ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (centralizer_le hFA)).trans centralizer_generalizedFitting_le_fitting
  have hAp : IsPGroup 2 ((A.map f).subgroupOf (fittingSubgroup J)) :=
    (hA.map f).comap_subtype
  obtain ⟨P,hP⟩ := hAp.exists_le_sylow
  have hAP : A.map f ≤ pCore 2 J := by
    have hm := map_mono (f := (fittingSubgroup J).subtype) hP
    rw [map_subgroupOf_eq_of_le hAf] at hm
    exact hm.trans (P.map_le_pCore inferInstance inferInstance 2)
  have hAfker : A ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp (bot_unique (hcore ▸ hAP))
  exact two_subgroup_le_core_of_central_residual_kernel N hq f hf hkill hk A hA hAfker
end Theory.GroupTheory

namespace Theory.GroupTheory
variable {K N : Type*} [Group K] [Group N]

theorem fitting_core_preimage_map_equiv (e : K ≃* N) :
    ((generalizedFitting (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K))).map
        e.toMonoidHom =
      (generalizedFitting (N ⧸ pCore 2 N)).comap (QuotientGroup.mk' (pCore 2 N)) := by
  let eQ := QuotientGroup.congr (pCore 2 K) (pCore 2 N) e (pCore_map_iso 2 e)
  have he := map_generalizedFitting_equiv eQ
  ext n
  rw [mem_map_equiv]
  change QuotientGroup.mk' (pCore 2 K) (e.symm n) ∈ generalizedFitting (K ⧸ pCore 2 K) ↔
    QuotientGroup.mk' (pCore 2 N) n ∈ generalizedFitting (N ⧸ pCore 2 N)
  rw [← he, mem_map_equiv]
  rfl
end Theory.GroupTheory
