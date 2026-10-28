module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions
public import Theory.GroupTheory.PCoreImage

/-!
# Recovering the containing component from its action on U

Match the action of each element of K_U by an element of L_U. The remaining
factor lies in the actual action kernel, hence in L_U O₂(K_U). The source
Sylow normalizes L_U and contains O₂(K_U); consequently L_U is normal in
this product. The quotient is a two-group, so perfectness of K_U forces
the quotient to be trivial.

This proves the cocode branch from the full GL(U) action of 8.2.6 and its
kernel restriction. It also supplies the lifting step for the remaining
marked rank-four inspections; their action-image premise remains to be
proved. No overgroup classification is assumed as a theorem here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Proposition 8.2.8(1), printed p.719 (PDF p.736), first paragraph after
“It remains to establish (1)”. The literal L_U is GroupDeductions.localResidual.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G]

/-- The literal image of the relative normalizer of U in H acting on U. -/
@[expose] def actionImage (H U : Subgroup G) : Subgroup (MulAut U) :=
  (H.subgroupOf (normalizer (U : Set G))).map U.normalizerMonoidHom

private theorem eq_of_twoCore_cover [Finite G] (R K : Subgroup G) [Group.IsPerfect K]
    (hRK : R ≤ K) (hQR : K.pCoreIn 2 ≤ normalizer (R : Set G))
    (hcover : K ≤ R ⊔ K.pCoreIn 2) : R = K := by
  have hgen : R ⊔ K.pCoreIn 2 = K :=
    le_antisymm (sup_le hRK (pCoreIn_le 2 K)) hcover
  have hKR : K ≤ normalizer (R : Set G) :=
    hcover.trans (sup_le R.le_normalizer hQR)
  let : (R.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKR
  have hs : R.subgroupOf K ⊔ (K.pCoreIn 2).subgroupOf K = ⊤ := by
    rw [← subgroupOf_sup hRK (pCoreIn_le 2 K), hgen, subgroupOf_self]
  have hp := isPGroup_quotient_of_sup_eq_top (R.subgroupOf K)
    ((K.pCoreIn 2).subgroupOf K) (isPGroup_pCoreIn 2 K).comap_subtype hs
  let : Group.IsNilpotent (K ⧸ R.subgroupOf K) := hp.isNilpotent
  have hr : (⊤ : Subgroup K) ≤ R.subgroupOf K := by
    simpa only [solvableResidual_eq_top] using
      solvableResidual_le_of_solvable_quotient (R.subgroupOf K)
  exact le_antisymm hRK (fun k hk => hr (show (⟨k, hk⟩ : K) ∈ ⊤ from trivial))

/-- Lift the small-overgroup conclusion through the original U-action kernel.
The kernel may lie in L_U O₂(K_U), retaining the extra cubic layer in the
code branch. The Sylow containment makes O₂(K_U) normalize L_U, and
perfectness removes the remaining two-group supplement. This is an assembly
lemma; the rank-four overgroup argument must still prove its image premise. -/
theorem localResidual_eq_of_actionImage_le [Finite G] (L K U T : Subgroup G)
    [Group.IsPerfect K]
    (hRK : localResidual L U ≤ K) (hKN : K ≤ normalizer (U : Set G))
    (hQT : K.pCoreIn 2 ≤ T) (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G))
    (hker : K ⊓ centralizer (U : Set G) ≤ localResidual L U ⊔ K.pCoreIn 2)
    (haction : actionImage K U ≤ actionImage (localResidual L U) U) :
    localResidual L U = K := by
  apply eq_of_twoCore_cover _ K hRK
    (hQT.trans (normalizes_localResidual L U T hTL hTU))
  intro k hk
  let kn : normalizer (U : Set G) := ⟨k, hKN hk⟩
  have hm : U.normalizerMonoidHom kn ∈ actionImage K U :=
    mem_map_of_mem U.normalizerMonoidHom hk
  obtain ⟨rn, hr, he⟩ := haction hm
  have hrK : (rn : G) ∈ K := hRK hr
  have hc : rn⁻¹ * kn ∈ U.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hc
  have hcK : (rn : G)⁻¹ * k ∈ K := K.mul_mem (K.inv_mem hrK) hk
  have hd := (localResidual L U ⊔ K.pCoreIn 2).mul_mem
    (mem_sup_left hr) (hker ⟨hcK, hc⟩)
  simpa only [subtype_apply, mul_inv_cancel_left] using hd

/-- The cocode deduction in 8.2.8(1), conditional on the earlier full action
and two-core kernel. For elementary abelian U, its full automorphism group
is exactly GL(U). Normality is relative to the literal N_G(U). -/
theorem localResidual_eq_and_normal_of_full_action [Finite G]
    (L K U T : Subgroup G) [Group.IsPerfect K]
    (hRK : localResidual L U ≤ K) (hKN : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hQT : K.pCoreIn 2 ≤ T) (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G))
    (hker : K ⊓ centralizer (U : Set G) ≤ K.pCoreIn 2)
    (hfull : actionImage (localResidual L U) U = ⊤) :
    localResidual L U = K ∧
      ((localResidual L U).subgroupOf (normalizer (U : Set G))).Normal := by
  have he := localResidual_eq_of_actionImage_le L K U T hRK hKN hQT hTL hTU
    (hker.trans le_sup_right) (by rw [hfull]; exact le_top)
  exact ⟨he, he ▸ normal_subgroupOf_of_le_normalizer hNK⟩

/-- Apply the cocode deduction to an actual Sylow two-subgroup of N_G(U).
Relative normality of K_U supplies its two-core containment in that Sylow;
no ambient normality or replacement of the Sylow by an arbitrary two-group
is assumed. -/
theorem localResidual_eq_and_normal_of_full_sylow_action [Finite G]
    (L K U : Subgroup G) (S : Sylow 2 (normalizer (U : Set G))) [Group.IsPerfect K]
    (hRK : localResidual L U ≤ K) (hKN : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hSL : (S : Subgroup (normalizer (U : Set G))).map
      (normalizer (U : Set G)).subtype ≤ normalizer (L : Set G))
    (hker : K ⊓ centralizer (U : Set G) ≤ K.pCoreIn 2)
    (hfull : actionImage (localResidual L U) U = ⊤) :
    localResidual L U = K ∧
      ((localResidual L U).subgroupOf (normalizer (U : Set G))).Normal := by
  apply localResidual_eq_and_normal_of_full_action L K U _ hRK hKN hNK
    ((pCoreIn_mono_of_normalizes hKN hNK).trans (pCoreIn_le_sylow _ S)) hSL
    (map_subtype_le _) hker hfull

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
