module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RadicalImages

/-!
# The radical and Thompson subgroup meet the actual star kernel

The quotient of the action kernel by O₂(KR) is odd. Hence its intersection
with any two-subgroup containing O₂(KR) is exactly that two-core. Applying
this to R shows that the original Thompson subgroup acts nontrivially,
using C.2.7(2) and Thompson heredity. No equality of the whole star kernel
with O₂(KR) is assumed; the possible odd central kernel is retained.

Source: Aschbacher–Smith C.2.7(1–3), pp.145–146.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

private theorem twoGroup_inf_eq_of_odd_kernel (A N P : Subgroup G) [P.Normal]
    (hA : IsPGroup 2 A) (hPA : P ≤ A) (hPN : P ≤ N)
    (ho : Nat.Coprime 2 (Nat.card (N.map (QuotientGroup.mk' P)))) : A ⊓ N = P := by
  let q := QuotientGroup.mk' P
  obtain ⟨n,hn⟩ := (hA.map q).exists_card_eq
  have hd : Disjoint (A.map q) (N.map q) :=
    disjoint_of_coprime_natCard (by rw [hn]; exact ho.pow_left n)
  have hm : (A ⊓ N).map q = ⊥ := bot_unique ((map_inf_le A N q).trans (disjoint_iff.mp hd).le)
  have hp : A ⊓ N ≤ P := by
    have hh := (map_eq_bot_iff (A ⊓ N)).mp hm
    simpa only [q,QuotientGroup.ker_mk'] using hh
  exact le_antisymm hp (le_inf hPA hPN)

theorem starKernel_core_image_coprime_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    Nat.Coprime 2 (Nat.card ((starKernel K R).map
      (QuotientGroup.mk' (pCore 2 (K ⊔ R : Subgroup G))))) := by
  let J := K ⊔ R
  let K₀ := K.subgroupOf J
  let R₀ := R.subgroupOf J
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hK : K₀.IsCComponent := h.component.2.subgroupOf_of_le le_sup_left h.join_le
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hgen : K₀ ⊔ R₀ = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),subgroupOf_self]
  have hkernel := (kernel_offender_of_normal_input h).1
  have hmove : ¬K₀ ≤ starKernel K R := by
    intro hh
    apply starImage_ne_bot_of_bound h.normalizes h.quasisimple hkernel.upper
    exact (Subgroup.map_eq_bot_iff K₀).mpr (by simpa only [QuotientGroup.ker_mk'] using hh)
  exact QuasisimpleThompson.core_kernel_coprime K₀ R₀ (starKernel K R) hK hR.comap_subtype
    hgen hkernel.lower hmove

theorem twoSubgroup_inf_starKernel_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (A : Subgroup (K ⊔ R : Subgroup G)) (hA : IsPGroup 2 A)
    (hQA : pCore 2 (K ⊔ R : Subgroup G) ≤ A) :
    A ⊓ starKernel K R = pCore 2 (K ⊔ R : Subgroup G) :=
  twoGroup_inf_eq_of_odd_kernel _ _ _ hA hQA
    (core_le_starKernel K R) (starKernel_core_image_coprime_of_normal_input h)

theorem radical_inf_starKernel_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    R.subgroupOf (K ⊔ R) ⊓ starKernel K R = pCore 2 (K ⊔ R : Subgroup G) := by
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  exact twoGroup_inf_eq_of_odd_kernel _ _ _ hR.comap_subtype
    (fun x hx => source_joinCore_le_radical h (mem_map_of_mem (K ⊔ R : Subgroup G).subtype hx))
    (core_le_starKernel K R) (starKernel_core_image_coprime_of_normal_input h)

theorem thompson_not_le_starKernel_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    ¬ elementaryAbelianMaxJ (R.subgroupOf (K ⊔ R)) ≤ starKernel K R := by
  intro hh
  let J := K ⊔ R
  let R₀ := R.subgroupOf J
  have hQR : pCore 2 J ≤ R₀ := fun x hx => source_joinCore_le_radical h
    (mem_map_of_mem J.subtype hx)
  have hle : elementaryAbelianMaxJ R₀ ≤ pCore 2 J := by
    rw [←radical_inf_starKernel_of_normal_input h]
    exact le_inf (sSup_le fun _ hA => hA.1) hh
  have he := elementaryAbelianMaxJ_eq_of_intermediate R₀ (pCore 2 J) hle hQR
  have hm := congrArg (map J.subtype) he
  rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
    map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)] at hm
  exact (kernel_offender_of_normal_input h).2.thompson hm.ge

end CFSG.Quasithin.ChapterC.C27Source
