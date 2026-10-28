module

public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Kernels of commuting finite-group actions

Two normal generating subgroups whose action images commute have a direct
product image if one image is centerless. If each restricted kernel is the
two-core, the full kernel is the product of these two-cores and is the
ambient two-core. The product equivalence uses multiplication of the actual
images, so it preserves both factors' actions.

The kernel calculation splits an element into the two normal factors;
disjointness forces each factor into its own kernel. The resulting image
has trivial two-core by the direct-product formula.

Source application: Aschbacher–Smith, Proposition 8.2.8(4), printed p.718,
in `CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Kernel`.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Commuting action images are disjoint when the second is centerless. -/
theorem action_images_disjoint (f : G →* H) (R I : Subgroup G)
    (hc : ⁅R, I⁆ ≤ f.ker) (hz : center (I.map f) = ⊥) :
    Disjoint (R.map f) (I.map f) := by
  have hcomm : R.map f ≤ centralizer (I.map f : Set H) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr hc
  apply disjoint_def.mpr
  intro x hxR hxI
  have hcen : (⟨x, hxI⟩ : I.map f) ∈ center (I.map f) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hcomm hxR y y.property)
  rw [hz] at hcen
  exact congrArg Subtype.val hcen

/-- Disjoint factor images split the full kernel into its two intersections. -/
theorem action_kernel_product (f : G →* H) (R I : Subgroup G) [R.Normal]
    (hgen : R ⊔ I = ⊤) (hd : Disjoint (R.map f) (I.map f)) :
    f.ker = (R ⊓ f.ker) ⊔ (I ⊓ f.ker) := by
  apply le_antisymm ?_ (sup_le inf_le_right inf_le_right)
  intro x hx
  obtain ⟨r, hr, i, hi, rfl⟩ := mem_sup_of_normal_left.mp
    (show x ∈ R ⊔ I by rw [hgen]; exact mem_top _)
  have hmul : f r * f i = 1 := by rw [← map_mul]; exact hx
  have hiR : f i ∈ R.map f := by
    rw [← inv_eq_iff_mul_eq_one.mpr hmul]
    exact (R.map f).inv_mem (mem_map_of_mem _ hr)
  have hi0 : f i = 1 := disjoint_def.mp hd hiR (mem_map_of_mem _ hi)
  have hr0 : f r = 1 := by simpa only [hi0, mul_one] using hmul
  exact mul_mem_sup ⟨hr, hr0⟩ ⟨hi, hi0⟩

/-- Restricted two-core kernels give the full two-core and an actual direct-product image. -/
theorem action_core_product [Finite G] [Finite H]
    (f : G →* H) (R I : Subgroup G) [R.Normal] [I.Normal]
    (hgen : R ⊔ I = ⊤) (hc : ⁅R, I⁆ ≤ f.ker)
    (hz : center (I.map f) = ⊥)
    (hR : (f.comp R.subtype).ker = pCore 2 R)
    (hI : (f.comp I.subtype).ker = pCore 2 I) :
    pCore 2 G = f.ker ∧ f.ker = R.pCoreIn 2 ⊔ I.pCoreIn 2 ∧
      ∃ e : R.map f × I.map f ≃* f.range,
        ∀ r i, (e (r, i) : H) = (r : H) * (i : H) := by
  have hd := action_images_disjoint f R I hc hz
  have heR : R ⊓ f.ker = R.pCoreIn 2 := by
    have he := congrArg (Subgroup.map R.subtype) hR
    change (f.ker.subgroupOf R).map R.subtype = _ at he
    simpa only [pCoreIn, subgroupOf_map_subtype, inf_comm] using he
  have heI : I ⊓ f.ker = I.pCoreIn 2 := by
    have he := congrArg (Subgroup.map I.subtype) hI
    change (f.ker.subgroupOf I).map I.subtype = _ at he
    simpa only [pCoreIn, subgroupOf_map_subtype, inf_comm] using he
  have hk : f.ker = R.pCoreIn 2 ⊔ I.pCoreIn 2 := by
    rw [action_kernel_product f R I hgen hd, heR, heI]
  have hcomm : R.map f ≤ centralizer (I.map f : Set H) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr hc
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (R.map f) (I.map f) hd hcomm
  have hsup : R.map f ⊔ I.map f = f.range := by
    rw [← map_sup, hgen, ← MonoidHom.range_eq_map]
  let e' := e.trans (MulEquiv.subgroupCongr hsup)
  have hcr : pCore 2 (R.map f) = ⊥ := by
    let er := MulEquiv.subgroupCongr (show (f.comp R.subtype).range = R.map f by
      rw [MonoidHom.range_comp, range_subtype])
    have hh := pCore_map_iso 2 er
    rw [pCore_range_eq_bot_of_ker_eq_pCore 2 _ hR, map_bot] at hh
    exact hh.symm
  have hci : pCore 2 (I.map f) = ⊥ := by
    let ei := MulEquiv.subgroupCongr (show (f.comp I.subtype).range = I.map f by
      rw [MonoidHom.range_comp, range_subtype])
    have hh := pCore_map_iso 2 ei
    rw [pCore_range_eq_bot_of_ker_eq_pCore 2 _ hI, map_bot] at hh
    exact hh.symm
  have hcf : pCore 2 f.range = ⊥ := by
    have hh := pCore_map_iso 2 e'
    rw [pCore_prod, hcr, hci, bot_prod_bot, map_bot] at hh
    exact hh.symm
  have hkp : IsPGroup 2 f.ker := by
    let : (R.pCoreIn 2).Normal := by unfold pCoreIn; infer_instance
    rw [hk]
    exact (isPGroup_pCoreIn 2 R).to_sup_of_normal_left (isPGroup_pCoreIn 2 I)
  have hcore := f.rangeRestrict.comap_pCore_of_ker_isPGroup (p := 2)
    f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hkp)
  rw [hcf, MonoidHom.comap_bot, MonoidHom.ker_rangeRestrict] at hcore
  exact ⟨hcore.symm, hk, e', he⟩
end Subgroup
