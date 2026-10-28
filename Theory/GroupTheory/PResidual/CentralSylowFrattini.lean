module

public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.Transfer

/-!
# Central kernels and Sylow generation in p-perfect groups

Transfer to the Sylow Frattini quotient kills a p-perfect group. On a
central element it is the Sylow-index power, which is invertible in a
p-group. Thus central kernels lie in the Sylow Frattini subgroup, and
quotient generators lift through a kernel which is central modulo N.

Only p-perfectness is needed; no classification of central covers is used.
In Aschbacher–Smith 15.3.59, printed pp.1149–1150 (combined manuscript,
1 March 2004), this applies to K/U. Its kernel is the image of K ∩ Q_H;
one need not put all of C_T(U) inside K.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A central subgroup of a Sylow group has Frattini image when the ambient
finite group has no nontrivial p-group quotient. -/
theorem central_subgroup_le_frattini_sylow_of_isPPerfect
    (hG : IsPPerfect p G) (S : Sylow p G) (C : Subgroup S)
    (hc : C.map (S : Subgroup G).subtype ≤ center G) : C ≤ frattini S := by
  let : Fact (IsPGroup p S) := ⟨S.isPGroup'⟩
  let F := frattini S
  let q := QuotientGroup.mk' F
  let : IsMulCommutative (S ⧸ F) :=
    Normal.quotient_commutative_iff_commutator_le.mpr
      (commutator_le_frattini_of_isPGroup (p := p))
  let transfer := MonoidHom.transfer q
  have hp : IsPGroup p (S ⧸ F) := S.isPGroup'.to_quotient F
  have ht : transfer.ker = ⊤ := hG _ inferInstance
    ((hp.of_injective transfer.range.subtype transfer.range.subtype_injective).of_equiv
      (QuotientGroup.quotientKerEquivRange transfer).symm)
  intro c hC
  have hcG : (c : G) ∈ center G := hc (mem_map_of_mem _ hC)
  have formula := MonoidHom.transfer_eq_pow q (c : G) (fun k g _ => by
    rw [mem_center_iff.mp ((center G).pow_mem hcG k) g⁻¹,
      mul_assoc, inv_mul_cancel, mul_one])
  have hpow : q c ^ S.index = 1 := by
    rw [← map_pow]
    exact formula.symm.trans (MonoidHom.mem_ker.mp (ht ▸ mem_top (c : G)))
  have he : q c = 1 := (hp.powEquiv' S.not_dvd_index).injective (by simpa using hpow)
  exact (QuotientGroup.eq_one_iff c).mp he

variable {D : Type*} [Group D]
/-- Generators of a Sylow image lift across a central kernel in a p-perfect group. -/
theorem sylow_eq_of_map_eq_of_central_kernel_of_isPPerfect
    (hG : IsPPerfect p G) (S : Sylow p G) (f : G →* D)
    (hc : f.ker ≤ center G) (A : Subgroup G) (hAS : A ≤ S)
    (hcover : (S : Subgroup G).map f ≤ A.map f) : A = S := by
  let C := f.ker.subgroupOf (S : Subgroup G)
  have hC : C ≤ frattini S :=
    central_subgroup_le_frattini_sylow_of_isPPerfect hG S C
      (by rintro _ ⟨x, hx, rfl⟩; exact hc hx)
  have hs : A.subgroupOf (S : Subgroup G) ⊔ frattini S = ⊤ := by
    apply top_unique
    intro s _
    obtain ⟨a, ha, he⟩ := hcover (mem_map_of_mem f s.property)
    have hk : (⟨a, hAS ha⟩ : S)⁻¹ * s ∈ C := by
      change f (a⁻¹ * (s : G)) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hm := mul_mem_sup (show (⟨a, hAS ha⟩ : S) ∈ A.subgroupOf (S : Subgroup G) from ha)
      (hC hk)
    simpa only [mul_inv_cancel_left] using hm
  have he := congrArg (map (S : Subgroup G).subtype) (frattini_nongenerating hs)
  simpa only [map_subgroupOf_eq_of_le hAS, ← MonoidHom.range_eq_map, range_subtype] using he


/-- If the kernel is central modulo N, a subgroup covering the Sylow image,
together with N, contains the entire Sylow subgroup. -/
theorem sylow_le_sup_of_image_cover_of_central_kernel_mod
    (hG : IsPPerfect p G) (S : Sylow p G) (f : G →* D)
    (N : Subgroup G) [N.Normal] (hN : N ≤ f.ker)
    (hc : f.ker ≤ (center (G ⧸ N)).comap (QuotientGroup.mk' N))
    (A : Subgroup G) (hAS : A ≤ S)
    (hcover : (S : Subgroup G).map f ≤ A.map f) : (S : Subgroup G) ≤ A ⊔ N := by
  let q := QuotientGroup.mk' N
  let fbar := QuotientGroup.lift N f hN
  have hcomp : fbar.comp q = f := by ext; rfl
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective N)
  have hcbar : fbar.ker ≤ center (G ⧸ N) := by
    rw [QuotientGroup.ker_lift]
    exact map_le_iff_le_comap.mpr hc
  have hcoverbar : (Sbar : Subgroup (G ⧸ N)).map fbar ≤ (A.map q).map fbar := by
    change ((S : Subgroup G).map q).map fbar ≤ _
    simpa only [map_map, hcomp] using hcover
  have he := sylow_eq_of_map_eq_of_central_kernel_of_isPPerfect
    (hG.of_surjective q (QuotientGroup.mk'_surjective N)) Sbar fbar hcbar
    (A.map q) (map_mono hAS) hcoverbar
  have hh : (S : Subgroup G).map q ≤ A.map q := he.symm.le
  have hle := (le_comap_map q (S : Subgroup G)).trans (comap_mono hh)
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk'] using hle

end Subgroup
