module

public import Mathlib.GroupTheory.Sylow

/-!
# Localizing subgroup images in a Sylow group

If the image of a p-subgroup lies in the image of a chosen Sylow subgroup,
conjugation by an element of the kernel places the subgroup in that Sylow.
Conjugate first inside the preimage of the Sylow image, then cancel the image
of the conjugator using an element of the Sylow subgroup. No assumption on
the kernel, or surjectivity of the homomorphism, is needed.

Source application: the maximal elementary images in Aschbacher–Smith,
B.2.7–9 (printed pp.76–77), and Lemma 13.6.22 (printed p.932).
-/

public section
open Subgroup
open scoped Pointwise

namespace Sylow
variable {G Q : Type*} [Group G] [Finite G] [Group Q]
  {p : ℕ} [Fact p.Prime]

theorem exists_kernel_conjugate_le (R : Sylow p G) (q : G →* Q)
    (A : Subgroup G) (hA : IsPGroup p A) (hAR : A.map q ≤ (R : Subgroup G).map q) :
    ∃ g : G, q g = 1 ∧ A.map (MulAut.conj g).toMonoidHom ≤ R := by
  let U := ((R : Subgroup G).map q).comap q
  have hRU : (R : Subgroup G) ≤ U := le_comap_map q _
  have hAU : A ≤ U := map_le_iff_le_comap.mp hAR
  obtain ⟨S, hAS⟩ := (hA.comap_subtype (K := U)).exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U S (R.subtype hRU)
  have hconj : (S : Subgroup U).map (MulAut.conj u).toMonoidHom =
      (R : Subgroup G).subgroupOf U := by
    change ((u • S : Sylow p U) : Subgroup U) = _
    rw [hu, Sylow.coe_subtype]
  obtain ⟨r, hr, he⟩ := u.property
  refine ⟨r⁻¹ * u, by simp only [map_mul, map_inv, he, inv_mul_cancel], ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hmem : u.val * a * u.val⁻¹ ∈ (R : Subgroup G) := by
    have hm := hconj ▸ mem_map_of_mem (MulAut.conj u).toMonoidHom
      (hAS (show (⟨a, hAU ha⟩ : U) ∈ A.subgroupOf U from ha))
    exact hm
  change (r⁻¹ * u.val) * a * (r⁻¹ * u.val)⁻¹ ∈ (R : Subgroup G)
  convert (R : Subgroup G).mul_mem ((R : Subgroup G).mul_mem
    ((R : Subgroup G).inv_mem hr) hmem) hr using 1
  group
end Sylow

