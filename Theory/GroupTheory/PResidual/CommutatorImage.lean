module

public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Lifting commutator generation through a prime-group kernel

Suppose K is p-perfect, W normalizes K, and f has p-group kernel.
If f(K)=[f(K),f(W)], then K=[K,W]. Indeed [K,W] is normal inside K;
the image equality makes the quotient a p-group, and p-perfectness
makes that quotient trivial. No ambient normality of W is assumed.
The specialization uses the literal map G→G/O_p(G).

Source application: Aschbacher--Smith, 14.4.7, printed p.1009, lifting
K*=[K*,W^{g*}] to the original two-residual.
-/

public section

namespace Subgroup
variable {G F : Type*} [Group G] [Group F] {p : ℕ} [Fact p.Prime]

theorem eq_commutator_of_isPPerfect_of_map_eq (K W : Subgroup G)
    (hK : IsPPerfect p K) (hWK : W ≤ normalizer (K : Set G))
    (f : G →* F) (hf : IsPGroup p f.ker)
    (himage : K.map f = ⁅K.map f, W.map f⁆) : K = ⁅K, W⁆ := by
  let C := ⁅K, W⁆
  have hCK : C ≤ K := le_normalizer_iff_commutator_le_left.mp hWK
  have him : K ≤ C ⊔ f.ker := by
    have hh : K.map f ≤ C.map f := by rw [map_commutator]; exact himage.le
    have hpre : K ≤ (C.map f).comap f :=
      (le_comap_map f K).trans (comap_mono (f := f) hh)
    simpa only [comap_map_eq] using hpre
  let _ : (C.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCK).mpr (normalizer_commutator_ge_left K W)
  have htop : (⊤ : Subgroup K) ≤ C.subgroupOf K ⊔ f.ker.subgroupOf K := by
    intro x _
    obtain ⟨c, hc, q, hq, he⟩ := mem_sup_of_normal_right.mp (him x.property)
    have hqK : q ∈ K := by
      have hqeq : q = c⁻¹ * (x : G) := by rw [← he]; group
      rw [hqeq]
      exact K.mul_mem (K.inv_mem (hCK hc)) x.property
    have hh := mul_mem_sup (show (⟨c, hCK hc⟩ : K) ∈ C.subgroupOf K from hc)
      (show (⟨q, hqK⟩ : K) ∈ f.ker.subgroupOf K from hq)
    have he' : (⟨c, hCK hc⟩ : K) * ⟨q, hqK⟩ = x := Subtype.ext he
    rwa [he'] at hh
  have hperfect : IsPPerfect p (⊤ : Subgroup K) :=
    hK.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).symm.toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).symm.surjective
  have hle := le_normal_of_isPPerfect_of_le_sup_pGroup ⊤ (C.subgroupOf K)
    (f.ker.subgroupOf K) hperfect hf.comap_subtype htop
  apply le_antisymm ?_ hCK
  intro x hx
  exact hle (mem_top (⟨x, hx⟩ : K))

variable [Finite G]
theorem pResidual_eq_commutator_of_quotient (W : Subgroup G)
    (himage : (pResidual p G).map (QuotientGroup.mk' (pCore p G)) =
      ⁅(pResidual p G).map (QuotientGroup.mk' (pCore p G)),
        W.map (QuotientGroup.mk' (pCore p G))⁆) :
    pResidual p G = ⁅pResidual p G, W⁆ := by
  apply eq_commutator_of_isPPerfect_of_map_eq (pResidual p G) W
    (isPPerfect_pResidual p) le_normalizer_of_normal
    (QuotientGroup.mk' (pCore p G)) _ himage
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup
end Subgroup
