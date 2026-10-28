module
public import Theory.GroupTheory.MinimalParabolicKernelReduction
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Centralizers supplement the core in a minimal parabolic

Let S lie in a unique maximal subgroup, with a non-two simple quotient H/K.
If V centralizes a normal subgroup N, lies in S, and is not contained in N,
the maximality test for C_S(N) forces C_H(N) to supplement K. The normal-kernel
Frattini reduction then makes it supplement O2(H). Consequently O^2(H)
centralizes N.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 7.3. The final
consumer uses a normal subgroup N of S and V in the center of O2(H). The
maximality premise is discharged for the actual automorphism-invariant kernel
by the source 7.2 construction.
-/

public section
open Subgroup
namespace Theory.GroupTheory.MinimalParabolicKernel
variable {H : Type*} [Group H] [Finite H]

theorem centralizer_supplements_core_of_not_le
    (S : Sylow 2 H) (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K))
    (N V : Subgroup H) [N.Normal]
    (hVS : V ≤ (S : Subgroup H)) (hVC : V ≤ centralizer (N : Set H))
    (hVN : ¬ V ≤ N)
    (hmax : (S : Subgroup H) ⊓ centralizer (N : Set H) ≤ pCore 2 H →
      (S : Subgroup H) ⊓ centralizer (N : Set H) ≤ N) :
    centralizer (N : Set H) ⊔ pCore 2 H = ⊤ := by
  let C := centralizer (N : Set H)
  have hnot : ¬ (S : Subgroup H) ⊓ C ≤ pCore 2 H := by
    intro h
    exact hVN ((le_inf hVS hVC).trans (hmax h))
  have hSK := (quotient_kernel_reduction S hu K hK).1
  let q := QuotientGroup.mk' K
  have hq := QuotientGroup.mk'_surjective K
  have hn := (inferInstance : C.Normal).map q hq
  have hCt : C.map q = ⊤ := by
    rcases hn.eq_bot_or_eq_top with hb | ht
    · have hCK : C ≤ K := by
        simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff C).mp hb
      exact False.elim (hnot ((inf_le_inf_left _ hCK).trans_eq hSK))
    · exact ht
  have hCKt : C ⊔ K = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hCt
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  exact (quotient_kernel_reduction S hu K hK).2.2.2.2 C hCKt

theorem residual_centralizes_of_not_le
    (S : Sylow 2 H) (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K))
    (N V : Subgroup H) [N.Normal]
    (hVS : V ≤ (S : Subgroup H)) (hVC : V ≤ centralizer (N : Set H))
    (hVN : ¬ V ≤ N)
    (hmax : (S : Subgroup H) ⊓ centralizer (N : Set H) ≤ pCore 2 H →
      (S : Subgroup H) ⊓ centralizer (N : Set H) ≤ N) :
    pResidual 2 H ≤ centralizer (N : Set H) := by
  have hsup := centralizer_supplements_core_of_not_le S hu K hK N V hVS hVC hVN hmax
  apply (pResidual_le_iff_isPGroup_quotient 2 _).mpr
  exact isPGroup_quotient_of_sup_eq_top _ (pCore 2 H) pCore_isPGroup hsup

/-- The centralizer test for a normal kernel in S and a central subgroup of O2(H). -/
theorem residual_centralizes_normal_sylow_kernel
    (S : Sylow 2 H) (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K))
    (N V : Subgroup H) [N.Normal] (hNS : N ≤ (S : Subgroup H))
    (hVQ : V ≤ pCore 2 H) (hVC : V ≤ centralizer (pCore 2 H : Set H))
    (hVN : ¬ V ≤ N)
    (hmax : (S : Subgroup H) ⊓ centralizer (N : Set H) ≤ pCore 2 H →
      (S : Subgroup H) ⊓ centralizer (N : Set H) ≤ N) :
    pResidual 2 H ≤ centralizer (N : Set H) := by
  have hNP : IsPGroup 2 N := S.isPGroup'.of_injective
    (inclusion hNS) (inclusion_injective hNS)
  have hNQ : N ≤ pCore 2 H := le_sSup ⟨inferInstance, hNP⟩
  exact residual_centralizes_of_not_le S hu K hK N V
    (hVQ.trans (pCore_isPGroup.le_sylow_of_normal S))
    (hVC.trans (centralizer_le hNQ)) hVN hmax

end Theory.GroupTheory.MinimalParabolicKernel
