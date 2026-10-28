module

public import Theory.GroupTheory.NormalSectionTwoResidual
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Normal sections below a faithful simple residual image

Let q map a finite group G onto J with p-group kernel. Suppose the image
of O^p(G) is simple and has trivial centralizer in J. Every normal subgroup
of G escaping the kernel contains O^p(G): its nontrivial normal image
contains the simple subgroup, and p-perfectness removes the remaining
p-group kernel. The same argument applies to the kernel of the action on
a normal section.

This retains the actual quotient J, including its outer automorphisms.
Source application: Meierfrankenfeld–Stellmacher (1993), final action step
of (5.9), printed p.922, before removing the outer part of the local group.
-/

public section
namespace Subgroup
variable {G J : Type*} [Group G] [Finite G] [Group J]

/-- A normal subgroup outside the kernel contains the residual when its
image is simple with trivial centralizer in the whole quotient. -/
theorem pResidual_le_normal_of_not_le_monolithic_kernel
    (p : ℕ) [Fact p.Prime] (q : G →* J) (hq : Function.Surjective q)
    (hker : IsPGroup p q.ker) [IsSimpleGroup ((pResidual p G).map q)]
    (hC : centralizer ((pResidual p G).map q : Set J) = ⊥)
    (N : Subgroup G) [N.Normal] (hN : ¬ N ≤ q.ker) :
    pResidual p G ≤ N := by
  let S := (pResidual p G).map q
  let K := N.map q
  let : S.Normal := Normal.map inferInstance q hq
  let : K.Normal := Normal.map inferInstance q hq
  have hK : K ≠ ⊥ := fun h => hN ((map_eq_bot_iff N).mp h)
  have hSK : S ≤ K := by
    rcases (inferInstance : (K.subgroupOf S).Normal).eq_bot_or_eq_top with hz | ht
    · have hd := subgroupOf_eq_bot.mp hz
      have hcomm : ⁅K,S⁆ = ⊥ :=
        bot_unique ((commutator_le_inf K S).trans (hd inf_le_left inf_le_right))
      have hc : K ≤ centralizer (S : Set J) :=
        commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact False.elim (hK (le_bot_iff.mp (hc.trans hC.le)))
    · exact subgroupOf_eq_top.mp ht
  have hcover : pResidual p G ≤ N ⊔ q.ker := by
    have h := (le_comap_map q (pResidual p G)).trans (comap_mono hSK)
    simpa only [K, comap_map_eq] using h
  exact le_normal_of_isPPerfect_of_le_sup_pGroup (pResidual p G) N q.ker
    (isPPerfect_pResidual p) hker hcover

/-- An actor outside the kernel fixing a normal section forces the whole
residual to fix it, even when the quotient has an outer part. -/
theorem commutator_pResidual_le_of_monolithic_kernel_escape
    (p : ℕ) [Fact p.Prime] (q : G →* J) (hq : Function.Surjective q)
    (hker : IsPGroup p q.ker) [IsSimpleGroup ((pResidual p G).map q)]
    (hC : centralizer ((pResidual p G).map q : Set J) = ⊥)
    (V Z T : Subgroup G) [V.Normal] [Z.Normal]
    (hT : ¬ T ≤ q.ker) (hcomm : ⁅V,T⁆ ≤ Z) :
    ⁅V,pResidual p G⁆ ≤ Z := by
  let C := centralizerModulo ⊤ V Z
  let : (V.map (QuotientGroup.mk' Z)).Normal :=
    Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  let : C.Normal := by dsimp only [C, centralizerModulo]; infer_instance
  have hTC : T ≤ C := by
    intro t ht
    exact mem_centralizerModulo_iff.mpr
      ⟨mem_top _, fun v hv => hcomm (commutator_mem_commutator hv ht)⟩
  have hescape : ¬ C ≤ q.ker := fun h => hT (hTC.trans h)
  have hres := pResidual_le_normal_of_not_le_monolithic_kernel p q hq hker hC C hescape
  apply commutator_le.mpr
  intro v hv r hr
  exact (mem_centralizerModulo_iff.mp (hres hr)).2 v hv

end Subgroup
