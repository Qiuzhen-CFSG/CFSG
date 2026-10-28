module

public import Theory.GroupTheory.CentralizerModulo
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# A normal section fixed by an element outside a simple quotient's kernel

Suppose a group maps onto a simple group with p-group kernel. Any normal
subgroup not contained in that kernel supplements it and therefore contains
the p-residual. Applied to the centralizer of a normal section, this shows
that a subgroup escaping the kernel and centralizing the section forces the
whole p-residual to centralize it. No abelian or splitting hypothesis on the
section is needed.

Source application: Meierfrankenfeld–Stellmacher (1993), proof of (5.9),
printed pp.921–922, with p = 2 and the literal local normal section V/Z.
-/

public section
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]

/-- A normal subgroup escaping the kernel of a simple p-group cover
contains the p-residual. -/
theorem pResidual_le_normal_of_not_le_simple_kernel (p : ℕ)
    (q : G →* S) (hq : Function.Surjective q) (hker : IsPGroup p q.ker)
    (N : Subgroup G) [N.Normal] (hN : ¬ N ≤ q.ker) :
    pResidual p G ≤ N := by
  have hmap : N.map q = ⊤ := by
    rcases (Normal.map (inferInstance : N.Normal) q hq).eq_bot_or_eq_top with h | h
    · exact False.elim (hN ((map_eq_bot_iff N).mp h))
    · exact h
  have hsup : N ⊔ q.ker = ⊤ := by
    have h := congrArg (Subgroup.comap q) hmap
    simpa only [comap_map_eq, comap_top] using h
  exact sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N q.ker hker hsup⟩

/-- If a subgroup outside the simple-quotient kernel fixes a normal section,
then the p-residual fixes that same section. -/
theorem commutator_pResidual_le_of_simple_kernel_escape (p : ℕ)
    (q : G →* S) (hq : Function.Surjective q) (hker : IsPGroup p q.ker)
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
  have hC : ¬ C ≤ q.ker := fun h => hT (hTC.trans h)
  have hres := pResidual_le_normal_of_not_le_simple_kernel p q hq hker C hC
  apply commutator_le.mpr
  intro v hv r hr
  exact (mem_centralizerModulo_iff.mp (hres hr)).2 v hv

end Subgroup
