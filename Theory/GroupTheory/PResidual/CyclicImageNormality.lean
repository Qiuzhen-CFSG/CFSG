module
public import Theory.GroupTheory.PResidual.CyclicConjugateImage
public import Theory.GroupTheory.CyclicSubgroupNormalizer
/-!
# Normality of relative residuals with cyclic full residual image

Suppose a two-subgroup centralizes the kernel of a homomorphism whose target
has cyclic two-residual. The two-residual of its full normal closure is faithful
and cyclic. The residual of any relative conjugate span lies in that cyclic
normal subgroup and is therefore normal in the whole ambient group.

Source application: the marked order-five row of Aschbacher--Smith15.2.3(2),
printed p.1105, applied in the literal quotient M/O₂(M).
-/
public section
open Subgroup
namespace Subgroup
theorem normal_twoResidual_conjugateSpan_of_cyclic_residual_image {G D : Type*} [Group G] [Finite G] [Group D]
    (f : G →* D) (R B : Subgroup G) (hR : IsPGroup 2 R)
    (hc : R ≤ centralizer (f.ker : Set G)) [IsCyclic (pResidual 2 D)] :
    ((pResidual 2 (conjugateSpanBy R B)).map (conjugateSpanBy R B).subtype).Normal := by
  let N := normalClosure (R : Set G)
  let E := (pResidual 2 N).map N.subtype
  have hEf : E.map f ≤ pResidual 2 D := by
    rw [show E = (pResidual 2 N).map N.subtype from rfl,map_map]
    exact map_pResidual_le 2 (f.comp N.subtype)
  let : IsCyclic (E.map f) := isCyclic_of_injective (inclusion hEf) (inclusion_injective hEf)
  have hd : Disjoint E f.ker := disjoint_twoResidual_normalClosure_ker_of_cyclic_image f R hR hc
  let : IsCyclic E := isCyclic_of_injective (f.subgroupMap E) (by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    exact disjoint_def.mp hd x.property (congrArg Subtype.val hx))
  have hNE : (⊤ : Subgroup G) ≤ normalizer (E : Set G) := le_normalizer_of_normal
  have hRE : (pResidual 2 (conjugateSpanBy R B)).map (conjugateSpanBy R B).subtype ≤ E :=
    embedded_pResidual_mono 2 (conjugateSpanBy_le (fun _ hx => le_normalClosure hx) le_normalizer_of_normal)
  apply normalizer_eq_top_iff.mp
  exact top_unique (hNE.trans (normalizer_le_normalizer_of_le_cyclic _ E hRE))

end Subgroup
