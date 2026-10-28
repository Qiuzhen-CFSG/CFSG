module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Cyclic
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# The single-component Borel and its two distinct quotients

The source product and subnormal perfectness identify the component with
O²(X), proving normality rather than assuming it. Intersecting the product
with the maximal subgroup gives M = (M ∩ K)S.

The actual Borel is reached in two stages: first quotient by the ambient
two-core, then by the source kernel. The first map has two-group kernel;
the second has central kernel by E.2.2's center identity in X/O₂(X).
Both maps are surjective and the recognition isomorphism restricts to the
literal marked overlap. No central extension is discarded.

Source: Aschbacher--Smith, E.2.2(2), printed pp.215--216; E.6.27,
p.257; the Borel paragraph of 4.4.13, pp.623--624.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall
universe u v
variable {X : Type u} [Group X] [Finite X]

theorem SingleClauses.component_eq_residual {M K : Subgroup X} {S : Sylow 2 X}
    (hc : SingleClauses M K S) (hK : K.IsCComponent) : K = pResidual 2 X := by
  let : Group.IsPerfect K := hK.perfect
  have hp : IsPPerfect 2 K := by
    intro N hN hq
    let := hN
    have hsub : Subsingleton (K ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hq.isNilpotent
    exact eq_top_iff.mpr fun x _ =>
      (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  apply (pResidual_eq_of_subnormal_product K S hK.subnormal hp S.isPGroup' ?_).symm
  intro x
  exact Set.mem_mul.mp (hc.product ▸ Set.mem_univ x)

theorem SingleClauses.component_normal {M K : Subgroup X} {S : Sylow 2 X}
    (hc : SingleClauses M K S) (hK : K.IsCComponent) : K.Normal := by
  rw [SingleClauses.component_eq_residual hc hK]
  infer_instance

theorem SingleClauses.overlap_normal {M K : Subgroup X} {S : Sylow 2 X}
    (hc : SingleClauses M K S) (hK : K.IsCComponent) :
    ((M ⊓ K).subgroupOf M).Normal := by
  let := SingleClauses.component_normal hc hK
  have he : (M ⊓ K).subgroupOf M = K.subgroupOf M := by
    ext x
    exact and_iff_right x.property
  rw [he]
  infer_instance

omit [Finite X] in
theorem SingleClauses.maximal_product {M K : Subgroup X} {S : Sylow 2 X}
    (hc : SingleClauses M K S) (hSM : (S : Subgroup X) ≤ M) :
    (M : Set X) = (M ⊓ K : Subgroup X) * (S : Set X) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, s, hs, rfl⟩ := Set.mem_mul.mp (hc.product ▸ Set.mem_univ x)
    refine ⟨k, ⟨?_, hk⟩, s, hs, rfl⟩
    change k ∈ M
    have := M.mul_mem hx (M.inv_mem (hSM hs))
    simpa only [mul_inv_cancel_right] using this
  · rintro ⟨k, hk, s, hs, rfl⟩
    exact M.mul_mem hk.1 (hSM hs)

def actorBorelProjection (M K : Subgroup X) : (M ⊓ K : Subgroup X) →* actorImage (M ⊓ K) :=
  (QuotientGroup.mk' (pCore 2 X)).subgroupMap (M ⊓ K)

omit [Finite X] in
theorem actorBorelProjection_surjective (M K : Subgroup X) :
    Function.Surjective (actorBorelProjection M K) :=
  (QuotientGroup.mk' (pCore 2 X)).subgroupMap_surjective (M ⊓ K)

omit [Finite X] in
theorem actorBorelProjection_kernel (M K : Subgroup X) :
    IsPGroup 2 (actorBorelProjection M K).ker := by
  let f : (actorBorelProjection M K).ker →* pCore 2 X :=
    ((M ⊓ K).subtype.comp (actorBorelProjection M K).ker.subtype).codRestrict _ (by
      intro x
      apply (QuotientGroup.eq_one_iff (N := pCore 2 X) _).mp
      exact congrArg Subtype.val (show actorBorelProjection M K x.val = 1 from x.property))
  apply pCore_isPGroup.of_injective f
  intro x y h
  have he : x.val.val = y.val.val := congrArg (fun a : pCore 2 X => (a : X)) h
  exact Subtype.ext (Subtype.ext he)

def actorBorelToSource (M K : Subgroup X) (hO : pCore 2 X ≤ sourceKernel M) :
    actorImage (M ⊓ K : Subgroup X) →* sourceImage M (M ⊓ K) :=
  ((QuotientGroup.map (pCore 2 X) (sourceKernel M) (MonoidHom.id X) hO).comp
    (actorImage (M ⊓ K)).subtype).codRestrict _ (by
      rintro ⟨_, x, hx, rfl⟩
      exact mem_map_of_mem (QuotientGroup.mk' (sourceKernel M)) hx)

omit [Finite X] in
theorem actorBorelToSource_surjective (M K : Subgroup X)
    (hO : pCore 2 X ≤ sourceKernel M) :
    Function.Surjective (actorBorelToSource M K hO) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨QuotientGroup.mk' (pCore 2 X) x, mem_map_of_mem _ hx⟩, rfl⟩

omit [Finite X] in
theorem SingleClauses.actorBorelToSource_kernel {M K T : Subgroup X}
    (hc : SingleClauses M K T) (hO : pCore 2 X ≤ sourceKernel M) :
    (actorBorelToSource M K hO).ker ≤ center (actorImage (M ⊓ K)) := by
  intro z hz
  obtain ⟨x, hx, hxz⟩ := z.property
  have he : actorBorelToSource M K hO z = 1 := hz
  have hxJ : x ∈ sourceKernel M := by
    apply (QuotientGroup.eq_one_iff x).mp
    have hval := congrArg Subtype.val he
    change QuotientGroup.map (pCore 2 X) (sourceKernel M) (MonoidHom.id X) hO z.val = 1 at hval
    rw [← hxz] at hval
    exact hval
  have hcZ : (z : X ⧸ pCore 2 X) ∈ (center (actorImage K)).map (actorImage K).subtype := by
    rw [← hc.kernel_center, ← hxz]
    exact mem_map_of_mem _ hxJ
  obtain ⟨c, hc, hcz⟩ := hcZ
  apply mem_center_iff.mpr
  intro y
  have hy : y.val ∈ actorImage K :=
    map_mono (f := QuotientGroup.mk' (pCore 2 X)) inf_le_right y.property
  apply Subtype.ext
  have h := congrArg Subtype.val (mem_center_iff.mp hc ⟨y.val, hy⟩)
  change y.val * c.val = c.val * y.val at h
  change y.val * z.val = z.val * y.val
  change c.val = z.val at hcz
  rwa [hcz] at h

omit [Finite X] in
theorem SingleClauses.central_borel_lift {M K T : Subgroup X}
    (hc : SingleClauses M K T) (hO : pCore 2 X ≤ sourceKernel M)
    {A : Type v} [Group A] {B : Subgroup A} (hB : ModelBorelPair M K B) :
    ∃ q : (M ⊓ K : Subgroup X) →* actorImage (M ⊓ K),
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      ∃ r : actorImage (M ⊓ K : Subgroup X) →* B,
        Function.Surjective r ∧ r.ker ≤ center (actorImage (M ⊓ K)) := by
  obtain ⟨e, he⟩ := hB
  let b := componentBorelEquiv B e he
  let f := actorBorelToSource M K hO
  refine ⟨actorBorelProjection M K, actorBorelProjection_surjective M K,
    actorBorelProjection_kernel M K, b.toMonoidHom.comp f,
    b.surjective.comp (actorBorelToSource_surjective M K hO), ?_⟩
  intro z hz
  apply SingleClauses.actorBorelToSource_kernel hc hO
  apply b.injective
  exact (MonoidHom.mem_ker.mp hz).trans b.map_one.symm
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall
