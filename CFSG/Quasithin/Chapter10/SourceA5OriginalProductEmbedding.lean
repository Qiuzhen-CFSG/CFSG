module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter10.SourceA5ActionKernel
/-!
# The original A₅ pair inside the faithful full actor

The restriction of the full actor projection to the literal orbit L₀ has
kernel O₂(L₀). The upper containment uses the original action-kernel theorem;
the lower containment uses reducedness of the full module in its normalizer.
The marked product projection therefore induces an injective homomorphism
A₅ × A₅ into the full actor quotient, with normal image and the exact
commuting quotient diagram.

Source: Aschbacher–Smith D.3.6–7 and 10.1.1, pp. 196–199 and 741.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original full actor restricted to L₀ has precisely its two-core as kernel. -/
theorem source_a5_original_actor_restriction_ker (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    ((QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))).comp
      (inclusion (localOrbit T L).le_normalizer)).ker = pCore 2 (localOrbit T L) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let H := localJoin T L
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let qM := QuotientGroup.mk' (centralizer (U : Set M))
  let f := qM.comp (inclusion R.le_normalizer)
  change f.ker = pCore 2 R
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans R.le_normalizer
  apply le_antisymm
  · have hCH := source_a5_full_module_local_kernel_isTwoGroup D e hn
    have hp := hCH.comap_of_injective (inclusion (show R ≤ H from le_sup_left))
      (inclusion_injective _)
    have hk : f.ker ≤ (centralizer (D.fullModule.subgroupOf H : Set H)).comap
        (inclusion (show R ≤ H from le_sup_left)) := by
      intro x hx v hv
      have hxC : (inclusion R.le_normalizer x : M) ∈ centralizer (U : Set M) :=
        (QuotientGroup.eq_one_iff _).mp hx
      have hxm := hxC ⟨v, hVM hv⟩ hv
      exact Subtype.ext (congrArg (fun z : M => (z : G)) hxm)
    exact le_sSup ⟨inferInstance,hp.to_le hk⟩
  · intro x hx
    have hc : R.pCoreIn 2 ≤ M.pCoreIn 2 :=
      pCoreIn_mono_of_normalizes R.le_normalizer le_rfl
    obtain ⟨z,hz,hzx⟩ := hc (mem_map_of_mem R.subtype hx)
    have hz' : z = inclusion R.le_normalizer x := Subtype.ext hzx
    have hm : inclusion R.le_normalizer x ∈ pCore 2 M := hz' ▸ hz
    exact (QuotientGroup.eq_one_iff _).mpr
      ((le_centralizer_iff.mp (source_full_module_reduced D).le_centralizer_pCore) hm)

/-- The marked A₅ pair embeds normally in the original faithful actor quotient. -/
theorem source_a5_original_product_embedding
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    ∃ i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
        (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)),
      Function.Injective i ∧ i.range.Normal ∧
        ∀ x : localOrbit T L,
          i (originalA5ProductProjection D e hn ht htn x) =
            QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
              (inclusion (localOrbit T L).le_normalizer x) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let qM := QuotientGroup.mk' (centralizer (U : Set M))
  let f := qM.comp (inclusion R.le_normalizer)
  let q := originalA5ProductProjection D e hn ht htn
  have hq := originalA5ProductProjection_surjective D e hn ht htn
  have hk : q.ker = f.ker :=
    (originalA5ProductProjection_ker D e hn ht htn).trans
      (source_a5_original_actor_restriction_ker D e hn).symm
  let i := q.liftOfSurjective hq ⟨f, hk.le⟩
  have hi (x : R) : i (q x) = f x :=
    q.liftOfRightInverse_comp_apply _ _ _ x
  refine ⟨i, ?_, ?_, hi⟩
  · apply (MonoidHom.ker_eq_bot_iff i).mp
    apply le_bot_iff.mp
    intro a ha
    obtain ⟨x, rfl⟩ := hq a
    have hx : x ∈ f.ker := (hi x).symm.trans ha
    have hxq : x ∈ q.ker := hk.symm ▸ hx
    exact hxq
  · have hf : f.range = (R.subgroupOf M).map qM := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨inclusion R.le_normalizer x, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    have hir : i.range = f.range := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        obtain ⟨x, rfl⟩ := hq a
        exact ⟨x, (hi x).symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨q x, hi x⟩
    rw [hir, hf]
    exact (normal_subgroupOf_of_le_normalizer (show M ≤ normalizer (R : Set G)
      from le_rfl)).map qM (QuotientGroup.mk'_surjective _)
end CFSG.Quasithin.Chapter10
