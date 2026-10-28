module

public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.LocalNormalization
public import Theory.Representation.BinaryOffender.KernelQuotient
public import Theory.Representation.BinaryOffender.Restriction
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

public import Theory.GroupTheory.GeneralizedFitting.ComponentImageNormalizer

/-!
# Best offenders normalize components: source B.1.5(4)

Induct on the dimension of the faithful binary module. For a minimal moving
best offender, restrict to the displacement space of the actual component
orbit. Perfectness ensures that the component survives there. Restriction
preserves the best offender, and the faithful kernel quotient stays in the
original actor universe. Induction normalizes its component image, and
component calculus reflects normalization. Thus the moved space is the whole
module, where the proved replacement contradiction finishes the argument.

All quadratic models, natural sections, normalizer rank bounds and odd
commutators used in that contradiction are constructed by the imported source
proofs. No local classification or moved-space premise remains.

Source: Aschbacher--Smith, B.1.5(4), printed p.69; GLS volume 2,
Theorem 26.24, Step 1 and its subsequent replacement argument.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentNormalization
universe u v

private theorem normalization_by_dimension (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G]
      (V : Type v) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (ρ : Representation (ZMod 2) G V), Function.Injective ρ →
      Module.finrank (ZMod 2) V = n →
      ∀ A L : Subgroup G, IsBestOffender ρ A → IsComponent G L →
      A ≤ normalizer (L : Set G) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ V _ _ _ ρ hf hdim A₀ L₀ hA₀ hL₀
    by_contra hAN₀
    obtain ⟨A,L,hA,hL,hAN,hmin⟩ := exists_minimal_component_counterexample ρ
      ⟨A₀,L₀,hA₀,hL₀,hAN₀⟩
    let E := componentOrbit L A
    let W := subspaceCommutator ρ ⊤ E
    by_cases hW : W = ⊤
    · apply hAN
      apply ReplacementSource.normalizes_of_moved_space ρ hf hA hL hmin
      rw [← hW]
      unfold W subspaceCommutator
      congr 1
      ext v
      constructor
      · rintro ⟨⟨e,w⟩,rfl⟩
        exact ⟨e,e.property,w,Submodule.mem_top,rfl⟩
      · rintro ⟨e,he,w,_,rfl⟩
        exact ⟨(⟨e,he⟩,w),rfl⟩
    have htop (D : Subgroup G) : D ≤ subspaceStabilizer ρ (⊤ : Submodule (ZMod 2) V) :=
      le_subspaceStabilizer ρ ⊤ (by simp)
    have hAW : A ≤ subspaceStabilizer ρ W :=
      subspaceCommutator_invariant_normalizer ρ (htop A) (le_normalizer_componentOrbit L A)
    have hLW : L ≤ subspaceStabilizer ρ W :=
      subspaceCommutator_invariant_normalizer ρ (htop L)
        ((le_componentOrbit L A).trans E.le_normalizer)
    let S := subspaceStabilizer ρ W
    let σ := stabilizerRepresentation ρ W
    let π := KernelQuotient.projection σ
    let Ls := L.subgroupOf S
    let As := A.subgroupOf S
    have hLs : IsComponent S Ls := hL.subgroupOf hLW
    have hLne : Ls.map π ≠ ⊥ := by
      intro he
      let := hL.2
      have hfix : W ≤ fixedSpace ρ L := by
        intro w hw l
        have hp : π ⟨l,hLW l.property⟩ = 1 :=
          (map_eq_bot_iff Ls).mp he l.property
        have hh := congrArg (fun x => KernelQuotient.action σ x ⟨w,hw⟩) hp
        change KernelQuotient.action σ (KernelQuotient.projection σ ⟨l,hLW l.property⟩)
          ⟨w,hw⟩ = KernelQuotient.action σ 1 ⟨w,hw⟩ at hh
        rw [KernelQuotient.action_projection, map_one] at hh
        exact congrArg (fun x : W => (x:V)) hh
      have hdisp : subspaceCommutator ρ ⊤ L ≤ W := by
        apply Submodule.span_mono
        rintro v ⟨l,hl,w,hw,he⟩
        exact ⟨l,le_componentOrbit L A hl,w,hw,he⟩
      have htriv := le_fixedSpace_of_commutator_le_fixedSpace ρ L ⊤ (htop L)
        (hdisp.trans hfix)
      have hbot : L = ⊥ := by
        apply bot_unique
        intro l hl
        apply hf
        ext v
        simpa only [MonoidHom.comp_apply, Subgroup.coe_mk, Subgroup.subtype_apply, map_one,Module.End.one_apply] using htriv (x := v) Submodule.mem_top ⟨l,hl⟩
      let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
      let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
      exact (nontrivial_iff_ne_bot L).mp inferInstance hbot
    have hLq : IsComponent (KernelQuotient.Actor σ) (Ls.map π) :=
      (hLs.map_surjective π (KernelQuotient.projection_surjective σ)).resolve_left hLne
    have hreflect {a : G} (ha : a ∈ A)
        (han : π ⟨a,hAW ha⟩ ∈ normalizer (Ls.map π : Set (KernelQuotient.Actor σ))) :
        a ∈ normalizer (L : Set G) := by
      have hnorm := hLs.mem_normalizer_of_mem_normalizer_map π hLne han
      have hm := Ls.le_normalizer_map S.subtype (mem_map_of_mem S.subtype hnorm)
      change a ∈ normalizer ((L.subgroupOf S).map S.subtype : Set G) at hm
      rw [map_subgroupOf_eq_of_le hLW] at hm
      exact hm
    have hnotfix : ¬ W ≤ fixedSpace ρ A := by
      intro hfix
      apply hAN
      intro a ha
      apply hreflect ha
      have hp : π ⟨a,hAW ha⟩ = 1 := by
        apply (KernelQuotient.faithful σ)
        change KernelQuotient.action σ (KernelQuotient.projection σ ⟨a,hAW ha⟩) =
          KernelQuotient.action σ 1
        rw [KernelQuotient.action_projection,map_one]
        ext w
        exact hfix w.property ⟨a,ha⟩
      rw [hp]
      exact (normalizer (Ls.map π : Set (KernelQuotient.Actor σ))).one_mem
    have hAbest := hA.restricted ρ W hAW hnotfix
    have hAq : IsBestOffender (KernelQuotient.action σ) (As.map π) := by
      have hh := KernelQuotient.bestOffender_transport σ hAbest
      change IsBestOffender (KernelQuotient.action σ)
        ((actionSubgroup σ As).map (KernelQuotient.equiv σ).symm.toMonoidHom) at hh
      rwa [KernelQuotient.actionSubgroup_transport] at hh
    have hdlt : Module.finrank (ZMod 2) W < n := by
      rw [← hdim]
      exact Submodule.finrank_lt hW
    have hind := ih (Module.finrank (ZMod 2) W) hdlt
      (KernelQuotient.Actor σ) W (KernelQuotient.action σ)
      (KernelQuotient.faithful σ) rfl (As.map π) (Ls.map π) hAq hLq
    apply hAN
    intro a ha
    exact hreflect ha (hind (mem_map_of_mem π ha))

end CFSG.Quasithin.ChapterB.ComponentNormalization

namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- B.1.5(4): each best offender on the original faithful finite binary
module normalizes every actual subnormal quasisimple component. -/
theorem source_lemma_B_1_5_4 (hf : Function.Injective ρ)
    {A L : Subgroup G} (hA : IsBestOffender ρ A) (hL : IsComponent G L) :
    A ≤ normalizer (L : Set G) :=
  ComponentNormalization.normalization_by_dimension (Module.finrank (ZMod 2) V)
    G V ρ hf rfl A L hA hL

/-- The subgroup generated by all best offenders normalizes each component. -/
theorem offenderSubgroup_le_normalizer_component (hf : Function.Injective ρ)
    {L : Subgroup G} (hL : IsComponent G L) :
    offenderSubgroup ρ ≤ normalizer (L : Set G) :=
  (offenderSubgroup_le_iff ρ _).mpr fun _ hA => source_lemma_B_1_5_4 ρ hf hA hL
end CFSG.Quasithin.ChapterB
