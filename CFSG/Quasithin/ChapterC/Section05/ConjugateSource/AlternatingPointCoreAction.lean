module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingNormalizerAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointCentralizer
public import Theory.GroupTheory.PCoreSurjective

/-!
# The marked action of the actual alternating point core

Restrict the full normalizer action to the literal point stabilizer.
Its kernel is a two-group, so lifting the two-core of A₄ identifies
the action image of the actual point-centralizer two-core. This retains
the original action marking, needed when combining two commuting blocks.

Source: Aschbacher–Smith, proof of 14.6.9(l), printed p.1027.
-/

public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open AlternatingFiveBorel
variable {G : Type*} [Group G] [Finite G] {R K L C : Subgroup G}

/-- Every element of the marked Klein four has a lift in the literal point core. -/
theorem AlternatingPairSetup.point_core_action_lift
    (h : AlternatingPairSetup R K L)
    (hmark : ∀ k : K, (k : G) ∈ C ↔
      h.action (Subgroup.inclusion le_sup_left k) 4 = 4)
    (q : normalizer (K : Set G) →* FivePerm)
    (hcompat : ∀ s : (K ⊔ ChapterB.baumann R : Subgroup G),
      q (Subgroup.inclusion (sup_le K.le_normalizer h.normalizes) s) = h.action s)
    (a : B) (ha : a ∈ pCore 2 B) :
    ∃ k : (K ⊓ C).pCoreIn 2,
      q ⟨k,K.le_normalizer ((pCoreIn_le 2 (K ⊓ C) k.property).1)⟩ = a.val.val := by
  let Y := K ⊓ C
  let f : Y →* B :=
    { toFun := fun y => ⟨⟨h.action (Subgroup.inclusion (show K ≤ K ⊔ ChapterB.baumann R from le_sup_left) ⟨(y:G),y.property.1⟩),by
        rw [←h.block_image]
        exact mem_map_of_mem h.action y.property.1⟩,
        (hmark ⟨y,y.property.1⟩).mp y.property.2⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact h.action.map_one
      map_mul' := fun x y => by
        apply Subtype.ext; apply Subtype.ext
        change h.action ((Subgroup.inclusion (show K ≤ K ⊔ ChapterB.baumann R from le_sup_left) ⟨(x:G),x.property.1⟩) *
          (Subgroup.inclusion (show K ≤ K ⊔ ChapterB.baumann R from le_sup_left) ⟨(y:G),y.property.1⟩)) = _
        exact h.action.map_mul _ _ }
  have hf : Function.Surjective f := by
    intro b
    have hb : b.val.val ∈ (K.subgroupOf (K ⊔ ChapterB.baumann R)).map h.action :=
      h.block_image.symm ▸ b.val.property
    obtain ⟨k,hk,he⟩ := hb
    have hkc : (k : G) ∈ C := (hmark ⟨k,hk⟩).mpr (he ▸ b.property)
    exact ⟨⟨k,hk,hkc⟩,Subtype.ext (Subtype.ext he)⟩
  have hk : IsPGroup 2 f.ker := by
    let g : Y →* K := Subgroup.inclusion inf_le_left
    have hle : f.ker ≤ (pCore 2 K).comap g := by
      intro y hy
      rw [←h.block.2.1.centralizer_blockU]
      intro u hu
      have hzero : h.action (Subgroup.inclusion le_sup_left (g y)) = 1 :=
        congrArg (fun b : B => b.val.val) hy
      have hc : (Subgroup.inclusion le_sup_left (g y)) ∈ h.action.ker := hzero
      rw [h.action_kernel] at hc
      exact Subtype.ext (hc u (mem_map_of_mem K.subtype hu))
    exact (pCore_isPGroup.comap_of_injective g (Subgroup.inclusion_injective inf_le_left)).to_le hle
  have hcore := f.comap_pCore_of_ker_isPGroup hf hk
  obtain ⟨y,hy⟩ := hf a
  have hycore : y ∈ pCore 2 Y := hcore ▸ (show y ∈ (pCore 2 B).comap f from (show f y ∈ pCore 2 B from hy.symm ▸ ha))
  refine ⟨⟨y,mem_map_of_mem Y.subtype hycore⟩,?_⟩
  exact (hcompat (Subgroup.inclusion (show K ≤ K ⊔ ChapterB.baumann R from le_sup_left) ⟨(y:G),y.property.1⟩)).trans
    (congrArg (fun b : B => b.val.val) hy)

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
