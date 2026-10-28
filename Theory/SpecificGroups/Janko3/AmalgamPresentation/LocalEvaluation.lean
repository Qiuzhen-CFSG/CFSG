module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Core

/-!
# Transfer the literal twenty-two relations along compatible local maps

Each defining word is either a local relation or a product of two words
in adjacent local groups. If the model word is one, those two evaluations
are inverse elements in the actual intersection. Pointwise agreement of
local homomorphisms on that intersection therefore transfers the relation.
The finite word partition is checked for the exact Core words.
-/

public section
namespace Sporadic.Janko3.AmalgamPresentation
open Subgroup Subgroup.CosetWordCertificate

/-- The local group containing each of the six marked generators. -/
@[expose] def localIndex : Fin 6 → Fin 3
  | 0 | 1 => 0
  | 2 | 3 => 1
  | _ => 2

private theorem eval_local {M G α : Type*} [Group M] [Group G]
    (L : Subgroup M) (f : L →* G) (g : α → M) (h : α → G) (w : Word α)
    (hw : ∀ a ∈ w, ∃ x : L, (x : M) = g a.1 ∧ f x = h a.1) :
    ∃ x : L, (x : M) = eval g w ∧ f x = eval h w := by
  induction w with
  | nil => exact ⟨1,by simp,by simp⟩
  | cons a w ih =>
    obtain ⟨x,hx,hfx⟩ := hw a (by simp)
    obtain ⟨y,hy,hfy⟩ := ih (by intro b hb; exact hw b (by simp [hb]))
    cases ha : a.2
    · refine ⟨x⁻¹*y,?_,?_⟩
      · simp only [Subgroup.coe_mul,Subgroup.coe_inv,hx,hy,eval_cons,ha,Bool.false_eq_true,↓reduceIte]
      · simp only [map_mul,map_inv,hfx,hfy,eval_cons,ha,Bool.false_eq_true,↓reduceIte]
    · refine ⟨x*y,?_,?_⟩
      · simp only [Subgroup.coe_mul,hx,hy,eval_cons,ha,↓reduceIte]
      · simp only [map_mul,hfx,hfy,eval_cons,ha,↓reduceIte]

private theorem eval_two_locals {M G α : Type*} [Group M] [Group G]
    (L K : Subgroup M) (f : L →* G) (k : K →* G)
    (g : α → M) (h : α → G) (u v : Word α)
    (hu : ∀ a ∈ u, ∃ x : L, (x : M) = g a.1 ∧ f x = h a.1)
    (hv : ∀ a ∈ v, ∃ x : K, (x : M) = g a.1 ∧ k x = h a.1)
    (hc : ∀ (x : M) (hx : x ∈ L) (hy : x ∈ K), f ⟨x,hx⟩ = k ⟨x,hy⟩)
    (he : eval g (u ++ v) = 1) : eval h (u ++ v) = 1 := by
  obtain ⟨x,hx,hfx⟩ := eval_local L f g h u hu
  obtain ⟨y,hy,hky⟩ := eval_local K k g h v hv
  have hxy : (x : M) * (y : M) = 1 := by rwa [eval_append,←hx,←hy] at he
  have hxe : (x : M) = (y : M)⁻¹ := eq_inv_of_mul_eq_one_left hxy
  have hxK : (x : M) ∈ K := hxe ▸ K.inv_mem y.property
  have hf : f x = k y⁻¹ := by
    rw [hc x x.property hxK]
    apply congrArg k
    exact Subtype.ext hxe
  rw [eval_append,←hfx,←hky,hf,map_inv,inv_mul_cancel]

private def relatorCut : Fin 22 → Nat
  | 16 => 3
  | 17 => 12
  | 18 => 11
  | 19 => 11
  | 20 => 12
  | 21 => 12
  | i => (relatorWord i).length

private def relatorLeft : Fin 22 → Fin 3
  | 0 | 1 | 2 | 3 | 4 | 5 | 16 | 17 | 18 | 19 => 0
  | 6 | 7 | 8 | 9 | 10 | 20 | 21 => 1
  | _ => 2

private def relatorRight : Fin 22 → Fin 3
  | 16 | 17 => 1
  | 18 | 19 | 20 | 21 => 2
  | i => relatorLeft i

private theorem relator_local_partition : ∀ i : Fin 22,
    (∀ a ∈ (relatorWord i).take (relatorCut i), localIndex a.1 = relatorLeft i) ∧
    (∀ a ∈ (relatorWord i).drop (relatorCut i), localIndex a.1 = relatorRight i) := by
  decide +kernel

/-- Compatible maps from the actual three local subgroups transport every
one of the literal twenty-two relations to the resulting six-tuple. -/
theorem satisfies_of_compatible_local_maps {M G : Type*} [Group M] [Group G]
    (L : Fin 3 → Subgroup M) (g : Fin 6 → M)
    (hg : ∀ i, g i ∈ L (localIndex i)) (hs : Satisfies g)
    (f : ∀ i, L i →* G)
    (hc : ∀ i j (x : M) (hi : x ∈ L i) (hj : x ∈ L j),
      f i ⟨x,hi⟩ = f j ⟨x,hj⟩) :
    Satisfies (fun i => f (localIndex i) ⟨g i,hg i⟩) := by
  intro i
  let h := fun i => f (localIndex i) ⟨g i,hg i⟩
  have hword (j : Fin 3) (a : Fin 6 × Bool) (ha : localIndex a.1 = j) :
      ∃ x : L j, (x : M) = g a.1 ∧ f j x = h a.1 := by
    subst j
    exact ⟨⟨g a.1,hg a.1⟩,rfl,rfl⟩
  have hp := relator_local_partition i
  have he := eval_two_locals (L (relatorLeft i)) (L (relatorRight i))
    (f (relatorLeft i)) (f (relatorRight i)) g h
    ((relatorWord i).take (relatorCut i)) ((relatorWord i).drop (relatorCut i))
    (fun a ha => hword _ a (hp.1 a ha)) (fun a ha => hword _ a (hp.2 a ha))
    (hc _ _) (by simpa only [List.take_append_drop] using hs i)
  simpa only [List.take_append_drop] using he

/-- Local generation and generation by the actual local images give
surjectivity of the same evaluation of the literal presentation. -/
theorem evaluation_surjective_of_compatible_local_maps
    {M G : Type*} [Group M] [Group G]
    (L : Fin 3 → Subgroup M) (g : Fin 6 → M)
    (hg : ∀ i, g i ∈ L (localIndex i)) (hs : Satisfies g)
    (f : ∀ i, L i →* G)
    (hc : ∀ i j (x : M) (hi : x ∈ L i) (hj : x ∈ L j),
      f i ⟨x,hi⟩ = f j ⟨x,hj⟩)
    (hlocal : ∀ k, closure {x : L k | ∃ i, (x : M) = g i ∧ localIndex i = k} = ⊤)
    (hgen : (⨆ k, (f k).range) = ⊤) :
    Function.Surjective
      (evaluation (satisfies_of_compatible_local_maps L g hg hs f hc)) := by
  apply evaluation_surjective
  let h := fun i => f (localIndex i) ⟨g i,hg i⟩
  let H := closure (Set.range h)
  change H = ⊤
  apply top_unique
  rw [←hgen]
  apply iSup_le
  intro k
  rintro _ ⟨x,rfl⟩
  have hx : x ∈ closure {x : L k | ∃ i, (x : M) = g i ∧ localIndex i = k} := by
    rw [hlocal]
    exact mem_top x
  induction hx using closure_induction with
  | mem x hx =>
    obtain ⟨i,he,hi⟩ := hx
    subst k
    have hx : x = ⟨g i,hg i⟩ := Subtype.ext he
    rw [hx]
    exact subset_closure ⟨i,rfl⟩
  | one => simpa only [map_one] using H.one_mem
  | mul x y _ _ hx hy => simpa only [map_mul] using H.mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using H.inv_mem hx

end Sporadic.Janko3.AmalgamPresentation
