module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreSquares
public import Theory.Frattini.SquareImage
public import Theory.Frattini.Intersection
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# Frattini centralization by a short block

Every square in the ambient two-core centralizes a subnormal short block.
Its conjugation image on that block therefore has exponent two and kills
its Frattini subgroup. The relative version retains the actual two-core
of a containing subgroup and its literal embedding in the ambient group.

OriginalCentralization/BlockIntersection applies this separately in LT
and in H; neither block is assumed subnormal in their join.
Source: Aschbacher--Smith C.1.7--8, pp.123--124, and the original pair
preceding 13.2.8(1), p.880.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The Frattini subgroup of the ambient two-core fixes the entire block. -/
theorem IsBlock.ambient_core_frattini_centralizes
    {K : Subgroup G} (hK : IsBlock K) :
    (frattini (pCore 2 G)).map (pCore 2 G).subtype ≤ centralizer (K : Set G) := by
  have hn : pCore 2 G ≤ normalizer (K : Set G) :=
    le_normalizer_of_isSubnormal_isPPerfect K (pCore 2 G)
      hK.subnormal hK.short.twoPerfect pCore_isPGroup le_normalizer_of_normal
  let a : pCore 2 G →* MulAut K := K.normalizerMonoidHom.comp (inclusion hn)
  have hs (x : pCore 2 G) : a x ^ 2 = 1 := by
    rw [←map_pow]
    ext k
    change (x : G)^2 * (k : G) * ((x : G)^2)⁻¹ = (k : G)
    rw [←hK.ambient_core_square_centralizes x x.property k k.property,
      mul_inv_cancel_right]
  have hf := frattini_le_ker_of_square_image a hs
  rintro x ⟨y,hy,rfl⟩ k hk
  have he := congrArg (fun f : MulAut K => (f ⟨k,hk⟩ : G)) (hf hy)
  change (y : G)*k*(y : G)⁻¹=k at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Keep the block subnormality relative to its original containing group. -/
theorem relative_core_frattini_centralizes
    {K H : Subgroup G} (hKH : K ≤ H) (hK : IsBlock (K.subgroupOf H)) :
    (frattini (H.pCoreIn 2)).map (H.pCoreIn 2).subtype ≤ centralizer (K : Set G) := by
  rw [pCoreIn,frattini_image_map (pCore 2 H) H.subtype H.subtype_injective]
  calc
    _ ≤ (centralizer (K.subgroupOf H : Set H)).map H.subtype :=
      map_mono hK.ambient_core_frattini_centralizes
    _ = H ⊓ centralizer (K : Set G) := by
      rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hKH]
    _ ≤ _ := inf_le_right
end CFSG.Quasithin.ChapterC
