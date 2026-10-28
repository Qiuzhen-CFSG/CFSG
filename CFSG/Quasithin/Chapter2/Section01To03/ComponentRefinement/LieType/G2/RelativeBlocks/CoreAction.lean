module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# External two-core action on relative blocks

Subnormality and two-perfection put [Q,B] in the actual U(B), whenever Q
is a two-group normalized by B. Thus every element of [Q,B] has square
one for a short B. This conclusion also holds after an arbitrary ambient
homomorphism: no assumption on its kernel is needed.

This is the core-image bridge for the relative-block step on printed p.526
of Aschbacher–Smith. The source conventions are C.1.7 (printed p.123) and
A.4.2(2) (printed p.57). It does not identify the block with a parabolic.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

open Subgroup ChapterC
open scoped commutatorElement

variable {K A : Type*} [Group K] [Group A] [Finite K]

/-- The entire external two-group commutator, not just its generators, has
exponent dividing two. -/
theorem subnormal_short_commutator_square (B Q : Subgroup K)
    (hs : B.IsSubnormal) (hb : IsShort B) (hq : IsPGroup 2 Q)
    (hn : B ≤ normalizer Q) {x : K} (hx : x ∈ ⁅Q, B⁆) : x ^ 2 = 1 := by
  have hc : ⁅Q, B⁆ ≤ (blockU B).map B.subtype :=
    commutator_le_core_commutator_of_isSubnormal B Q hs hb.twoPerfect hq hn
  obtain ⟨u, hu, rfl⟩ := hc hx
  have he := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    hb.elementary.exponent_dvd_p (⟨u, hu⟩ : blockU B)
  exact congrArg (fun v : blockU B => ((v : B) : K)) he

/-- A homomorphism transports the external radical obstruction even when
its kernel contains other components. -/
theorem subnormal_short_image_square (B Q : Subgroup K)
    (hs : B.IsSubnormal) (hb : IsShort B) (hq : IsPGroup 2 Q)
    (hn : B ≤ normalizer Q) (f : K →* A) {x y : A}
    (hx : x ∈ Q.map f) (hy : y ∈ B.map f) : ⁅x, y⁆ ^ 2 = 1 := by
  obtain ⟨q, hq', rfl⟩ := hx
  obtain ⟨b, hb', rfl⟩ := hy
  have he := congrArg f (subnormal_short_commutator_square B Q hs hb hq hn
    (commutator_mem_commutator hq' hb'))
  simpa only [map_pow, map_commutatorElement, map_one] using he

/-- The ambient two-core may be used without identifying O₂(B) first. -/
theorem subnormal_short_core_image_square (B : Subgroup K)
    (hs : B.IsSubnormal) (hb : IsShort B) (f : K →* A) {x y : A}
    (hx : x ∈ (pCore 2 K).map f) (hy : y ∈ B.map f) : ⁅x, y⁆ ^ 2 = 1 :=
  subnormal_short_image_square B (pCore 2 K) hs hb pCore_isPGroup
    le_normalizer_of_normal f hx hy

/-- A coordinate map may be defined only on an overgroup N of B. Its
kernel may contain other components, and N need not be normal in K. -/
theorem subnormal_short_overgroup_image_square (B N : Subgroup K)
    (hs : B.IsSubnormal) (hb : IsShort B) (hBN : B ≤ N) (f : N →* A)
    {x y : A} (hx : x ∈ (pCore 2 N).map f)
    (hy : y ∈ (B.subgroupOf N).map f) : ⁅x, y⁆ ^ 2 = 1 := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨b, hb', rfl⟩ := hy
  let Q := (pCore 2 N).map N.subtype
  have hNQ : N ≤ normalizer Q := by
    have hh := (pCore 2 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have he : (⁅(q : K), (b : K)⁆ : K) ^ 2 = 1 :=
    subnormal_short_commutator_square B Q hs hb (pCore_isPGroup.map N.subtype)
      (hBN.trans hNQ) (commutator_mem_commutator (mem_map_of_mem N.subtype hq) hb')
  have heN : (⁅q, b⁆ : N) ^ 2 = 1 := Subtype.ext he
  simpa only [map_pow, map_commutatorElement, map_one] using congrArg f heN

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

end
