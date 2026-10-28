module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.NormalFour.Preparation
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.NormalizerInnerAutomorphisms

/-!
# The outer index of the inner subgroup

Conjugation on the actual `L`, followed by the quotient by inner
automorphisms, has kernel exactly `R ∩ C_G(L)L`. Thus its image is a
two-subgroup of `Out(L)` of order `|R : R₀|`. An intrinsic outer-group
bound gives the required relative index bound without assuming it for `R`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 16.4.10, printed p.1193.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- The outer automorphism bound controls the index of the actual inner part. -/
theorem IntersectionSetup.innerPart_relIndex_le_two
    (h : IntersectionSetup T z L g R)
    (houter : ∀ Q : Subgroup (MulAut.Outer L), IsPGroup 2 Q → Nat.card Q ≤ 2) :
    (innerPart L R).relIndex R ≤ 2 := by
  let i : R →* normalizer (L : Set G) := inclusion (h.le_sylow.trans h.sylow_normalizes)
  let f : R →* MulAut.Outer L :=
    (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp (L.normalizerMonoidHom.comp i)
  have hker : f.ker = (innerPart L R).subgroupOf R := by
    rw [show f = (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp
      (L.normalizerMonoidHom.comp i) from rfl, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      ← comap_comap]
    rw [normalizerMonoidHom_comap_conj_range]
    ext r
    change ((r : G) ∈ L ⊔ centralizer (L : Set G)) ↔
      (r : G) ∈ R ⊓ (centralizer (L : Set G) ⊔ L)
    simp only [mem_inf, r.property, true_and, sup_comm]
  have hbound := houter f.range
    (h.sylow.isPGroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  rwa [← index_ker, hker] at hbound

end CFSG.Quasithin.Chapter16.Intersections
