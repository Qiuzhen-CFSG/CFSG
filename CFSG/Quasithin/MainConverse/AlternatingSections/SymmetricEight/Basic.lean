module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SmallDegrees
public import Theory.GroupTheory.MinimalSimple
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Base cases and transport for the degree-eight section calculation

Source: Aschbacher–Smith, Theorem 0.1.2(3), condition K, printed pp.4 and
482. All sections here are surjections from actual subgroups. The first
isomorphism theorem allows the target simple group to inhabit any universe,
even though `IsKGroup` itself uses the universe of its ambient group.

The sign kernel reduces symmetric groups to alternating groups. The checked
A₆ section theorem and extension by the sign image therefore handle every
permutation degree at most six. Minimal simple models contribute only prime
cyclic sections and copies of themselves. These are base cases, not an
exhaustive classification of subgroups in degrees seven and eight.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple

namespace SymmetricEight

universe u v

/-- A section can be checked in the ambient universe and then transported
to an arbitrary target universe using its actual quotient isomorphism. -/
public theorem constructed_section_of_isKGroup {G : Type u} [Group G]
    (hG : IsKGroup IsConstructedCarrier G)
    {S : Type v} [Group S] [IsSimpleGroup S]
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let : IsSimpleGroup (U ⧸ f.ker) := e.isSimpleGroup
  exact (hG (U ⧸ f.ker) inferInstance U (QuotientGroup.mk' f.ker)
    (QuotientGroup.mk'_surjective f.ker)).of_mulEquiv e.symm

/-- Injections preserve the constructed-section property across universes. -/
public theorem isKGroup_constructed_of_injective {G : Type u} {H : Type v}
    [Group G] [Group H] (hH : IsKGroup IsConstructedCarrier H)
    (f : G →* H) (hf : Function.Injective f) :
    IsKGroup IsConstructedCarrier G := by
  intro S _ hS U g hg
  let := hS
  let e := Subgroup.equivMapOfInjective U f hf
  exact constructed_section_of_isKGroup hH (U.map f)
    (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective)

/-- The sign quotient is solvable, so it introduces only prime cyclic sections. -/
public theorem symmetric_isKGroup_of_alternating (n : ℕ)
    (h : IsKGroup IsConstructedCarrier (alternatingGroup (Fin n))) :
    IsKGroup IsConstructedCarrier (Equiv.Perm (Fin n)) := by
  let e := QuotientGroup.quotientKerEquivRange (Equiv.Perm.sign (α := Fin n))
  let : Group.IsSolvable (Equiv.Perm (Fin n) ⧸ alternatingGroup (Fin n)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact IsKGroup.of_normal_quotient (alternatingGroup (Fin n)) h
    (solvable_isKGroup_constructed _)

/-- A nontrivial quotient of a simple constructed carrier is that carrier. -/
public theorem simple_quotient_constructed {G : Type u} {S : Type v}
    [Group G] [IsSimpleGroup G] [Group S] [Nontrivial S]
    (hG : IsConstructedCarrier G) (f : G →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S :=
  hG.of_mulEquiv
    (MulEquiv.ofBijective f ⟨f.injective_of_surjective_of_simple hf, hf⟩).symm

/-- Minimal simplicity discharges every proper-subgroup branch. -/
public theorem minimalSimple_isKGroup_constructed {G : Type u}
    [Group G] [Finite G] (hG : IsMinimalSimple G) (hmodel : IsConstructedCarrier G) :
    IsKGroup IsConstructedCarrier G := by
  intro S _ hS U f hf
  let := hS
  by_cases hU : U = ⊤
  · subst U
    let : IsSimpleGroup G := hG.isSimpleGroup
    let : IsSimpleGroup (⊤ : Subgroup G) := Subgroup.topEquiv.isSimpleGroup
    exact simple_quotient_constructed (hmodel.of_mulEquiv Subgroup.topEquiv) f hf
  · let := hG.solvable_of_lt U (lt_top_iff_ne_top.mpr hU)
    let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
    exact .cyclic (primeCyclic_of_solvable_simple S)

end SymmetricEight

/-- Every simple section in permutation degree at most six is constructed. -/
public theorem symmetricSmall_isKGroup_constructed (n : ℕ) (hn : n ≤ 6) :
    IsKGroup IsConstructedCarrier (Equiv.Perm (Fin n)) := by
  have h6 : IsKGroup IsConstructedCarrier (Equiv.Perm (Fin 6)) :=
    SymmetricEight.symmetric_isKGroup_of_alternating 6
      (alternatingSix_isKGroup_constructed (MulEquiv.refl _))
  exact h6.of_injective (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn))
    (Equiv.Perm.viaEmbeddingHom_injective _)

/-- The small-degree base case with an arbitrary-universe simple target. -/
public theorem symmetricSmall_simple_section_constructed (n : ℕ) (hn : n ≤ 6)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (U : Subgroup (Equiv.Perm (Fin n))) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S :=
  SymmetricEight.constructed_section_of_isKGroup
    (symmetricSmall_isKGroup_constructed n hn) U f hf

/-- Simple quotients of actual alternating carriers of degree at least five. -/
public theorem alternating_simple_quotient_constructed {G S : Type*}
    [Group G] [Group S] [Nontrivial S] (n : ℕ) (hn : 5 ≤ n)
    (e : G ≃* alternatingGroup (Fin n)) (f : G →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  let : IsSimpleGroup G := e.isSimpleGroup
  exact SymmetricEight.simple_quotient_constructed (.alternating n hn ⟨e⟩) f hf

end CFSG.Quasithin.MainConverse
