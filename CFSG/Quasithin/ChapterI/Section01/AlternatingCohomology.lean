module

public import Theory.Representation.CentralFixedPointCohomology
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.Representation.BinaryAlternatingSevenCohomology
public import Theory.GroupTheory.Covering
public import Mathlib.GroupTheory.Perm.Fin

/-!
# I.1.6(1), (8), (9): alternating-group first cohomology

The natural module is exactly the image of the augmentation kernel in the
binary permutation module modulo constants, as defined in §B.3. Its first
cohomology has dimension zero in degrees five and seven, and one in degrees
six and eight. The degree-five module is projective over the group algebra.
The odd-degree proof chooses a principal vector in the augmentation kernel;
the even-degree proof normalizes cocycles on a point stabilizer. A relative
trace equal to the identity proves projectivity.

For every four-dimensional irreducible binary A₇-module, commuting three-cycles
with generating centralizers kill first cohomology. In Notation A.3.5, `Â₆`
means the quasisimple group with center of order three and central quotient A₆.
A faithful irreducible module for it has no fixed vectors under a nontrivial
central element, which kills first cohomology in every finite dimension.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(1), (8), (9), printed p.408/PDF p.419,
citing Exercise 6.3 of Aschbacher, *Finite Group Theory* [Asc86a]. The natural
module convention is §B.3, printed pp.83--84/PDF pp.94--95, especially B.3.3(1).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI

open Theory.GroupTheory
open Representation Representation.OneCohomology BinaryPermutation

/-- I.1.6(1): the cohomology dimensions of the actual natural alternating
modules in degrees five through eight. This is also the cohomology assertion
of B.3.3(1). -/
theorem alternatingNatural_firstCohomology_finrank
    (n : ℕ) (hmin : 5 ≤ n) (hmax : n ≤ 8) :
    Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation (Fin n))) =
      if Even n then 1 else 0 := by
  interval_cases n <;>
    norm_num [alternatingFive_natural_finrank_H1, alternatingSix_natural_finrank_H1,
      alternatingSeven_natural_finrank_H1, alternatingEight_natural_finrank_H1]

/-- I.1.6(1) for any group and module identified equivariantly with the natural
alternating action. Both the group and vector-space identifications are retained. -/
theorem alternatingNatural_firstCohomology_finrank_of_equiv
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (n : ℕ) (hmin : 5 ≤ n) (hmax : n ≤ 8)
    (eG : G ≃* alternatingGroup (Fin n))
    (eV : V ≃ₗ[ZMod 2] natural (Fin n))
    (he : ∀ g v, eV (ρ g v) = alternatingNaturalRepresentation (Fin n) (eG g) (eV v)) :
    Module.finrank (ZMod 2) (H1 ρ) = if Even n then 1 else 0 := by
  rw [(H1Congr ρ (alternatingNaturalRepresentation (Fin n)) eG eV he).finrank_eq]
  exact alternatingNatural_firstCohomology_finrank n hmin hmax

/-- The projectivity clause of I.1.6(1), for the four-dimensional
deleted-permutation A₅-module of B.3. -/
theorem alternatingFiveNatural_projective :
    Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      (alternatingNaturalRepresentation (Fin 5)).asModule :=
  alternatingFive_natural_projective

/-- The projectivity assertion applies to every equivariant realization of
the natural A₅-module. -/
theorem alternatingFiveNatural_projective_of_equiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) V)
    (e : V ≃ₗ[ZMod 2] natural (Fin 5))
    (he : ∀ g v, e (ρ g v) = alternatingNaturalRepresentation (Fin 5) g (e v)) :
    Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5))) ρ.asModule := by
  let := alternatingFiveNatural_projective
  let f : ρ.IntertwiningMap (alternatingNaturalRepresentation (Fin 5)) :=
    { toLinearMap := e.toLinearMap
      isIntertwining' := fun g => LinearMap.ext (he g) }
  let F := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  let E := LinearEquiv.ofBijective F e.bijective
  exact Module.Projective.of_equiv E.symm

/-- I.1.6(8): vanishing for every four-dimensional irreducible binary
A₇-module, without choosing an isomorphism class. -/
theorem alternatingSeven_firstCohomology_eq_zero
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    [IsIrreducible ρ] (hdim : Module.finrank (ZMod 2) V = 4) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 :=
  binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four ρ hdim

/-- Lemma I.1.6(9): a faithful irreducible binary representation of a
quasisimple three-fold central cover of `A₆` has zero first cohomology.
In particular this applies to the six-dimensional module in the source. -/
theorem alternatingSixTripleCover_firstCohomology_eq_zero
    {G V : Type*} [Group G] [Finite G] [IsQuasisimple G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : G →* alternatingGroup (Fin 6))
    (_hsurj : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G)
    (hker : Nat.card f.ker = 3)
    (ρ : Representation (ZMod 2) G V) [Representation.IsIrreducible ρ]
    (hfaithful : Function.Injective ρ) :
    Module.finrank (ZMod 2) (Representation.OneCohomology.H1 ρ) = 0 := by
  have hex : ∃ z : f.ker, (z : G) ≠ 1 := by
    by_contra hn
    push Not at hn
    have hsub : Subsingleton f.ker := ⟨fun x y =>
      Subtype.ext ((hn x).trans (hn y).symm)⟩
    have hone : Nat.card f.ker = 1 := by
      let := hsub
      exact Nat.card_unique
    omega
  obtain ⟨z, hz⟩ := hex
  have hsub := Representation.subsingleton_H1_of_faithful_irreducible_central
    ρ hfaithful z (hcentral z.property) hz
  let := hsub
  exact Module.finrank_zero_of_subsingleton

/-- I.1.6(9), with `Â₆` specified exactly as in Notation A.3.5: a
quasisimple group with center of order three and central quotient A₆.
The existing covering-map form above proves the stronger assertion without
the six-dimensional restriction. -/
theorem alternatingSixTripleCover_firstCohomology_eq_zero_of_centralQuotient
    {G V : Type*} [Group G] [Finite G] [IsQuasisimple G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (eG : G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 6))
    (hcenter : Nat.card (Subgroup.center G) = 3)
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (hfaithful : Function.Injective ρ) (_hdim : Module.finrank (ZMod 2) V = 6) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  let f := eG.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hker : f.ker = Subgroup.center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ eG.injective, QuotientGroup.ker_mk']
  exact alternatingSixTripleCover_firstCohomology_eq_zero f
    (eG.surjective.comp (QuotientGroup.mk'_surjective _))
    (by rw [hker]) (by simpa only [hker] using hcenter) ρ hfaithful

end CFSG.Quasithin.ChapterI
