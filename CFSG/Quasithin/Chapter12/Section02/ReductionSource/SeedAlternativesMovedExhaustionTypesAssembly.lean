module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionTypes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowTripleSixAssembly

/-!
# Repeated-copy reduction for the literal normalizer orbit

The completed moved-Sylow classification and the characteristic-kernel
transport account for every constituent type in the full normalizer orbit.
If that orbit exceeds the Sylow orbit, inverse translation by the marked
Sylow element produces a same-type conjugate outside the Sylow orbit. TI
makes this conjugate disjoint from the seed.

Both source325 and its actual Chapter12 structural consumer now reduce to
containing such same-type copies. Proving that containment from the full
normalizer cubic bound remains with qt-baumann-fsu; the independent final
doubled-branch exclusion remains with qt-d-1222-source. These conditional
applications do not assert the completed source theorem.

Source: Aschbacher--Smith D.3.10--19, 3.2.5 and 12.2.2,
printed pp.201--204,580 and794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The completed local classifier supplies the two full-normalizer types. -/
theorem normalizer_two_types_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G)) :
    ∀ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∨
      SameConjugationModule L (V.map (MulAut.conj t).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom) :=
  D.normalizer_two_types_of_constituentModel h.quasisimple
    (D.seed_constituentModel_of_moved_of_many h hmany hc hm) t ht hnt

/-- The literal Sylow pair marks every constituent type in the full normalizer
orbit. This does not bound the number of copies of either type. -/
theorem normalizer_type_pair_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V : Set G) ∧
      componentOrbit V (T : Subgroup G) = V ⊔ V.map (MulAut.conj t).toMonoidHom ∧
      V ⊓ V.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      ¬ SameConjugationModule L V (V.map (MulAut.conj t).toMonoidHom) ∧
      ∀ g ∈ normalizer (L : Set G),
        SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∨
        SameConjugationModule L (V.map (MulAut.conj t).toMonoidHom)
          (V.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨_,t,ht,hnt,hpair⟩ := D.sylowMovedModel_of_moved_of_many h hmany hc hm
  exact ⟨t,ht,hnt,hpair,D.moved_conjugate_inf_eq_bot h.toHypothesis1221 hc ht hnt,
    D.moved_conjugate_not_sameModule ht hnt,
    D.normalizer_two_types_of_moved_of_many h hmany hc hm t ht hnt⟩

/-- A strict full-normalizer enlargement supplies a disjoint same-type copy
outside the literal Sylow orbit. This is the remaining multiplicity obstruction. -/
theorem exists_repeated_conjugate_of_normalizerOrbit_ne
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠
      componentOrbit V (T : Subgroup G)) :
    ∃ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∧
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ componentOrbit V (T : Subgroup G) := by
  obtain ⟨t,ht,hnt,_⟩ := D.exists_moved_conjugate_geometry h.toHypothesis1221 hc hm
  obtain ⟨g,hg,he,hout⟩ := exists_repeated_conjugate_of_larger_orbit
    D.sylow_normalizes_component ⟨t,ht⟩
    (D.normalizer_two_types_of_moved_of_many h hmany hc hm t ht hnt) hne
  refine ⟨g,hg,he,?_,hout⟩
  apply (D.ti_of_centralizer_eq_bot h.toHypothesis1221
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hc g hg).resolve_right
  intro hv
  exact hout (hv.le.trans (le_componentOrbit V (T : Subgroup G)))

/-- Excluding escaping copies of the seed type suffices for full exhaustion;
no separate containment premise for the second type is needed. -/
theorem normalizerOrbit_eq_of_same_type_contained
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hcopies : ∀ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) →
      V.map (MulAut.conj g).toMonoidHom ≤ componentOrbit V (T : Subgroup G)) :
    componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G) := by
  by_contra hn
  obtain ⟨g,hg,he,_,hout⟩ := D.exists_repeated_conjugate_of_normalizerOrbit_ne h hmany hc hm hn
  exact hout (hcopies g hg he)


/-- The source assembly reduces to containment of same-type copies. The
owner qt-baumann-fsu must still prove that premise from the cubic bounds. -/
theorem source325_of_same_type_containment_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcopies : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      ∀ g ∈ normalizer (L : Set G),
        SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) →
        V.map (MulAut.conj g).toMonoidHom ≤ componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_exhaustion_of_many h hmany
  intro hq hfull hc hm hs
  exact D.normalizerOrbit_eq_of_same_type_contained h hmany hc hm
    (hcopies hq hfull hc hm hs)

/-- The actual structural consumer retains same-type containment with
qt-baumann-fsu and the independent doubled-branch exclusion with qt-d-1222-source. -/
theorem structural_of_same_type_containment_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcopies : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      ∀ g ∈ normalizer (L : Set G),
        SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) →
        V.map (MulAut.conj g).toMonoidHom ≤ componentOrbit V (T : Subgroup G))
    (hex : ¬ D.MarkedDoubled) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) ∧
    ((normalizer (L : Set G)) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) :=
  D.structural_of_source325_of_not_doubled_of_many h hmany
    (D.source325_of_same_type_containment_of_many h hmany hcopies) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
