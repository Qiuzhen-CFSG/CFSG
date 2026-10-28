module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesNormalizerBound
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesFixedComplete

/-!
# Chosen-seed assembly with both numerical bounds discharged

The full normalizer-orbit bound supplies `hfull` in the original conditional
3.2.5 consumer. Combining it with the proved fixed-space branch leaves only
the marked moved-seed argument, retained with this assembly's owner
`qt-baumann-fsu`. The structural consumer also retains exclusion of the marked
doubled branch, whose final discharge belongs to `qt-d-1222-source`.

Source: Aschbacher--Smith 3.2.5 and 12.2.2, printed pp.580--581,794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual source-alternatives consumer, with its full-orbit numerical
premise supplied by 3.1.6. -/
theorem source325_of_fixed_and_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfixed : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
      componentOrbit V (normalizer (L : Set G)) = V)
    (hmoved : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.MarkedDoubled) :
    D.Source325Alternatives :=
  D.source325_of_earlier_inputs_of_many h hmany
    (D.normalizerOrbit_cubicBound_of_many h hmany) hfixed hmoved

/-- The Chapter 12 structural consumer needs no independent numerical
bound, while retaining the separately owned source branches. -/
theorem structural_of_fixed_and_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfixed : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
      componentOrbit V (normalizer (L : Set G)) = V)
    (hmoved : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.MarkedDoubled)
    (hex : ¬ D.MarkedDoubled) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) ∧
    ((normalizer (L : Set G)) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) :=
  D.structural_of_earlier_inputs_of_many h hmany
    (D.normalizerOrbit_cubicBound_of_many h hmany) hfixed hmoved hex

/-- Both cubic bounds and the fixed-space implication are discharged for
the original chosen seed. The moved D.3.5--10 argument remains explicit. -/
theorem source325_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmoved : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.MarkedDoubled) :
    D.Source325Alternatives :=
  D.source325_of_earlier_inputs_of_many_fixed_complete h hmany
    (D.normalizerOrbit_cubicBound_of_many h hmany) hmoved

/-- The actual Chapter 12 structural application after discharging the
numerical and fixed-space source inputs. -/
theorem structural_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmoved : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.MarkedDoubled)
    (hex : ¬ D.MarkedDoubled) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) ∧
    ((normalizer (L : Set G)) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) :=
  D.structural_of_source325_of_not_doubled_of_many h hmany
    (D.source325_of_moved_of_many h hmany hmoved) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
