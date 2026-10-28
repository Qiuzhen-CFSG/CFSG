module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternatives

/-!
# Conditional assembly of the chosen-seed source trichotomy

Construct the original source alternatives by the fixed-space and moved-seed
case split. The common-normal and local numerical premises are proved in the
imported source. The full normalizer cubic bound, D.3.20 invariance and the
marked D.3.10 moved branch remain explicit independent inputs. The final
Chapter12 application retains their discharge and doubled-branch exclusion
with the assembly owner; it is not a proof of unconditional3.2.5 or12.2.2.

Source: Aschbacher--Smith3.2.5 and12.2.2, combined manuscript of
1 March2004, printed pp.580--581 and794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 3.2.5 from the three separately owned earlier inputs. The
nonzero-fixed-space branch constructs its Thompson premise, the unmoved
fixed-free branch constructs TI, and the moved branch uses both distinct
numerical bounds on their original actions. -/
theorem source325_of_earlier_inputs_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : D.NormalizerOrbitCubicBound h.toHypothesis1221)
    (hfixed : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
      componentOrbit V (normalizer (L : Set G)) = V)
    (hmoved : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.MarkedDoubled) :
    D.Source325Alternatives := by
  by_cases hc : V ⊓ centralizer (L : Set G) = ⊥
  · by_cases he : componentOrbit V (T : Subgroup G) = V
    · refine Or.inr (Or.inl ⟨he, hc, ?_⟩)
      exact D.ti_of_centralizer_eq_bot h.toHypothesis1221
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hc
    · exact Or.inr (Or.inr (hmoved (D.orbit_cubicRatio_le_of_many h hmany)
        hfull hc (lt_of_le_of_ne (le_componentOrbit V T) (Ne.symm he))))
  · have hU := hfixed (D.thompson_commutator_of_many_of_fixedSpace_ne_bot h hmany hc) hc
    have hn : normalizer (L : Set G) ≤ normalizer (V : Set G) :=
      hU ▸ le_normalizer_componentOrbit V (normalizer (L : Set G))
    exact Or.inl ⟨le_antisymm
      (iSup_conjugates_le_of_le_normalizer V T V le_rfl
        (D.sylow_normalizes_component.trans hn)) (le_componentOrbit V T), hU⟩

/-- Actual Chapter 12 application of the conditional source assembly.
Final assembly must supply the earlier inputs and exclude the marked
branch using the normalized non-FF and double-natural source producers. -/
theorem structural_of_earlier_inputs_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : D.NormalizerOrbitCubicBound h.toHypothesis1221)
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
  D.structural_of_source325_of_not_doubled_of_many h hmany
    (D.source325_of_earlier_inputs_of_many h hmany hfull hfixed hmoved) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
