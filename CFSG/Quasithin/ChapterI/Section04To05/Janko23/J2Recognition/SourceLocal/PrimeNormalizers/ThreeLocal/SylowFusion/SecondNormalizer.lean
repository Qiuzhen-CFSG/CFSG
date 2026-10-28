module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.FiveExclusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.NormalRoot

/-!
# The full normalizer of every second-class cubic subgroup

For a cubic element in the selected component, the involution geometry of
the literal quotient C_G(⟨y⟩)/⟨y⟩ gives either relative root normality or
C_G(⟨y⟩) ≃ C₃ × A₅. The actual 47.2 component and vertex-generation data,
together with the first cubic centralizer, exclude the latter alternative.

Relative root normality identifies the root with the intrinsic two-core of
the cubic centralizer. Hence the full cubic normalizer preserves it, and
the marked A₄ × A₅ root normalizer gives N_G(⟨y⟩) ≃ S₃ × A₄. Element
fusion transports this isomorphism to every element of 3B.

This discharges `SecondNormalizerFamily` from the earlier source inputs
`CentralizerCalculation`, `SelectedGeometry`, and `FiveLocal.SourceConclusion`.
No further ambient order or simplicity premise is needed for this implication.
Their source constructions remain with their respective assembly owners.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3(2), printed pp.261–262.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- This is the actual consumer of the five-local exclusion. Its remaining
premise is the intermediate recognition alternative, not a normalizer model. -/
theorem normal_root_of_centralizer_alternatives
    (H : CentralizerCalculation D) (S : InvolutionGeometry.SelectedGeometry D)
    (F : FiveLocal.SourceConclusion D S.t) (hA : CentralizerAlternatives S)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent S.t) (hyo : orderOf y = 3) :
    RootNormal S y :=
  (hA y hy hyo).resolve_right
    (not_centralizer_equiv_cyclic_three_alternating_five H F hyo)

/-- The independently proved centralizer alternative and the exact 47.2
exclusion give normality of the actual root inside the cubic centralizer. -/
theorem normal_root
    (H : CentralizerCalculation D) (S : InvolutionGeometry.SelectedGeometry D)
    (F : FiveLocal.SourceConclusion D S.t)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent S.t) (hyo : orderOf y = 3) :
    RootNormal S y :=
  normal_root_of_centralizer_alternatives H S F (centralizerAlternatives S) hy hyo

/-- The full ambient normalizer for a cubic element of the literal component;
all intermediate recognition and relative-normality premises are discharged. -/
theorem normalizer_equiv_of_mem_component
    (H : CentralizerCalculation D) (S : InvolutionGeometry.SelectedGeometry D)
    (F : FiveLocal.SourceConclusion D S.t)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent S.t) (hyo : orderOf y = 3) :
    Nonempty (normalizer (zpowers y : Set G) ≃*
      (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))) :=
  normalizer_equiv_of_rootNormal S hy hyo (normal_root H S F hy hyo)

/-- Aschbacher 47.3(2): every second-class cubic subgroup has full normalizer
S₃ × A₄. Only the specified earlier-source calculations remain as inputs. -/
theorem secondNormalizerFamily
    (H : CentralizerCalculation D) (S : InvolutionGeometry.SelectedGeometry D)
    (F : FiveLocal.SourceConclusion D S.t) : SecondNormalizerFamily D := by
  obtain ⟨x, hx, hxo, hxB⟩ := exists_component_three S
  obtain ⟨ex⟩ := normalizer_equiv_of_mem_component H S F hx hxo
  intro y hy
  obtain ⟨g, hg⟩ := isConj_iff.mp (threeB_isConj S hxB hy)
  let e := MulAut.conj g
  have hmap : (zpowers x).map e.toMonoidHom = zpowers y := by
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers hg
  have hnmap : (normalizer (zpowers x : Set G)).map e.toMonoidHom =
      normalizer (zpowers y : Set G) := by
    rw [map_equiv_normalizer_eq, hmap]
  exact ⟨(MulEquiv.subgroupCongr hnmap).symm.trans
    (((normalizer (zpowers x : Set G)).equivMapOfInjective
      e.toMonoidHom e.injective).symm.trans ex)⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
