module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLineOrbits
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLinesAt

/-!
# The two component orbits at the same G,T

The guarded fixed-line splitting and the actual component supplement X=KT
show that the full omega span is the sum of the two component orbits.
This retains the literal component and does not assume a direct sum.
Both linear and alternating module comparisons consume this equality.
Source: Aschbacher--Smith 13.4.7, printed pp.900--901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
/-- The whole original omega module is the sum of the two component orbits.
The component and both fixed lines are those constructed from the original pair. -/
theorem original_pair_component_fixed_line_spans_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (L : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let C := K.map X.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let F₁ := Z ⊓ centralizer (A : Set G)
    let F₂ := Z ⊓ centralizer (B : Set G)
    conjugateSpanBy Z X = conjugateSpanBy F₁ C ⊔ conjugateSpanBy F₂ C := by
  have hd := pair_fixed_subgroups_ne hTA hTB eA eB hne hres
  have hs := (original_pair_fixed_lines_at h structural D m hout
    hindexL hindexA hindexB hd).2.2.2.2.1
  have hTC := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2.2.2.1
  have hg := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  exact pair_fixed_line_spans A B (K.map (A ⊔ B).subtype) hTC hg hs

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
