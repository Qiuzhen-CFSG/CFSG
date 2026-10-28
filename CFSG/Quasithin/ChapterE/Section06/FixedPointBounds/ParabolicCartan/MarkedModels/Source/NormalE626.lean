module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalKnownSimple
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Overlap.Source
/-!
# The original normal-component Cartan application after E.6.26

The source Hall data proves solvability of the original maximal subgroup.
Its genuine E-generation and the proved E.6.26 argument now place it in M.
Thus the original normal-component residual Cartan alternative retains only
4.4.13(1) as an earlier containment input. No E.6.26 callback remains.
Source: Aschbacher–Smith E.6.26–27, pp.256–257.
-/

public section
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem source_normal_residual_alternative_of_thompson_source
    {T : Sylow 2 G} {U M V : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One KnownSimple.IsKnownSimple G)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤ M ⊓ centralizer (V : Set G))
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (S : Sylow 2 (centralizer (U : Set G)))
    (hS : (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map (M ⊓ centralizer (U : Set G)).subtype)
    (P : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hP : ChapterB.IsMinimalParabolicOver (residualSylow S) P)
    (hn : j < generationParameter P)
    (K : Subgroup P) (hK : K.IsCComponent) [K.Normal]
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (parabolicSylow S P hP : Subgroup P) = ⊤)
    (hescape : ¬ (P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M) :
    ∃ f : ℕ, IsEGenerated f P ∧ generationParameter P ≤ f ∧
      ParabolicCartanAlternative V M U
        ((P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype) f := by
  have hn1 : 1 < generationParameter P := lt_of_le_of_lt hj1 hn
  obtain ⟨f,hg,hb,⟨d⟩⟩ := source_normal_intrinsic_cartan_knownSimple
    (residual_sqtk h hU hUV P) (parabolicSylow S P hP)
    (minimalParabolic_subtype (residualSylow S) P hP) hn1 K hK hqs hgen
  have hM := Overlap.source_residual_maximal_eq_overlap h hU hUV hj1 hj hJ R S hS
    P hP d.maximal_solvable hescape
  let d' := transportResidual S P hP f d M hM R hS.symm
  exact ⟨f,hg,hb,residual_alternative_of_hall_data_at h hU hUV earlier P
    (parabolicSylow S P hP) (minimalParabolic_subtype (residualSylow S) P hP)
    (residual_twoCore_ne_bot h hU hUV S P hP) hn1 hM hescape d'⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
