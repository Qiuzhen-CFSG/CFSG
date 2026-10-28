module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Rank
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.WeakClosure.Generation

/-!
# Nonabelianness of the original natural closure under K = L₁

The two native point-model calculations give the intersection-line assertion
and the global corank bound. The actual semilinear plane rank and the proved
plane-displacement calculation then align every offending conjugate with V₁.
If the normal closure W were abelian, V₂ would lie in C₁(T,V). Its centralizer
bound and the genuine 11.2.5 obstruction supply the two relative subgroup
bounds in E.3.19. The actual Sylow subgroup of the chosen outside H and n(H)=1
then force H into M, a contradiction.

All local point-generation and plane-action premises are discharged. The
remaining hypotheses are precisely named preceding chapter inputs. Parent
`qt-d-1222-natural-closure` supplies those inputs and assembles the final
11.5.8 contradiction; this module establishes 11.5.3(3), including q=4.
Source: Aschbacher--Smith, printed pp.779--780; E.3.19, pp.234--235.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian
open Subgroup
open CFSG.Quasithin.ChapterE CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (F₀ : MarkedFlag E)

include F₀ in
/-- Source 11.5.3(3), on the original natural module and literal normal closure.
All remaining inputs are preceding source hypotheses; the two point-generation
calculations and the plane-action rank are discharged here. -/
theorem not_isMulCommutative_of_K_eq
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ E.M)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hK : E.Kz = E.K)
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hobstruction : Chapter11.Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hm : @localM _ _ V D.elementary = E.input.field.degree)
    (hn : generationParameter E.H = 1) :
    E.K = E.L₁ → ¬ IsMulCommutative E.W := by
  intro hKL habelian
  obtain ⟨hintersection, hr⟩ := PointModels.intersection_and_rank F₀ hfixed hz hz1 htrans hK hTI hKL
  obtain ⟨hC, hN⟩ := LineAlignment.weakClosure_bounds_of_plane_rank F₀ hfixed hNV
    hintersection hr hH hobstruction (LineAlignment.plane_action_rank_bound F₀ hfixed hNV) habelian
  have hTH : (T : Subgroup G) ≤ E.H := hH.1.1.2
  have hS : ((T.subtype hTH : Sylow 2 E.H) : Subgroup E.H).map E.H.subtype =
      (T : Subgroup G) := by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
  have hs := one_lt_globalS F₀ hfixed hm (by rwa [corank_line F₀ hfixed])
  let := D.elementary
  have hgen := RankOneWeakClosure.generation_of_parameter_eq_one (T.subtype hTH) hn hs
  rw [hS] at hgen
  apply hH.1.2
  rw [hgen]
  exact sup_le (inf_le_right.trans hC) hN

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian
