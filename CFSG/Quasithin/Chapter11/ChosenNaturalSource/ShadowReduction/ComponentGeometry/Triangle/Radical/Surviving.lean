module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.PrimeContainment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.PSLIndex
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.Commutator

/-!
# The surviving alternatives in the original chosen geometry

The first bound of 11.4.1(3) is proved for every surviving alternative.
The equal and PSL₂ cases also give the second bound, including the
index-one calculation in the latter. The final assembly below isolates
exactly the still-needed index calculation for the two-odd SL₂ branch.
It does not assert that this calculation follows from an arbitrary
normal two-extension, or that the source theorem is complete.

The source's component lives in C_G(V₁), with relative normality retained;
T-normalization and the preceding X-normalization facts remain explicit.
All residuals and cores are those of the original chosen flag.
Source: Aschbacher--Smith 11.4.1(3), printed pp.775--776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical

private theorem sl2_prime_parameters {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p)) :
    p.Prime ∧ 3 < p := by
  rcases hp with rfl | ⟨hp, hlarge⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨hp, by omega⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The radical containment is complete conditional on the surviving list;
no signalizer or radical-containment premise remains. -/
theorem ofFlag_surviving_radical_containment (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hA : f.Li 0 ≠ ⊥) (hAK : f.Li 0 ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree) :
    (ofFlag S f X z H).R₁ ≤
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype := by
  cases hcase with
  | equal he =>
      change ((f.Li 0) ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
      rw [he]
      apply map_mono
      let : Group.IsNilpotent (pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) :=
        pCore_isPGroup.isNilpotent
      exact le_solvableRadical _ inferInstance inferInstance
  | sl2Prime hi hn p hp hm =>
      have hprime := sl2_prime_parameters hp
      let : Fact p.Prime := ⟨hprime.1⟩
      exact ofFlag_radical_containment_of_prime_model S f X z H K hA hAK hTK hprime.2
        (relative_radical_model_of_twoOdd_sl2 hK.1 hprime.2 hm)
  | psl2Prime hi hn p hp hlarge hm hL =>
      let : Fact p.Prime := ⟨hp⟩
      let : Group.IsPerfect K := relative_component_perfect hK.1
      exact ofFlag_radical_containment_of_prime_model S f X z H K hA hAK hTK (by omega)
        (radical_model_of_psl2 (by omega) hm)

/-- The prime PSL₂ branch proves both bounds, including the Fitting index. -/
theorem ofFlag_psl_bounds (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hA : f.Li 0 ≠ ⊥) (hAK : f.Li 0 ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXK : X ≤ normalizer (K : Set G)) (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) :
    (ofFlag S f X z H).R₁ ≤
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
          (K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z H).R₁, X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let : Group.IsPerfect K := relative_component_perfect hK.1
  have hR := ofFlag_radical_containment_of_prime_model S f X z H K hA hAK hTK hp
    (radical_model_of_psl2 hp hm)
  exact ⟨hR, ofFlag_commutator_of_radical_fitting_index S f X z H K hAK hTK hXK hXR hR
    ((fitting_index_one_of_psl2 T K hTK hp hm).le.trans (by decide))⟩

/-- Conditional source assembly: only the SL₂ odd-extension Fitting index
remains to be supplied. The callback is an outstanding mathematical input,
not a certificate that original 11.4.1(3) has been completed. -/
theorem ofFlag_surviving_bounds_of_sl2_index (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hA : f.Li 0 ≠ ⊥) (hAK : f.Li 0 ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXK : X ≤ normalizer (K : Set G)) (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree)
    (hindex : ∀ p : ℕ, S.field.degree = 2 → (p = 5 ∨ (p.Prime ∧ 11 ≤ p)) →
      Source.IsSL (Source.TwoOddQuotient K) 2 p →
      (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2) :
    (ofFlag S f X z H).R₁ ≤
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
          (K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z H).R₁, X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hR := ofFlag_surviving_radical_containment S f X z H K hK hA hAK hTK hcase
  refine ⟨hR, ?_⟩
  cases hcase with
  | equal he => exact (ofFlag_equality_bounds S f X z H K he hXR).2
  | sl2Prime hi hn p hp hm =>
      exact ofFlag_commutator_of_radical_fitting_index S f X z H K hAK hTK hXK hXR hR
        (hindex p hn hp hm)
  | psl2Prime hi hn p hp hlarge hm hL =>
      let : Fact p.Prime := ⟨hp⟩
      exact (ofFlag_psl_bounds S f X z H K hK hA hAK hTK hXK hXR (by omega) hm).2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
