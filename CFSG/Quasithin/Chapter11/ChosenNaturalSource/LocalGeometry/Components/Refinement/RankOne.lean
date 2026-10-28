module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstPrimeLinear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.PointResidual

/-!
# The first-normalizer refinement for rank-one component quotients

The actual binary rank-one row gives equality. In the odd rows the local
embedding proves the field-four parameter and prime congruences, so the
prime-field argument gives the source refinement and the PSL₂(25) action
argument excludes the quadratic row. No full embedding list, field-four
hypothesis or exceptional-prime hypothesis is assumed by this consumer.

The earlier flag's quotient model, inner uniqueness and pointwise L₁ action,
and the original Hall Cartan, remain the explicit preceding inputs. Their
producer is qt-d-1222-natural-flag-cartan; the ultimate discharge remains
with qt-d-1222-natural-local-geometry. The relative-components task still
owns the other model branches and construction of the field-four triangle.

Source: Aschbacher--Smith 11.1.1--11.1.2, printed pp.761--762,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The rank-one branch of the first-normalizer refinement, with the
binary degree and prime congruences proved from the local embedding. -/
theorem first_refinement_of_rank_one
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hmodel : (∃ m, 1 < m ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ m)) ∨
      ∃ p, p.Prime ∧ Odd p ∧ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2))) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  by_cases he : f.Li 0 = K
  · exact .equal (by simpa using he)
  rcases hmodel with ⟨m, hm', hk⟩ | ⟨p, hp, ho, hmodel⟩
  · exact .equal (by simpa using flag_eq_of_binary_rank_one D S f 0 hm hK.1 hLK hm' hk)
  have h := flag_odd_rank_one_parameters D S f 0 hm hK.1 (lt_of_le_of_ne hLK he) hp ho
  rcases hmodel with hk | hk
  · obtain ⟨hn2, hprime⟩ := h.1 hk
    exact first_refinement_of_primeLinear D S f hu hm hX hK hLK hn2 hprime hk
  · obtain ⟨hn2, hp5⟩ := h.2 hk
    exact (first_component_not_twentyFive D S f hm hn2 hfix hK.1 hLK
      (by simpa [hp5] using hk)).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
