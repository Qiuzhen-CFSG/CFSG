module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SplitOrRee
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstSpecialLinear

/-!
# First-normalizer refinement for the split and Ree carrier branches

The local embedding determines the coefficient field of the containing
component. The existing Cartan rank sieve then leaves only field four and
the two ternary linear models. The fixed-cubic argument excludes SL₃(4),
while the PSL₃(4) branch identifies the quotient of the original K join X
with PGL₃(4). This discharges the embedding-list premise for these carrier
branches and retains the actual quotient needed by the triangle owner.

The preceding flag, pointwise action, and Cartan inputs are produced by
qt-d-1222-natural-flag-cartan, with final discharge in
qt-d-1222-natural-local-geometry. The relative-components owner retains
the other carriers, second-normalizer equality, and the triangle itself.

Source: Aschbacher--Smith 11.1.1--11.1.2, printed pp.761--764,
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

/-- In the split and Ree carriers, equality or the literal field-four
PSL₃/PGL₃ pair follows without an exhaustive embedding-list premise. -/
theorem first_split_or_ree_equal_or_projective
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : SplitOrReeCarrier (K ⧸ pCore 2 K)) :
    f.Li 0 = K ∨ S.field.degree = 2 ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∧
      IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) := by
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi 0 : Set G) := f.invariant 0
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi 0 : Set G)) :=
    ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩
  rcases relative_equal_or_lie_of_split_or_ree hs (flag_mem_local_of_model D S f 0 hm)
    hK.1 hLK S.nonbinary hm hmodel with he | hl
  · exact .inl he
  obtain ⟨hfour,hl⟩ := first_lie_overgroup_four_linear_of_cartan D S f hu hm hfix hX hK hLK
    hXcard hfaith hl
  rcases hl with hl | hl
  · exact (first_component_not_specialLinearFour D S f hu hm hfour hfix hX hK hLK
      hXcard hfaith hl).elim
  · exact .inr ⟨hfour,hl,first_projective_four_quotient D S f hu hm hfour hfix hX hK hLK
      hXcard hfaith hl⟩

/-- Apply the matched-carrier branch to the existing first-index reduction.
The further field-four triangle clauses remain with the same assembly owner. -/
theorem first_reduction_of_split_or_ree
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : SplitOrReeCarrier (K ⧸ pCore 2 K)) :
    RefinementReduction L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  rcases first_split_or_ree_equal_or_projective D S f hu hm hfix hX hK hLK hXcard hfaith hmodel
    with he | ⟨hfour,_,hpgl⟩
  · exact .equal (by simpa using he)
  · exact .pgl3 rfl hfour hpgl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
