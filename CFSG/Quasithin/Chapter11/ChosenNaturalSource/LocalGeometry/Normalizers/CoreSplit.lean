module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers

/-!
# The corrected cohomology split for the point radical

The denominator in C.1.13 is V C_T(L). Both factors lie in O₂(LT), and
their join is normal there. The quotient is nontrivial precisely in the
strict-denominator branch; V < O₂(LT) alone does not establish this.
The printed V C_T(V) instead equals C_T(V), because V is abelian.

The escaping-normalizer hypothesis also proves the characteristic exclusion
in (MS3), using normality relative to LT and the original maximal-local
uniqueness theorem. The MS recognition, the cohomology-model calculation
and the Goldschmidt--O'Nan exclusion are still separate obligations.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.5, printed pp.765--766, with the C.1.13 denominator corrected.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The corrected C.1.13 denominator, V C_T(L), inside the original G. -/
def cohomologyDenominator (T : Sylow 2 G) (L V : Subgroup G) : Subgroup G :=
  V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))

omit [Finite G] in
/-- C_T(L) is normal in LT because T normalizes L. -/
theorem join_normalizes_componentCentralizer (D : ChosenModule T L V) :
    L ⊔ (T : Subgroup G) ≤
      normalizer (((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
  apply sup_le
  · exact (le_centralizer_iff.mpr inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  · exact (le_inf (T : Subgroup G).le_normalizer
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf

/-- Both factors of the corrected denominator lie in the actual O₂(LT). -/
theorem cohomologyDenominator_le_core (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) :
    cohomologyDenominator T L V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply sup_le
  · let := D.elementary
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      (D.le_sylow.trans le_sup_right) (sup_le D.normalizes S.sylow_normalizes)
  · exact le_pCoreIn_of_normalizes
      (T.isPGroup'.of_injective
        (inclusion (show (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ T from inf_le_left))
        (inclusion_injective _))
      (inf_le_left.trans le_sup_right) (join_normalizes_componentCentralizer D)

/-- Relative normality of the corrected denominator, for the literal quotient. -/
theorem cohomologyDenominator_normal (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) :
    ((cohomologyDenominator T L V).subgroupOf ((L ⊔ (T : Subgroup G)).pCoreIn 2)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply (pCoreIn_le _ _).trans
  exact (le_inf (sup_le D.normalizes S.sylow_normalizes)
    (join_normalizes_componentCentralizer D)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The required first split: only Q > V C_T(L) gives a nontrivial
cohomology quotient. V < Q by itself is not used. -/
theorem cohomology_quotient_split (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = cohomologyDenominator T L V ∨
      Nontrivial (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
        ((cohomologyDenominator T L V).subgroupOf ((L ⊔ (T : Subgroup G)).pCoreIn 2))) := by
  by_cases he : (L ⊔ (T : Subgroup G)).pCoreIn 2 = cohomologyDenominator T L V
  · exact Or.inl he
  · apply Or.inr
    apply QuotientGroup.nontrivial_iff.mpr
    intro ht
    apply he
    apply le_antisymm _ (cohomologyDenominator_le_core D S)
    exact subgroupOf_eq_top.mp ht

omit [Finite G] in
/-- In the equality branch, trivial C_T(L) really does give Q=V. -/
theorem core_eq_seed_of_denominator_eq
    (hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 = cohomologyDenominator T L V)
    (hC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = V := by
  simpa only [cohomologyDenominator, hC, sup_bot_eq] using hQ

omit [Finite G] in
/-- The printed V C_T(V) collapses to C_T(V), since the chosen V is abelian.
This identifies why it is not the denominator used in the repaired proof. -/
theorem printed_denominator_eq (D : ChosenModule T L V) :
    V ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let := D.elementary
  exact sup_eq_right.mpr (le_inf D.le_sylow V.le_centralizer)

/-- The escaping normalizer supplies the genuine characteristic exclusion
used in (MS3), with normality relative to LT rather than the ambient G. -/
theorem no_characteristic_normal_of_escape (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (C : Subgroup (f.Ri 0)) (hchar : C.Characteristic) (hne : C ≠ ⊥) :
    ¬ ((C.map (f.Ri 0).subtype).subgroupOf (L ⊔ (T : Subgroup G))).Normal := by
  intro hn
  let := hchar
  have hC : C.map (f.Ri 0).subtype ≤ L ⊔ (T : Subgroup G) :=
    (map_subtype_le _).trans ((localRadical_le_sylow _).trans le_sup_right)
  have hCne : C.map (f.Ri 0).subtype ≠ ⊥ := by
    intro he
    exact hne ((map_eq_bot_iff_of_injective C (f.Ri 0).subtype_injective).mp he)
  apply hescape
  exact (normalizer_le_normalizer_characteristic_image (f.Ri 0) C).trans
    (D.normal_subgroup_normalizer_le S.source.toHypothesis1221 hC hCne
      ((normal_subgroupOf_iff_le_normalizer hC).mp hn))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
