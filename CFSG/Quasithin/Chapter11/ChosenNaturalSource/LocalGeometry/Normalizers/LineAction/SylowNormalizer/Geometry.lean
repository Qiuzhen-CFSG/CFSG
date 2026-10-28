module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.Frattini

/-!
# The exceptional local configuration in source 3.3.16

The two literal flag residuals, their PSL₂ quotients and their generation of L
are the outputs of the independent flag geometry. For an escaping odd Sylow
complement, generation forces one residual to move. If its Sylow join is a
minimal parabolic, the common-normal theorem gives a nonzero two-core after
adjoining the complement; the proved local-component theorem then constructs
the unique normal containing component.

JankoConfiguration records the remaining specific conclusion of 3.3.12--16:
field order four, the actual J₁ two-core quotient, relative normality in the
same local join, and the induced inner action of T on the rank-one quotient.
This is an intermediate mathematical configuration, not an existence theorem
or a claim of Sylow-normalizer containment. Its construction and exclusion are
separate source obligations. The last lemma supplies the normal-subgroup
contradiction used in its SL₃(4) terminal branch.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
3.3.12, 3.3.15--16, printed pp.588--591; the consumer is 11.2.3, pp.768--769.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The precise preceding flag output consumed here. The residuals are
N_L(Vᵢ)^∞, not arbitrary subgroups carrying a rank-one label. -/
structure FlagInput : Prop where
  model : ∀ i : Fin 2,
    ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree)
  generate : f.Li 0 ⊔ f.Li 1 = L

namespace FlagInput
variable {S f} (P : FlagInput S f) (A : OddSupplement T)
include P

/-- The escaping Hall subgroup moves one of the actual flag residuals. -/
theorem exists_moved_residual
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ i : Fin 2, ¬ A.subgroup ≤ normalizer (f.Li i : Set G) := by
  have hg : (f.Li 0 ⊔ f.Li 1) ⊔ (T : Subgroup G) = L ⊔ (T : Subgroup G) := by
    rw [P.generate]
  rcases A.moves_generator (D := D) (S := S) hg hescape with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- Common-normal control puts the actual enlarged parabolic in H(T). -/
theorem enlarged_parabolic_mem_HOver (i : Fin 2)
    (hmax : Order.HasUniqueMaximalOver (T : Subgroup G)
      (f.Li i ⊔ (T : Subgroup G))) :
    ((f.Li i ⊔ (T : Subgroup G)) ⊔ A.subgroup) ∈ Chapter1.HOver G (T : Set G) :=
  A.parabolic_join_mem_HOver (D := D) (S := S)
    (Components.flag_mem_local_of_model D S f i (P.model i)) hmax

/-- The first two clauses of 3.3.12 hold in the actual enlarged parabolic.
The exceptional quotient comparison remains separate. -/
theorem exists_normal_component (i : Fin 2)
    (hmax : Order.HasUniqueMaximalOver (T : Subgroup G)
      (f.Li i ⊔ (T : Subgroup G))) :
    ∃ K : Subgroup G,
      Source.NormalComponentIn ((f.Li i ⊔ (T : Subgroup G)) ⊔ A.subgroup) K ∧
      f.Li i ≤ K ∧
      ∀ J : Subgroup G,
        Source.ComponentIn ((f.Li i ⊔ (T : Subgroup G)) ⊔ A.subgroup) J →
        f.Li i ≤ J → J = K := by
  let H := (f.Li i ⊔ (T : Subgroup G)) ⊔ A.subgroup
  have hH := P.enlarged_parabolic_mem_HOver A i hmax
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) :=
    ⟨H.pCoreIn 2, hH.1, pCore_isPGroup.map H.subtype, rfl⟩
  have hsqt : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
      ((S.source.simpleQTKE.twoLocal_sqtk hN).subgroup _)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_left
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
  exact Components.exists_unique_normal_component hsqt hs
    (le_sup_left.trans le_sup_left)
    (Components.flag_mem_local_of_model D S f i (P.model i)) (f.sylow_normalizes_Li i)

/-- An escaping complement gives a proper normal component enlargement at
one of the two actual flag residuals. This stops before the model comparison. -/
theorem exists_moved_normal_component
    (hmax : ∀ i : Fin 2, Order.HasUniqueMaximalOver (T : Subgroup G)
      (f.Li i ⊔ (T : Subgroup G)))
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ (i : Fin 2) (K : Subgroup G),
      ¬ A.subgroup ≤ normalizer (f.Li i : Set G) ∧
      Source.NormalComponentIn ((f.Li i ⊔ (T : Subgroup G)) ⊔ A.subgroup) K ∧
      f.Li i < K := by
  obtain ⟨i, hi⟩ := P.exists_moved_residual A hescape
  obtain ⟨K, hK, hYK, _⟩ := P.exists_normal_component A i (hmax i)
  refine ⟨i, K, hi, hK, lt_of_le_of_ne hYK ?_⟩
  intro he
  have hnorm := (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  exact hi (he.symm ▸ (le_sup_right.trans hnorm))

end FlagInput

/-- The exceptional J₁ alternative in the first paragraph of 3.3.16.
All normality and component assertions are relative to the literal Hᵢ. -/
structure JankoConfiguration (A : OddSupplement T) where
  index : Fin 2
  degree_eq_two : S.field.degree = 2
  component : Subgroup G
  parabolic : Order.HasUniqueMaximalOver (T : Subgroup G)
    (f.Li index ⊔ (T : Subgroup G))
  moves : ¬ A.subgroup ≤ normalizer (f.Li index : Set G)
  contains : f.Li index < component
  normal_component : Source.NormalComponentIn
    ((f.Li index ⊔ (T : Subgroup G)) ⊔ A.subgroup) component
  model : Nonempty (component ⧸ pCore 2 component ≃* Janko1.Model)
  outside : ¬ component ⊓ A.subgroup ≤ normalizer (L : Set G)
  inner : ∀ t : (T : Subgroup G),
    coreQuotientAction (f.Li index)
      ⟨t, f.sylow_normalizes_Li index t.property⟩ ∈
        MulAut.innerSubgroup (f.Li index ⧸ pCore 2 (f.Li index))

namespace JankoConfiguration
variable {S f} {A : OddSupplement T} (E : JankoConfiguration S f A)

include E in
/-- The exceptional local configuration retains the original escaping
Sylow normalizer, so the proved characteristic-subgroup obstruction applies. -/
theorem sylow_escape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  fun h => E.outside (inf_le_right.trans (A.normalizes.trans h))

/-- The exceptional component really escapes N_G(L). -/
theorem component_not_le : ¬ E.component ≤ normalizer (L : Set G) :=
  fun h => E.outside (inf_le_left.trans h)

/-- A nontrivial common normal subgroup gives the exact source contradiction
in the SL₃(4) branch. The terminal producer must construct this subgroup and
both normalization assertions from the actual field-four configuration. -/
theorem false_of_common_normal {Q : Subgroup G}
    (hQ : Q ≤ L ⊔ (T : Subgroup G)) (hne : Q ≠ ⊥)
    (hLQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : E.component ≤ normalizer (Q : Set G)) : False :=
  E.component_not_le (hKQ.trans
    (D.normal_subgroup_normalizer_le S.source.toHypothesis1221 hQ hne hLQ))

end JankoConfiguration
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
