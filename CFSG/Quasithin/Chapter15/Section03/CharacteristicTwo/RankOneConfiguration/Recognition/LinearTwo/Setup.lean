module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Inputs for the L₂ block exclusion

`Earlier` selects the local conclusions used to construct the invariant
four-group in the block module. Its source-theorem consumer must prove
these inputs. `BorelIdentification` records the genuine marked alternative
15.3.28(1): an even exponent greater than one, a finite field of that order,
and a multiplicative equivalence taking the actual intersection image to
the matrix Borel. It does not assume block recognition or a centralizer
calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11 and 15.3.26–30, printed pp.1123–1124 and 1130–1132.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo
variable {G : Type*} [Group G]

/-- Selected genuine conclusions preceding 15.3.30. The commutator and
normalizer clauses come from 15.3.11 and 15.3.26–27; elementarity of U_I
is the B.2.14 input stated before 15.3.26. This contains no block recognition. -/
structure Earlier (d : LocalData G) (I : Subgroup G) (c : ComponentWitness d I) : Prop where
  /-- 15.3.27(1), normality inside I. -/
  component_normal : (c.L.subgroupOf I).Normal
  /-- 15.3.27(2). -/
  contains : d.Yplus ≤ c.L
  /-- 15.3.11(6). -/
  theta_eq : theta (d.MI I) = d.Yplus
  /-- 15.3.11(4). -/
  normalizer_eq : I ⊓ normalizer (d.Yplus : Set G) = d.MI I
  /-- The natural-plane action in the second case of 15.3.10. -/
  plane_eq : ⁅d.V, d.Yplus⁆ = d.V₂
  plane_full : ⁅d.V₂, d.Yplus⁆ = d.V₂
  plane_le_span : d.V₂ ≤ d.UI I
  span_elementary : IsElementaryAbelian 2 (d.UI I)

/-- The marked alternative 15.3.28(1), with the actual projective matrix
group and the image of its upper triangular Borel. Both maps refer to the
same chosen identification of L*. -/
structure BorelIdentification (d : LocalData G) (I : Subgroup G)
    (c : ComponentWitness d I) (n : ℕ) (F : Type*) [Field F] [Finite F]
    [CharP F 2] where
  parameter_gt_one : 1 < n
  parameter_even : Even n
  field_card : Nat.card F = 2 ^ n
  projective : d.starImage I c.L ≃* Theory.PSL2.Group F
  borel : ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)).map
    projective.toMonoidHom =
      (Matrix.SpecialLinearGroup.rankOneBorel F).map (Theory.PSL2.quotientMap F)

variable {G : Type*} [Group G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
/-- The canonical characteristic-two SL₂–PSL₂ isomorphism gives
the actual linear model of the same star image. -/
noncomputable def BorelIdentification.linear (b : BorelIdentification d I c n F) :
    d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  b.projective.trans (Theory.PSL2.sl2QuotientEquiv F).symm

/-- The marked Borel is preserved under the canonical change of model. -/
theorem BorelIdentification.linear_borel (b : BorelIdentification d I c n F) :
    ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)).map
      b.linear.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F := by
  apply map_injective (Theory.PSL2.quotientMap_injective F)
  rw [map_map]
  have he : (Theory.PSL2.quotientMap F).comp b.linear.toMonoidHom =
      b.projective.toMonoidHom := by
    ext x
    exact (Theory.PSL2.sl2QuotientEquiv F).apply_symm_apply (b.projective x)
  rw [he]
  exact b.borel

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
