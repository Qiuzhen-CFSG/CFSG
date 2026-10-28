module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Factorization.Source
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.CubicOrder
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel.LocalInputs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic

/-!
# The original cubic quotients and solvable local edge

The prescribed natural action and Sylow flag mark the ordinary six-letter
point stabilizer or its genuine central triple cover. The ordinary residual
and the covered commutator residual have intrinsic two-core quotient of
order three. The actual covered factorization then gives solvability of
L1 T in both cases, without an order or solvability premise.

Source: Aschbacher--Smith, Notation 13.2.1 and 13.2.2(3), printed p.877;
applications in 13.8.12--15, pp.950--952.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace LocalFitting
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
variable {G : Type*} [Group G] [Finite G]
 {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
 (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem ordinary_natural
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (he : ∀ l : L, e (QuotientGroup.mk' (pCore 2 L) l) =
      d.local_quotient (QuotientGroup.mk' (centralCore L) l)) :
    Nonempty (OrdinarySource.NaturalSetup L (T : Subgroup G) V V₁) := by
  obtain ⟨f,hf,hv⟩ := local_permutation_extension d
  refine ⟨{
    model := e
    normalizes_L := d.normalizes_L
    normalizes_V := d.normalizes_V
    sylow := T.subtype le_sup_right
    sylow_eq := rfl
    permutation := f
    model_compatible := fun l => (hf l).trans (congrArg Subtype.val (he l)).symm
    naturalMap := d.coordinate.toMonoidHom
    naturalMap_surjective := d.coordinate.surjective
    naturalMap_kernel := ?_
    conjugation := hv
    point := local_flag_image d V₁
    point_dim := local_flag_image_dim d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 (by simpa using d.line_card)
    line_eq := local_flag_preimage d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
    line_stable := d.line_stable }⟩
  rw [local_centralizer_bot d]
  exact (MonoidHom.ker_eq_bot_iff _).mpr d.coordinate.injective

omit d [Finite G] in
private theorem hex_not_alternating :
    ¬ Nonempty (Atlas.Codes.HexEvenAutomorphisms ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr (centerCongr e).toEquiv
  rw [Representation.Hexacode.even_center_card,
    alternatingGroup.center_eq_bot (by simp),card_bot] at hc
  omega

theorem ordinary_core_card
    (hm : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))) :
    Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 3 := by
  rcases local_quotient_alternatives d with ⟨e,he⟩ | ⟨e,he⟩
  · obtain ⟨a⟩ := ordinary_natural d e he
    exact OrdinarySource.source_residual_quotient_card a _ rfl
  · obtain ⟨ea⟩ := hm
    exact (hex_not_alternating ⟨e.symm.trans ea⟩).elim

theorem covered_core_card
    (hm : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3 := by
  rcases local_quotient_alternatives d with ⟨e,he⟩ | ⟨e,he⟩
  · have hc := Nat.card_congr (centerCongr e).toEquiv
    rw [hm.2.1, alternatingGroup.center_eq_bot (by simp),card_bot] at hc
    omega
  · obtain ⟨a⟩ := local_covered_flag_model d e he
    exact a.plus_core_card (CoverFactorization.source_factorization a)

theorem local_solvable : Group.IsSolvable (one L T V₁ ⊔ (T : Subgroup G) : Subgroup G) := by
  rcases local_quotient_alternatives d with ⟨e,he⟩ | ⟨e,he⟩
  · exact (ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel.ordinary_local_inputs
      L T V₁ T.isPGroup' d.line_stable (ordinary_core_card d ⟨e⟩)).2
  · obtain ⟨a⟩ := local_covered_flag_model d e he
    have hf := CoverFactorization.source_factorization a
    let : IsMulCommutative (one L T V₁ ⧸ pCore 2 (one L T V₁)) := a.one_quotient_commutative hf
    have hs : Group.IsSolvable (one L T V₁) :=
      (Group.isSolvable_iff_subgroup_quotient (pCore 2 (one L T V₁))).mpr
        ⟨@IsNilpotent.to_isSolvable _ _ pCore_isPGroup.isNilpotent,
          Group.isSolvable_of_comm (fun a b => mul_comm a b)⟩
    let := hs
    let A := (one L T V₁).subgroupOf (one L T V₁ ⊔ (T:Subgroup G))
    let B := (T:Subgroup G).subgroupOf (one L T V₁ ⊔ (T:Subgroup G))
    let : A.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le (one L T V₁).le_normalizer (T_normalizes_one L T V₁ d.line_stable))
    let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
      (f:=(subgroupOfEquivOfLe (show one L T V₁ ≤ one L T V₁ ⊔ (T:Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show one L T V₁ ≤ one L T V₁ ⊔ (T:Subgroup G) from le_sup_left)).injective
    let : Group.IsSolvable (T:Subgroup G) := @IsNilpotent.to_isSolvable _ _ T.isPGroup'.isNilpotent
    let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
      (f:=(subgroupOfEquivOfLe (show (T:Subgroup G) ≤ one L T V₁ ⊔ (T:Subgroup G) from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show (T:Subgroup G) ≤ one L T V₁ ⊔ (T:Subgroup G) from le_sup_right)).injective
    exact Group.isSolvable_of_normal_sup_eq_top A B (codisjoint_subgroupOf_sup _ _).eq_top

end LocalFitting
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
