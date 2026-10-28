module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Orbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Multiplicity

/-!
# The reciprocal rank budget on the actual omega orbit

The source star projection identifies the actor rank with the literal
centralizer corank. The strict r-bound makes V_H normalize the selected doubled
conjugate. Its automizer bound then limits the Sylow fixed codimension of V_H
to 3n. Applied to actual G.1.6 quotient coordinates, this forces one natural
summand over the field of binary degree 2n. The local geometry remains an
output required from the earlier paragraphs of this same source proof.

Source: Aschbacher--Smith, 11.3.6, printed p.772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL2SylowFixedRecognition Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance rankBudgetFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

open CommonCore CommonCore.NaturalRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    [IsElementaryAbelian 2 (omegaClosure T H)]

omit [Finite F] [CharP F 2] in
/-- The fixed codimension uses the literal centralizer of the selected actor. -/
theorem source_fixedCodim_eq_corank
    (e : residualStar T H ≃* SL(2,F)) (R : Sylow 2 (residualStar T H))
    (A : Subgroup G) (hAH : A ≤ H)
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (A.subgroupOf H).map (starProjection T H)) :
    fixedCodim (binaryAction T H e) (R.mapSurjective (f := e.toMonoidHom) e.surjective) =
      ChapterE.subgroupCorank (omegaClosure T H)
        (omegaClosure T H ⊓ centralizer (A : Set G)) := by
  let C := (centralizer (A : Set G)).subgroupOf (omegaClosure T H)
  let U := fixedSpace (binaryAction T H e)
    (R.mapSurjective (f := e.toMonoidHom) e.surjective)
  let f : U ≃ C :=
    { toFun v := ⟨v.val.toMul,(sylow_fixed_iff e R A hAH hR _).mp v.property⟩
      invFun v := ⟨Additive.ofMul v.val,(sylow_fixed_iff e R A hAH hR _).mpr v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card U = Nat.card C := Nat.card_congr f
  have h1 := Submodule.card_eq_card_quotient_mul_card U
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hq : Nat.card (Additive (omegaClosure T H) ⧸ U) =
      Nat.card ((omegaClosure T H) ⧸ C) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C))
    calc
      _ = Nat.card (Additive (omegaClosure T H)) := by rw [← hc,mul_comm,← h1]
      _ = Nat.card (omegaClosure T H) := rfl
      _ = _ := h2
  have hv := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (omegaClosure T H) ⧸ U)
  rw [Nat.card_zmod] at hv
  unfold ChapterE.subgroupCorank
  rw [Subgroup.inf_relIndex_left,Subgroup.relIndex,Subgroup.index_eq_card,← hq,hv,
    Nat.log_pow (by decide)]
  rfl

omit [Finite G] [IsElementaryAbelian 2 (omegaClosure T H)] in
/-- The original star projection measures precisely the action corank. -/
theorem star_rank_eq_corank (A : Subgroup G) (hAH : A ≤ H) :
    BinaryOffender.rank ((A.subgroupOf H).map (starProjection T H)) =
      ChapterE.subgroupCorank A (A ⊓ centralizer (omegaClosure T H : Set G)) := by
  unfold BinaryOffender.rank ChapterE.subgroupCorank
  rw [← relIndex_ker,starProjection,QuotientGroup.ker_mk',relIndex_subgroupOf hAH,
    inf_relIndex_left]

omit [IsElementaryAbelian 2 (omegaClosure T H)] in
/-- The r-bound makes the actual omega orbit normalize the doubled conjugate. -/
theorem reciprocal_normalization (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S) (z : Geometry d H)
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T)
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (omegaClosure T H : Set G))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ (2 * S.field.degree))) :
    omegaClosure T H ≤ normalizer ((fullModule L V).map (MulAut.conj g).toMonoidHom : Set G) := by
  apply (le_centralizer_iff.mpr inf_le_right).trans
  apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR inf_le_left
  rw [ChapterE.globalR_map_equiv,← star_rank_eq_corank _ (hg.trans s.outside.1.1.2),
    selected_rank s g d hF hg ha z.s_value hmodel]
  exact z.r_bound

/-- The source 3n budget bounds the reciprocal action on any normalized conjugate. -/
theorem reciprocal_corank_budget
    (d : Coordinates D S) (z : Geometry d H)
    (g : G)
    (hn : omegaClosure T H ≤
      normalizer ((fullModule L V).map (MulAut.conj g).toMonoidHom : Set G)) :
    ChapterE.subgroupCorank (omegaClosure T H)
      (omegaClosure T H ⊓ centralizer ((fullModule L V).map (MulAut.conj g).toMonoidHom : Set G)) ≤
      3 * S.field.degree := by
  have htop : ChapterE.inducedAutomizer (fullModule L V) (normalizer (L : Set G)) = ⊤ := by
    rw [← fullModule_normalizer d,ChapterE.inducedAutomizer,subgroupOf_self]
    exact map_top_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hm := z.automizer_rank
  rw [htop,Theory.GroupTheory.primeRank_equiv 2 (Subgroup.topEquiv)] at hm
  let B := (fullModule L V).map (MulAut.conj g).toMonoidHom
  have hb : primeRank 2 (ChapterE.Automizer B) ≤ 3 * S.field.degree := by
    rw [← Theory.GroupTheory.primeRank_equiv 2
      (ChapterE.automizerMapEquiv (fullModule L V) (MulAut.conj g))]
    exact hm
  let A := ChapterE.inducedAutomizer B (omegaClosure T H)
  let : IsElementaryAbelian 2 A := ChapterE.inducedAutomizer_elementary _ _ hn
  have hc := (primeRank_le_iff_elementary_card_le (ChapterE.Automizer B)).mp hb A
    (inferInstance : IsElementaryAbelian 2 A)
  have hr := Nat.log_mono_right (b := 2) hc
  rw [Nat.log_pow (by decide : 1 < 2)] at hr
  rw [← ChapterE.rank_inducedAutomizer _ _ hn]
  exact hr

theorem source_multiplicity_one (s : Hypothesis1131At D S U₁ H)
    (e : residualStar T H ≃* SL(2,F))
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (c : QuotientCoordinates (binaryAction T H e))
    (R : Sylow 2 (residualStar T H))
    (hbudget : fixedCodim (binaryAction T H e)
      (R.mapSurjective (f := e.toMonoidHom) e.surjective) ≤ 3 * S.field.degree) :
    c.multiplicity = 1 := by
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_zmod,hF] at hd
  have he := congrArg (Nat.log 2) hd
  have hdim : Module.finrank (ZMod 2) F = 2 * S.field.degree := by
    simpa only [Nat.log_pow (by decide : 1 < 2)] using he.symm
  exact quotient_multiplicity_one (binaryAction T H e) c S.field.degree_pos hdim
    (binaryAction_moves e s.outside.1.1.2 s.moves_omega_center)
    (R.mapSurjective (f := e.toMonoidHom) e.surjective) hbudget

/-- G.1.6 coordinates collapse to one summand using the actual source automizer.
No reciprocal rank or natural-multiplicity assumption is supplied. -/
theorem source_multiplicity_one_of_geometry (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S) (z : Geometry d H)
    (e : residualStar T H ≃* SL(2,F))
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T)
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (omegaClosure T H : Set G))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ (2 * S.field.degree)))
    (c : QuotientCoordinates (binaryAction T H e))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H))) :
    c.multiplicity = 1 := by
  apply source_multiplicity_one s e hF c R
  rw [source_fixedCodim_eq_corank e R _ (hg.trans s.outside.1.1.2) hR]
  exact reciprocal_corank_budget d z g (reciprocal_normalization s g d z hF hg ha hmodel)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
