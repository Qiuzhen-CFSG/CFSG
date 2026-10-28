module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Ordinary
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedMathieu
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedHeld

/-!
# Mathieu and Held exclusions for the original ordinary component

The whole original natural-plus-dual six-space has no fixed points under
its literal intersection residual. Its map through the full component
center is therefore injective, even though that center can be a two-group.
The original perfect residual and its SL₃(2) quotient preserve this exact
module marking. The native Mathieu and Held normalizer calculations exclude
both central quotient models.

Source: Aschbacher--Smith C.4.5--8, printed pp.151--154, and the local
module inspection of 4.4.12, printed pp.622--623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem ordinary_naturalDual_maps
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    _root_.Group.IsPerfect LH ∧
      ∃ f : LH →* K ⧸ center K, ∃ q : LH →* BinaryLinearThree.Group,
        Function.Surjective q ∧
        ∃ j : Multiplicative NaturalDual.Space →* K ⧸ center K,
          Function.Injective j ∧
          ∀ r v, f r * j (Multiplicative.ofAdd v) * (f r)⁻¹ =
            j (Multiplicative.ofAdd (NaturalDual.action (q r) v)) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let W := D.sourceOrbit
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  have hWL : W ≤ LH := hspan ▸ hc.module_le
  have hp : _root_.Group.IsPerfect LH := hspan ▸ hc.span_perfect
  let i : LH →* K := {
    toFun x := ⟨⟨x.val,hLH x.property⟩,hc.ordinary_component_contains_original K hK x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let iW := i.comp (inclusion hWL)
  let π := QuotientGroup.mk' (center K)
  have hiπ : Function.Injective (π.comp iW) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hz : iW x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
    have hxc : (x : G) ∈ centralizer (LH : Set G) := by
      intro y hy
      exact congrArg (fun z : K => ((z : H) : G)) (mem_center_iff.mp hz (i ⟨y,hy⟩))
    have he : (x : G) = 1 := mem_bot.mp
      (D.sourceOrbit_binary_witness_fixed_eq_bot h hd F hF hmodel hw ▸
        (show (x : G) ∈ W ⊓ centralizer (LH : Set G) from ⟨x.property,hxc⟩))
    exact Subtype.ext he
  obtain ⟨_,_,_,_,_,_,e,_,E,hE,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let v : Multiplicative NaturalDual.Space ≃* W :=
    E.symm.toAddEquiv.toMultiplicative.trans MulEquiv.toMultiplicative_toAdditive
  let f := π.comp i
  let j := (π.comp iW).comp v.toMonoidHom
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  refine ⟨hp,f,q,hq,j,hiπ.comp v.injective,?_⟩
  intro r x
  have hact : doubledSeedAction LH W
      (((map_subtype_le _).trans inf_le_left).trans D.sourceOrbit_component_normalizes)
      r (E.symm x) = E.symm (NaturalDual.action (q r) x) := by
    apply E.injective
    rw [hE,E.apply_symm_apply,E.apply_symm_apply]
    rfl
  have hh : r * inclusion hWL (v (Multiplicative.ofAdd x)) * r⁻¹ =
      inclusion hWL (v (Multiplicative.ofAdd (NaturalDual.action (q r) x))) :=
    Subtype.ext (congrArg (fun w : Additive W => (w.toMul : G)) hact)
  have hf := congrArg f hh
  simp only [map_mul,map_inv] at hf
  exact hf

/-- The actual ordinary component has no Mathieu M₂₄ central quotient.
The full center and whole original orbit are retained. -/
theorem sourceOrbit_binary_witness_ordinary_not_mathieu
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24) := by
  rintro ⟨m⟩
  obtain ⟨hp,f,q,hq,j,hj,ha⟩ := D.ordinary_naturalDual_maps h hd F hF hmodel hw hWJ hJC K hK
  let := hp
  apply DoubledBinaryPlacedMathieu.no_mathieu_natural_dual (m.toMonoidHom.comp f) q hq
    (m.toMonoidHom.comp j) (m.injective.comp hj)
  intro r v
  simpa only [MonoidHom.comp_apply,map_mul,map_inv] using congrArg m.toMonoidHom (ha r v)

/-- The actual ordinary component has no Held central quotient. Its complete
natural-plus-dual orbit embeds through the full component center. -/
theorem sourceOrbit_binary_witness_ordinary_not_held
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ¬ Nonempty ((K ⧸ center K) ≃* Held.He) := by
  rintro ⟨m⟩
  obtain ⟨_,f,q,hq,j,hj,ha⟩ := D.ordinary_naturalDual_maps h hd F hF hmodel hw hWJ hJC K hK
  apply DoubledBinaryPlacedHeld.no_held_natural_dual (m.toMonoidHom.comp f) q hq
    (m.toMonoidHom.comp j) (m.injective.comp hj)
  intro r v
  simpa only [MonoidHom.comp_apply,map_mul,map_inv] using congrArg m.toMonoidHom (ha r v)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
