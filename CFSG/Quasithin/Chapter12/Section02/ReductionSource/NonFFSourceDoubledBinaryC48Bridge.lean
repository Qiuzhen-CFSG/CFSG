module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC28
public import CFSG.Quasithin.ChapterC.Section04.ParabolicModules.BinaryThreeNaturalDualExclusion
public import Theory.Representation.BinaryNaturalDual.BinaryLinearThreeBridge
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality

/-!
# The original reciprocal witness and the binary C.4.8 module rows

The retained witness identifies its actual intersection residual LH/O₂(LH)
with L/O₂(L), compatibly with inclusion on every representative. Composing
that map with the original seed marking gives the natural-plus-dual action
on the whole source orbit, retaining the seed and its selected conjugate
as the two coordinate axes.

The checked matrix-to-linear comparison removes the model-bridge premise
from the repeated-natural exclusion. The independently marked quotient
LH R/R is retained literally. The orthogonal row has an impossible L₄(2)
actor, and the double-cover A₈ row has the wrong module dimension. The last
consumer constructs the original reciprocal witness and C.2.8 input before
applying these exclusions. The C.4.8 classification producing the rows and
the native J₄ cover remain explicit premises of that consumer.

Source: Aschbacher--Smith C.4.8(2),(9), printed pp.153--154; 4.2.12--13 and
4.4.3(i.a), printed pp.610--612,619, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open ChapterC.Section04.BinaryThreeNaturalDualExclusion
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private def binaryThreeModelBridge : ModelBridge where
  actor := slEquivLinear 3
  coordinates := LinearEquiv.refl _ _
  intertwines := by
    intro g v
    exact (LinearMap.congr_fun
      (BinaryLinearThree.NaturalDual.naturalDualRepresentation_slEquivLinear g) v).symm

/-- The literal residual quotient acts naturally and contragrediently on the
same two original summands; the quotient equation retains ambient inclusion. -/
theorem sourceOrbit_binary_witness_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* BinaryLinearThree.Group, Function.Surjective q ∧ q.ker = pCore 2 L ∧
      ∃ e : (LH ⧸ pCore 2 LH) ≃* BinaryLinearThree.Group,
        (∀ l : LH, e (QuotientGroup.mk' (pCore 2 LH) l) = q (inclusion hLH l)) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space,
        (∀ l v, E (doubledSeedAction LH D.sourceOrbit
          (hLH.trans D.sourceOrbit_component_normalizes) l v) =
            BinaryLinearThree.NaturalDual.action (e (QuotientGroup.mk' (pCore 2 LH) l)) (E v)) ∧
        (∀ v, (E v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, (E v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  obtain ⟨t,ht,hnt,q,hq,hk,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_quotient_coordinates h hd F hF hmodel
  rcases hw with ⟨_,_,_,_,_,_,_,_,_,_,_,⟨f,hf⟩,_⟩
  let b : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let e := f.trans b
  have he (l : LH) : e (QuotientGroup.mk' (pCore 2 LH) l) = q (inclusion hLH l) := by
    change b (f (QuotientGroup.mk' _ l)) = _
    rw [hf]
    rfl
  refine ⟨t,ht,hnt,q,hq,hk,e,he,E,?_,hV,hVt⟩
  intro l v
  rw [he]
  exact hE (inclusion hLH l) v

/-- No repeated-natural marking exists on the original reciprocal witness.
Neither a model-comparison premise nor a residual-coverage premise is needed,
and the proposed quotient marking may be independent of the original one. -/
theorem sourceOrbit_binary_witness_no_repeated_natural
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let R := J.pCoreIn 2
    let hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
    let := normal_subgroupOf_sup_of_le_normalizer
      ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
        hw.2.2.2.2.2.2.1.span_normalizes_radical)
    ∀ (d : ℕ), d = 3 ∨ d = 4 →
    ∀ (a : ((LH ⊔ R : Subgroup G) ⧸ R.subgroupOf (LH ⊔ R)) ≃* LinearGroup d)
      (m : ℕ), 0 < m →
      ∀ N : Additive D.sourceOrbit ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space d),
        (∀ l v, N (doubledSeedAction LH D.sourceOrbit
          (hLH.trans D.sourceOrbit_component_normalizes) l v) =
            fun i => a (radicalQuotientMap LH R l) (N v i)) → False := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  let := normal_subgroupOf_sup_of_le_normalizer
    ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hw.2.2.2.2.2.2.1.span_normalizes_radical)
  dsimp only
  intro d hdims a m hm N hN
  obtain ⟨_,_,_,q,_,_,e,_,E,hE,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  exact no_radical_quotient_natural_marking LH R D.sourceOrbit binaryThreeModelBridge
    (hLH.trans D.sourceOrbit_component_normalizes)
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) E hE d hdims a m hm N hN

/-- The orthogonal C.4.8 row has the wrong intrinsic actor: the original
residual quotient has order 168, whereas the binary degree-four group has
order 20160. No hypothesis about a quadratic form is required. -/
theorem sourceOrbit_binary_witness_not_linearFour
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ¬ Nonempty ((LH ⧸ pCore 2 LH) ≃* LinearGroup 4) := by
  dsimp only
  obtain ⟨_,_,_,_,_,_,e,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  rintro ⟨a⟩
  have hcard := Nat.card_congr (e.symm.trans a).toEquiv
  have h3 : Nat.card BinaryLinearThree.Group = 168 := Matrix.PSL3Two.card_SL
  have h4 : Nat.card (LinearGroup 4) = 20160 := by
    calc
      Nat.card (LinearGroup 4) = BinaryLinear.order 4 :=
        BinaryLinear.card_GL_of_finrank (by simp [BinaryLinear.OuterCyclic.Space])
      _ = 20160 := by decide
  omega

/-- The possible module conclusions of the binary-three rows of C.4.8.
The orthogonal alternative records only its necessary actor marking; the
double-cover alternative records its necessary dimension. -/
@[expose] def WitnessC48ModuleAlternatives
    {A J H U : Subgroup G} (hw : Witness L V A J H U) : Prop :=
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  let := normal_subgroupOf_sup_of_le_normalizer
    ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hw.2.2.2.2.2.2.1.span_normalizes_radical)
  (∃ d : ℕ, (d = 3 ∨ d = 4) ∧
    ∃ a : ((LH ⊔ R : Subgroup G) ⧸ R.subgroupOf (LH ⊔ R)) ≃* LinearGroup d,
    ∃ m : ℕ, 0 < m ∧
    ∃ N : Additive D.sourceOrbit ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space d),
      ∀ l v, N (doubledSeedAction LH D.sourceOrbit
        (hLH.trans D.sourceOrbit_component_normalizes) l v) =
          fun i => a (radicalQuotientMap LH R l) (N v i)) ∨
  Nonempty ((LH ⧸ pCore 2 LH) ≃* LinearGroup 4) ∨
  Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 4

/-- All binary-three module consequences of C.4.8 are excluded on the actual
six-dimensional orbit, including the rank-four double-cover alternative. -/
theorem sourceOrbit_binary_witness_c48_rows_false
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hrows : D.WitnessC48ModuleAlternatives hw) : False := by
  rcases hrows with ⟨d,hdims,a,m,hm,N,hN⟩ | hfour | hdim
  · exact D.sourceOrbit_binary_witness_no_repeated_natural h hd F hF hmodel hw
      d hdims a m hm N hN
  · exact D.sourceOrbit_binary_witness_not_linearFour h hd F hF hmodel hw hfour
  · have hsix := D.sourceOrbit_binary_dimension h hd F hF hmodel
    omega

/-- Original multiple-overgroup application. The source producer supplies
C.2.8 on the whole orbit and escape at the same selected witness. Only the
independent J₄ cover and the source classification forcing the rows remain. -/
theorem sourceOrbit_binary_reciprocal_false_of_c48_rows
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hclass : ∀ {A J H U : Subgroup G} (hw : Witness L V A J H U),
      D.sourceOrbit ≤ J.pCoreIn 2 →
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L →
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
        (H ⊓ normalizer (L : Set G))
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
        (J.pCoreIn 2) D.sourceOrbit →
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H →
      D.WitnessC48ModuleAlternatives hw) : False := by
  obtain ⟨_,_,_,_,_,A,_,_,_,_,_,J,H,U,hw,hWJ,hJC,hc,hescape⟩ :=
    D.sourceOrbit_binary_reciprocal_hypothesisC28_of_janko_cover
      hnative h hd hmany hnon F hF hmodel
  exact D.sourceOrbit_binary_witness_c48_rows_false h hd F hF hmodel hw
    (hclass hw hWJ hJC hc hescape)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
