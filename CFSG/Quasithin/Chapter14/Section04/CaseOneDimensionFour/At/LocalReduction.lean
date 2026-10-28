module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.LocalReduction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Preparation

/-!
# Reducing the actual order-32 source branch to its remaining local arguments at the original G,T

The proof constructs every field of the genuine I.4.5 configuration from the
selected counterexample and the residual conclusions of 14.4.4–5. The preceding
module proves the quaternion presentation of the actual U. Here characteristic
two supplies its self-centralizing core; the actual natural marking supplies
both the elementary-eight model and the PSL₃(2) quotient of L. The two core
equalities identify their literal embeddings, including the ambient center
whose centralizer is H. The quaternion inverting-action theorem then constructs
the two normal SL₂(3) factors, their intersection and their index.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

variable [Finite G]

/-- Construct the genuine I.4.5 configuration on the actual H and L. The
ambient normalizer and fusion conclusions are isolated in `localData`. -/
theorem configuration_on_of_source_local (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) : ∃ c : G2ThreeConfiguration G, c.H = F.H ∧ c.M = L := by
  let := setup.chosen.elementary
  let h := setup
  have hUH : F.U ≤ F.H := F.U_le_H
  have hVL : V ≤ L := localData.seed_core.le.trans (L.pCoreIn_le 2)
  have hUcore : F.U.subgroupOf F.H = pCore 2 F.H := by
    apply (map_injective F.H.subtype_injective)
    rw [map_subgroupOf_eq_of_le hUH]
    exact localData.closure_core
  have hVcore : V.subgroupOf L = pCore 2 L := by
    apply (map_injective L.subtype_injective)
    rw [map_subgroupOf_eq_of_le hVL]
    exact localData.seed_core
  obtain ⟨q⟩ := source_quaternion d setup structural alternatives F hne hZ hcard
  let eU : F.U ≃* pCore 2 F.H :=
    (subgroupOfEquivOfLe hUH).symm.trans (MulEquiv.subgroupCongr hUcore)
  have hHcentral : centralizer (pCore 2 F.H : Set F.H) ≤ pCore 2 F.H :=
    F.localKernel_characteristicTwo d.qtke L (normalizer (L : Set G)) F.H
      (h.point_mem_Hz_at F alternatives)
  have hLcentral : centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    intro x hx
    rw [← hVcore]
    change (x : G) ∈ V
    rw [localData.seed_core, ← h.centralizer_L]
    refine ⟨x.property, ?_⟩
    intro v hv
    have hv' : (⟨v, hVL hv⟩ : L) ∈ pCore 2 L := by rw [← hVcore]; exact hv
    exact congrArg L.subtype (hx ⟨v, hVL hv⟩ hv')
  have hz : (((center (pCore 2 F.H)).map (pCore 2 F.H).subtype).map F.H.subtype) =
      F.ZU := by
    rw [map_map, ← map_center_image_of_injective (pCore 2 F.H) F.H.subtype
      F.H.subtype_injective]
    change Chapter12.Section08.centerIn (F.H.pCoreIn 2) = Chapter12.Section08.centerIn F.U
    rw [← localData.closure_core]
  let eV : pCore 2 L ≃* V :=
    (MulEquiv.subgroupCongr hVcore.symm).trans (subgroupOfEquivOfLe hVL)
  let vmodel : pCore 2 L ≃* Multiplicative (Fin 3 → ZMod 2) :=
    eV.trans h.naturalMarking.coordinates.toAddEquiv.toMultiplicativeRight
  let lmodel : (L ⧸ pCore 2 L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    h.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
  obtain ⟨c, hn₁, hn₂, hi⟩ := normal_residual_factors_of_quaternion_inverting_quotient
    (pCore 2 F.H) (q.map eU) hHcentral
    (by simpa only [index_eq_card] using localData.quotient_card)
    localData.inverter localData.generates localData.inverts
  have hI : Nat.card (c.left ⊓ c.right : Subgroup F.H) = 2 := by
    rw [c.intersection, card_map_of_injective (pCore 2 F.H).subtype_injective,
      (q.map eU).center_card]
  refine ⟨{
    H := F.H, M := L, H₁ := c.left, H₂ := c.right
    H₁_normal := hn₁, H₂_normal := hn₂
    H₁_model := c.left_model, H₂_model := c.right_model
    commute := c.commute, index := hi
    intersection_model := ⟨mulEquivOfPrimeCardEq hI (by simp)⟩
    centralizer := ?_
    V := pCore 2 L, V_normal := inferInstance
    fitting := (generalizedFitting_eq_pCore_of_selfCentralizing 2 hLcentral).symm
    V_model := ⟨vmodel⟩, quotient_model := ⟨lmodel⟩ }, rfl, rfl⟩
  rw [c.intersection, hz]
  exact point_centralizer F hZ

/-- Construct the genuine I.4.5 configuration on the actual H and L. The
ambient normalizer and fusion conclusions are isolated in `localData`. -/
theorem configuration_of_source_local (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) : Nonempty (G2ThreeConfiguration G) := by
  obtain ⟨c, _, _⟩ := configuration_on_of_source_local d setup structural alternatives
    F hne hZ hcard localData
  exact ⟨c⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
