module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.Preparation
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# Reducing the actual order-32 source branch to its remaining local arguments

The proof constructs every field of the genuine I.4.5 configuration from the
selected counterexample and the residual conclusions of 14.4.4–5. The preceding
module proves the quaternion presentation of the actual U. Here characteristic
two supplies its self-centralizing core; the actual natural marking supplies
both the elementary-eight model and the PSL₃(2) quotient of L. The two core
equalities identify their literal embeddings, including the ambient center
whose centralizer is H. The quaternion inverting-action theorem then constructs
the two normal SL₂(3) factors, their intersection and their index.

`SourceLocalData` is the still-unproved local obligation. In particular, it is
not a replacement definition for the source setup. Proving it requires the
ambient normalizer/split-block exclusion and the fusion argument, rather than
a purely local normalizer-product assertion. `recognition_of_source_local`
separately retains the genuine universal I.4.5 recognition theorem. Neither
conditional consumer is claimed as a completed proof of 14.4.3.

The earlier naturality and structural/escape producers remain
`qt-d-1434-source` and `qt-d-1222-source`. Final order-32 assembly belongs to
`qt-d-14414-g2-source`; the full 14.4.14 assembly belongs to
`qt-d-14414-source`.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, 14.4.3–5,
printed pp.1007–1008, and (G1)–(G2) preceding I.4.5, printed p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The remaining source conclusions consumed by recognition. The inversion
identity uses the literal quotient by O₂(H) and the literal O²(H). No local
model, SL₂ factor, Fitting equality or ambient recognition is an input. -/
structure SourceLocalData (L : Subgroup G) (F : InvariantFlag T V 3) where
  seed_core : V = L.pCoreIn 2
  closure_core : F.U = F.H.pCoreIn 2
  quotient_card : Nat.card (HStar F.H) = 18
  inverter : F.H
  generates : pResidual 2 F.H ⊔ zpowers inverter = ⊤
  inverts : ∀ k : pResidual 2 F.H,
    QuotientGroup.mk' (pCore 2 F.H) (inverter * k * inverter⁻¹) =
      (QuotientGroup.mk' (pCore 2 F.H) k)⁻¹

variable [Finite G]

/-- Construct the genuine I.4.5 configuration on the actual H and L. The
ambient normalizer and fusion conclusions are isolated in `localData`. -/
theorem configuration_of_source_local (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) : Nonempty (G2ThreeConfiguration G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
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
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen structural alternatives F hne hZ hcard
  let eU : F.U ≃* pCore 2 F.H :=
    (subgroupOfEquivOfLe hUH).symm.trans (MulEquiv.subgroupCongr hUcore)
  have hHcentral : centralizer (pCore 2 F.H : Set F.H) ≤ pCore 2 F.H :=
    F.localKernel_characteristicTwo d.qtke L (normalizer (L : Set G)) F.H
      (h.point_mem_Hz F alternatives)
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
  exact configuration_of_quaternion_inverting_quotient F.H L (pCore 2 F.H)
    (q.map eU) hHcentral (by simpa only [index_eq_card] using localData.quotient_card)
    localData.inverter localData.generates localData.inverts
    (by rw [hz]; exact point_centralizer F hZ)
    (pCore 2 L) rfl hLcentral ⟨vmodel⟩ ⟨lmodel⟩

/-- Conditional final assembly for the selected-counterexample order-32
branch. Both the source local data and universal I.4.5 must still be proved. -/
theorem recognition_of_source_local (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F)
    (recognize : ∀ (X : Type u) [Group X] [Finite X],
      Nonempty (G2ThreeConfiguration X) → Nonempty (X ≃* Atlas.G2.Model (ZMod 3))) :
    Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) :=
  recognize G (configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
