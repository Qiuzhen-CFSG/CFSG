module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.NonquasisimpleFactorization.Action
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.Representation.ElementaryAbelianAction
/-!
# The marked plus representation and its induced Tᵥ action

Construct the faithful binary representation on the literal W_K from
plusAction. The full offender subgroup satisfies native B.5.3: its finite
SQTK cover is the inverse image in the actual plus actor. The adequate
B.5.6 implication therefore gives its complete source-correct alternatives,
without selecting a natural summand or asserting a splitting of W_K.

The Tᵥ conjugation action on K⁺ is transported through the specified model
equivalence, and an equivariance formula retains componentPlusMap. Stability
of a model subgroup then gives normalization of its literal embedded
preimage. In particular the point/line application uses no local-family
membership, so it is independent of LocalStructure's normalization input.

The classification-to-type-preservation implication is still required:
Sylow marking by itself does not exclude the graph automorphism interchanging
the two flag types. No type-preservation premise here is asserted to follow
from the classification application. Final discharge belongs to the marked
action assembly, followed by qt-13-06-higher-field-sl3-parabolics. The
universal B.5 input and earlier ambient hypotheses remain with
qt-13-06-centralizer-reduction and their existing source owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph preceding 13.6.14, printed p.929, and 13.6.19, p.931;
B.5.3–6, printed pp.104–105.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection
universe u
variable {G : Type u} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- The full faithful representation of the literal plus quotient on W_K. -/
def plusRepresentation [IsElementaryAbelian 2 (WK K L T z v)] :
    Representation (ZMod 2) (Gplus K L T z v hL hz) (Additive (WK K L T z v)) := by
  let _ := MulDistribMulAction.compHom (WK K L T z v) (plusAction K L T z v hL hz)
  exact Representation.ofElementaryAbelianAction

theorem plusRepresentation_apply [IsElementaryAbelian 2 (WK K L T z v)]
    (a : plusActor K L T v) (w : WK K L T z v) :
    (((plusRepresentation K L T z v hL hz (plusMk K L T z v hL hz a)
      (Additive.ofMul w)).toMul : WK K L T z v) : G) =
        (a : G) * (w : G) * (a : G)⁻¹ := rfl

theorem plusRepresentation_faithful [IsElementaryAbelian 2 (WK K L T z v)] :
    Function.Injective (plusRepresentation K L T z v hL hz) := by
  intro a b he
  apply plusAction_injective K L T z v hL hz
  apply MulEquiv.ext
  intro w
  exact Additive.ofMul.injective (LinearMap.congr_fun he (Additive.ofMul w))

/-- B.5.3 applies to the whole offender subgroup of the actual plus action.
The SQTK cover is the inverse image in the original plus actor, which is
contained in Gᵥ. In particular the actor is not replaced by its component. -/
theorem plus_offender_hypothesis [Finite G]
    [IsElementaryAbelian 2 (WK K L T z v)]
    {𝒦 : GroupClass.{u}} (hSQ : IsSQTK 𝒦 (Gv v)) (hK : K ≤ Gv v)
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    ChapterB.SourceInduction.FFHypothesis 𝒦
      ((plusRepresentation K L T z v hL hz).comp
        (offenderSubgroup (plusRepresentation K L T z v hL hz)).subtype) := by
  let : Module.Finite (ZMod 2) (Additive (WK K L T z v)) := Module.Finite.of_finite
  have hA : IsSQTK 𝒦 (plusActor K L T v) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (plusActor_le_Gv K L T v hK))).mp
      (hSQ.subgroup ((plusActor K L T v).subgroupOf (Gv v)))
  have h := NonquasisimpleFactorization.offender_hypothesis
    (plusRepresentation K L T z v hL hz) (plusMk K L T z v hL hz)
    (plusMk_surjective K L T z v hL hz) hA
    (plusRepresentation_faithful K L T z v hL hz) hcore
  refine ⟨h.finite_module, h.faithful, h.twoCore, h.generated, ?_⟩
  obtain ⟨d⟩ := h.quotient
  let := d.coverGroup
  let := d.coverFinite
  let := d.kernelNormal
  exact ⟨{ Cover := d.Cover, kernel := d.kernel, sqtk := d.sqtk, equiv := d.equiv }⟩

/-- Source-correct B.5.6 application, retaining its entire adequate action
catalogue (including repeated and extension alternatives). Only the universal
source implication is left explicit. -/
theorem plus_offender_classification [Finite G]
    [IsElementaryAbelian 2 (WK K L T z v)]
    {𝒦 : GroupClass.{u}}
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v)) (hK : K ∈ Yz L T z v)
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    ChapterB.SourceInduction.AdequateAlternative
      ((plusRepresentation K L T z v hL hz).comp
        (offenderSubgroup (plusRepresentation K L T z v hL hz)).subtype) :=
  source _ _ _ (plus_offender_hypothesis K L T z v hL hz hSQ hK.1.1 hcore)

/-- The original Tᵥ map to the plus quotient. -/
def plusTvMap : Tv T v →* Gplus K L T z v hL hz :=
  (plusMk K L T z v hL hz).comp (inclusion le_sup_right)

private theorem plusTv_normalizes_component
    (hn : Tv T v ≤ normalizer (K : Set G)) (t : Tv T v) :
    plusTvMap K L T z v hL hz t ∈ normalizer
      (plusImage K L T z v hL hz K : Set _) := by
  let q := plusMk K L T z v hL hz
  have hconj (t : Tv T v) (x : Gplus K L T z v hL hz)
      (hx : x ∈ plusImage K L T z v hL hz K) :
      plusTvMap K L T z v hL hz t * x * (plusTvMap K L T z v hL hz t)⁻¹ ∈
        plusImage K L T z v hL hz K := by
    obtain ⟨k, hk, rfl⟩ := hx
    let a : plusActor K L T v := inclusion le_sup_right t
    have hka : (a : G) * (k : G) * (a : G)⁻¹ ∈ K :=
      (mem_normalizer_iff.mp (hn t.property) k).mp hk
    exact mem_map.mpr ⟨a * k * a⁻¹, hka, by simp only [map_mul, map_inv]; rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hconj t x
  · intro hx
    have h := hconj t⁻¹ _ hx
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using h

/-- The action on K⁺ induced by the actual Tᵥ conjugation. -/
def componentPlusAction (hn : Tv T v ≤ normalizer (K : Set G)) :
    Tv T v →* MulAut (plusImage K L T z v hL hz K) :=
  (plusImage K L T z v hL hz K).normalizerMonoidHom.comp
    ((plusTvMap K L T z v hL hz).codRestrict _
      (by exact plusTv_normalizes_component K L T z v hL hz hn))

/-- The same action transported through the specified aligned model. -/
def modelAction {D : Type*} [Group D]
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* D) : Tv T v →* MulAut D :=
  (MulAut.congr e).toMonoidHom.comp (componentPlusAction K L T z v hL hz hn)

/-- Equivariance retains the literal component quotient map. -/
theorem modelAction_componentPlusMap {D : Type*} [Group D]
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* D) (t : Tv T v) (k : K) :
    modelAction K L T z v hL hz hn e t (e (componentPlusMap K L T z v hL hz k)) =
      e (componentPlusMap K L T z v hL hz
        (K.normalizerMonoidHom (inclusion hn t) k)) := by
  change e (componentPlusAction K L T z v hL hz hn t
    (e.symm (e (componentPlusMap K L T z v hL hz k)))) = _
  rw [e.symm_apply_apply]
  apply congrArg e
  apply Subtype.ext
  let q := plusMk K L T z v hL hz
  let a : plusActor K L T v := inclusion
    (show Tv T v ≤ plusActor K L T v from le_sup_right) t
  let b : plusActor K L T v := inclusion (K_le_plusActor K L T v) k
  change q a * q b * (q a)⁻¹ = q (a * b * a⁻¹)
  simp only [map_mul, map_inv]


/-- Type preservation in the marked model gives normalization of the actual
preimage. It does not use local-family membership of that preimage. -/
theorem preimage_normalized_of_modelAction {D : Type*} [Group D]
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* D) (P : Subgroup D)
    (hP : ∀ t : Tv T v, P.map (modelAction K L T z v hL hz hn e t).toMonoidHom = P) :
    Tv T v ≤ normalizer (preimageIn K
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) P : Set G) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  obtain ⟨k, hk, rfl⟩ := hx
  let a : Tv T v := ⟨t, ht⟩
  let k' := K.normalizerMonoidHom (inclusion hn a) k
  refine mem_map.mpr ⟨k', ?_, rfl⟩
  change e (componentPlusMap K L T z v hL hz k') ∈ P
  rw [← modelAction_componentPlusMap K L T z v hL hz hn e a k]
  rw [← hP a]
  exact mem_map_of_mem _ hk

open scoped MatrixGroups
/-- Once the classified marked action preserves both flag types, their
literal source preimages are Tᵥ-invariant. Local-family membership is not
used, so this interface can feed the independent local-structure producer. -/
theorem flagPreimages_normalized_of_modelAction
    {F : Type*} [Field F] [Finite F]
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hp : ∀ t : Tv T v, (Matrix.PSL3.LinearThree.pointParabolicSL F).map
      (modelAction K L T z v hL hz hn e t).toMonoidHom =
        Matrix.PSL3.LinearThree.pointParabolicSL F)
    (hl : ∀ t : Tv T v, (Matrix.PSL3.LinearThree.lineParabolicSL F).map
      (modelAction K L T z v hL hz hn e t).toMonoidHom =
        Matrix.PSL3.LinearThree.lineParabolicSL F) :
    Tv T v ≤ normalizer (pointPreimage F K L T z v hL hz e : Set G) ∧
      Tv T v ≤ normalizer (linePreimage F K L T z v hL hz e : Set G) :=
  ⟨preimage_normalized_of_modelAction K L T z v hL hz hn e _ hp,
    preimage_normalized_of_modelAction K L T z v hL hz hn e _ hl⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
