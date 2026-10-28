module
public import Theory.GroupTheory.SylowCharacteristicNormalizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.ElementaryClosure
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer
/-!
# Stability of the original J₄ pair's local overgroups

The literal max1 and max4 groups are the proved ambient normalizers of
subgroups characteristic in their Sylows. Consequently every automorphism
preserving the original full Sylow preserves either local group. For the
order-two canonical closure, its restriction is exactly the Sylow center,
so the same conclusion holds for its actual normalizer.

The proof uses the actual normalizer equalities rather than maximality of
an arbitrary overgroup. These are the compatible actor lifts required by
Aschbacher–Smith, Proposition 1.3.4, printed p.511.
-/

public section
open Subgroup
open Janko4 Janko4.Cardinality Janko4.LocalStructure
open Janko4.LocalStructure.SymmetricLinear
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
open Max4Conjugacy.SylowCover
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel max4Subgroup

/-- The literal Mathieu overgroup is preserved with its full Sylow. -/
theorem literal_max1_stable (S : Sylow 2 Model)
    (hSM : S.toSubgroup ≤ max1Subgroup matrixA_mul_self matrixB_pow_four)
    (b : MulAut Model) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ max1Subgroup matrixA_mul_self matrixB_pow_four ↔
      x ∈ max1Subgroup matrixA_mul_self matrixB_pow_four := by
  let M := max1Subgroup matrixA_mul_self matrixB_pow_four
  let N := localKernel matrixA_mul_self matrixB_pow_four
  have hNM : normalizer (N.map M.subtype : Set Model) = M := by
    apply le_antisymm normalizer_embedded_localKernel_le_max1
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      N.le_normalizer_map M.subtype
  apply stable_of_sylow_characteristic_normalizer N
    (IsPGroup.of_card (n := 11) (localKernel_card _ _))
    localKernel_sylow_characteristic S M hSM (MulEquiv.refl M) ?_ b hb
  change normalizer (N.map M.subtype : Set Model) = M
  exact hNM

/-- The literal symmetric-linear overgroup is preserved with its full Sylow. -/
theorem literal_max4_stable (S : Sylow 2 Model) (hSM : S.toSubgroup ≤ max4Subgroup)
    (b : MulAut Model) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ max4Subgroup ↔ x ∈ max4Subgroup := by
  let N := NormalEight.eight
  let _ : N.Normal := NormalEight.normal_eight
  let _ : IsElementaryAbelian 2 N := NormalEight.elementary_eight
  have hp : IsPGroup 2 N := IsElementaryAbelian.isPGroup 2 N
  have hchar (P : Sylow 2 max4Subgroup) : (N.subgroupOf P.toSubgroup).Characteristic := by
    have hle := hp.le_sylow_of_normal P
    apply max4SylowElementaryEightCharacteristic P (N.subgroupOf P.toSubgroup)
      inferInstance (IsElementaryAbelian.subgroupOf hle)
    exact (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans NormalEight.card_eight
  apply stable_of_sylow_characteristic_normalizer N hp hchar S max4Subgroup hSM
    (MulEquiv.refl max4Subgroup) ?_ b hb
  change normalizer (MatrixNormalizerBounds.max4Eight : Set Model) = max4Subgroup
  exact MatrixNormalizerBounds.max4_eight_normalizer_eq

/-- The normalizer of the order-two source closure is preserved with the original Sylow. -/
theorem closure_two_normalizer_stable (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : S.toSubgroup ≤ H) (hcore : pCore 2 H ≠ ⊥)
    (hc : Nat.card (elementaryClosure S H hSH) = 2)
    (b : MulAut Model) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ normalizer (elementaryClosure S H hSH : Set Model) ↔
      x ∈ normalizer (elementaryClosure S H hSH : Set Model) := by
  let A := elementaryClosure S H hSH
  have hAS : A ≤ S.toSubgroup := elementaryClosure_le_sylow S H hSH hcore
  have hn : (A.subgroupOf S.toSubgroup).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAS).mpr
      (hSH.trans (overgroup_le_elementaryClosure_normalizer S H hSH))
  let _ := hn
  have hcard : Nat.card (A.subgroupOf S.toSubgroup) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv).trans hc
  have hcenter : A.subgroupOf S.toSubgroup ≤ center S :=
    central_of_normal_card_two _ hcard
  have hZ : Nat.card (center S) = 2 := by
    let e : S.subtype hSH ≃* S := subgroupOfEquivOfLe hSH
    rw [← Nat.card_congr (centerCongr e).toEquiv]
    exact restricted_sylow_center_card S H hSH
  have heq : A.subgroupOf S.toSubgroup = center S :=
    eq_of_le_of_card_ge hcenter (by rw [hZ, hcard])
  have hchar : (A.subgroupOf S.toSubgroup).Characteristic := by rw [heq]; infer_instance
  let _ := hchar
  exact stable_normalizer_of_characteristic_subgroupOf S.toSubgroup A hAS b hb

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
