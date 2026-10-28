module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.LocalCore
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.NonsplitStructure

/-!
# The intrinsic first core and its marked wreath action

The concrete nonsplit subgroup is the ambient image of O₂(H), where H is the
centralizer of the original z. The literal inclusion gives an equivalence
from O₂(H) to that subgroup. Restricting the original Z through H and O₂(H)
gives the correct quotient denominator; the marked equivalence with E₄ wr C₂
takes the quaternion-core image to the wreath base. The center and square-one
count are transported to O₂(H) itself.

The action uses actual H-conjugation and the proved normalization of both
cores. Its formulas retain the original quaternion embeddings and factor-swap
lift. The only input is the marked inner-model comparison: no core, quotient,
normality or action conclusion is assumed. The original natural four is also
transported through that same embedding.

Sources: Aschbacher--Smith, F.1.12(I)(13), printed p.263, and the Aut(M₁₂)
paragraph in the proof of 14.2.21, printed p.988, refs/quasithin.pdf. The
central-product convention is E.2.16, p.228. NonsplitStructure proves the
obstruction to the printed C₄ * Q₈² description.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
open Subgroup

theorem natural_eq_map (m : InnerModel) : natural = M12SmallPair.natural.map m.embedding := by
  unfold natural M12SmallPair.natural
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton,
    map_z m.embedding m.embedding_originalA m.embedding_originalB,
    map_v m.embedding m.embedding_originalA m.embedding_originalB]

/-- The original natural four, with its original marked word embedding. -/
def naturalEquiv (m : InnerModel) : M12SmallPair.natural ≃* natural :=
  (Subgroup.equivMapOfInjective _ m.embedding m.embedding_injective).trans
    (MulEquiv.subgroupCongr (natural_eq_map m).symm)

theorem natural_kleinFour (m : InnerModel) : IsKleinFour natural where
  card_four := (Nat.card_congr (naturalEquiv m).toEquiv).symm.trans M12SmallPair.card_natural
  exponent_two := (Monoid.exponent_eq_of_mulEquiv (naturalEquiv m)).symm.trans
    M12SmallPair.natural_kleinFour.exponent_two

theorem card_natural (m : InnerModel) : Nat.card natural = 4 := (natural_kleinFour m).card_four

/-- The literal two-core inside H, identified with the proved nonsplit subgroup. -/
def intrinsicCoreEquiv (m : InnerModel) : pCore 2 firstParabolic ≃* outerCore :=
  (MulEquiv.subgroupCongr (outerCore_subgroupOf_eq_pCore m).symm).trans
    (subgroupOfEquivOfLe (outerCore_le_firstParabolic m))

theorem intrinsicCoreEquiv_coe (m : InnerModel) (x : pCore 2 firstParabolic) :
    (intrinsicCoreEquiv m x).val = x.val.val := by rfl

theorem intrinsicCoreEquiv_symm_coe (m : InnerModel) (x : outerCore) :
    ((intrinsicCoreEquiv m).symm x).val.val = x.val := by rfl

/-- The original Z, restricted first to H and then to its intrinsic two-core. -/
abbrev intrinsicDistinguished : Subgroup (pCore 2 firstParabolic) :=
  (distinguished.subgroupOf firstParabolic).subgroupOf (pCore 2 firstParabolic)

/-- The original quaternion core, restricted to the intrinsic two-core. -/
abbrev intrinsicQuaternion : Subgroup (pCore 2 firstParabolic) :=
  (quaternionCore.subgroupOf firstParabolic).subgroupOf (pCore 2 firstParabolic)

theorem intrinsicDistinguished_le_center :
    intrinsicDistinguished ≤ center (pCore 2 firstParabolic) := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Subtype.ext
  change y.val.val * x.val.val = x.val.val * y.val.val
  rcases (mem_distinguished x.val.val).mp hx with h | h
  · simp [h]
  · rw [h]
    exact mem_centralizer_singleton_iff.mp y.val.property

instance intrinsicDistinguished_normal : intrinsicDistinguished.Normal :=
  ⟨fun x hx g => by
    rw [mem_center_iff.mp (intrinsicDistinguished_le_center hx) g, mul_inv_cancel_right]
    exact hx⟩

theorem intrinsicCoreEquiv_subgroupOf (m : InnerModel) (S : Subgroup Carrier) :
    ((S.subgroupOf firstParabolic).subgroupOf (pCore 2 firstParabolic)).map
      (intrinsicCoreEquiv m).toMonoidHom = S.subgroupOf outerCore := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨(intrinsicCoreEquiv m).symm x,hx,(intrinsicCoreEquiv m).apply_symm_apply x⟩

/-- The quotient comparison induced by the literal subgroup identification. -/
def intrinsicQuotientEquiv (m : InnerModel) :
    (pCore 2 firstParabolic) ⧸ intrinsicDistinguished ≃* OuterQuotient :=
  QuotientGroup.congr _ _ (intrinsicCoreEquiv m)
    (intrinsicCoreEquiv_subgroupOf m distinguished)

/-- Source O₂(H)/Z ≃ E₄ wr C₂, with Z interpreted inside O₂(H). -/
def intrinsicCoreQuotientEquiv (m : InnerModel) :
    (pCore 2 firstParabolic) ⧸ intrinsicDistinguished ≃* QuaternionSwapModel.W :=
  (intrinsicQuotientEquiv m).trans (outerQuotientEquiv m)

/-- The marked wreath quotient map on the intrinsic two-core. -/
def intrinsicWreathMap (m : InnerModel) :
    pCore 2 firstParabolic →* QuaternionSwapModel.W :=
  (outerWreathMap m).comp (intrinsicCoreEquiv m).toMonoidHom

theorem intrinsicCoreQuotientEquiv_mk (m : InnerModel) (x : pCore 2 firstParabolic) :
    intrinsicCoreQuotientEquiv m (QuotientGroup.mk' intrinsicDistinguished x) =
      intrinsicWreathMap m x := by rfl

theorem intrinsicWreathMap_base (m : InnerModel) :
    intrinsicQuaternion.map (intrinsicWreathMap m) = QuaternionSwapModel.base := by
  unfold intrinsicWreathMap
  rw [← Subgroup.map_map, intrinsicCoreEquiv_subgroupOf]
  exact outerWreathMap_base m

theorem intrinsicCoreQuotientEquiv_base (m : InnerModel) :
    (intrinsicQuaternion.map (QuotientGroup.mk' intrinsicDistinguished)).map
      (intrinsicCoreQuotientEquiv m).toMonoidHom = QuaternionSwapModel.base := by
  rw [Subgroup.map_map]
  exact intrinsicWreathMap_base m

theorem intrinsicCore_center (m : InnerModel) :
    center (pCore 2 firstParabolic) = intrinsicDistinguished := by
  apply le_antisymm _ intrinsicDistinguished_le_center
  intro x hx
  have h := (Subgroup.centerCongr (intrinsicCoreEquiv m) ⟨x,hx⟩).property
  change intrinsicCoreEquiv m x ∈ center outerCore at h
  rw [center_outerCore_eq m] at h
  exact h

theorem card_intrinsicCore_center (m : InnerModel) :
    Nat.card (center (pCore 2 firstParabolic)) = 2 := by
  rw [Nat.card_congr (Subgroup.centerCongr (intrinsicCoreEquiv m)).toEquiv]
  exact card_center_outerCore m

theorem intrinsicDistinguished_image (m : InnerModel) :
    intrinsicDistinguished.map
      (firstParabolic.subtype.comp (pCore 2 firstParabolic).subtype) = distinguished := by
  calc
    _ = (intrinsicDistinguished.map (intrinsicCoreEquiv m).toMonoidHom).map
        outerCore.subtype := (Subgroup.map_map _ _ _).symm
    _ = (distinguished.subgroupOf outerCore).map outerCore.subtype := by
      rw [intrinsicCoreEquiv_subgroupOf]
    _ = _ := map_subgroupOf_eq_of_le distinguished_le_outerCore

theorem intrinsicCore_center_image (m : InnerModel) :
    (center (pCore 2 firstParabolic)).map
      (firstParabolic.subtype.comp (pCore 2 firstParabolic).subtype) = distinguished := by
  rw [intrinsicCore_center m, intrinsicDistinguished_image m]

theorem card_square_one_intrinsicCore (m : InnerModel) :
    Nat.card {x : pCore 2 firstParabolic // x ^ 2 = 1} = 20 := by
  let e := intrinsicCoreEquiv m
  let f := Equiv.subtypeEquiv (p := fun x => x ^ 2 = 1) (q := fun x => x ^ 2 = 1)
    e.toEquiv (fun x => by
      change x ^ 2 = 1 ↔ (e x) ^ 2 = 1
      rw [← map_pow, ← map_one e]
      exact e.injective.eq_iff.symm)
  rw [Nat.card_congr f]
  exact card_square_one_outerCore m

theorem intrinsicCore_not_equiv_split (m : InnerModel) :
    ¬ Nonempty (pCore 2 firstParabolic ≃* QuaternionSwapModel.QH) := by
  rintro ⟨e⟩
  exact outerCore_not_equiv_split m ⟨(intrinsicCoreEquiv m).symm.trans e⟩

/-- Actual H-conjugation in wreath coordinates; both normalization facts are proved. -/
def wreathAction (m : InnerModel) : firstParabolic →* MulAut QuaternionSwapModel.W :=
  outerWreathAction m (firstParabolic_normalizes_outerCore m)

theorem wreathAction_evaluation (m : InnerModel) (h : firstParabolic) (x : outerCore) :
    wreathAction m h (outerWreathMap m x) =
      outerWreathMap m (outerConjugation (firstParabolic_normalizes_outerCore m) h x) :=
  outerWreathAction_evaluation m (firstParabolic_normalizes_outerCore m) h x

/-- Evaluation on intrinsic core representatives is their actual H-conjugation. -/
theorem wreathAction_intrinsic_evaluation (m : InnerModel) (h : firstParabolic)
    (x : pCore 2 firstParabolic) :
    wreathAction m h (intrinsicWreathMap m x) =
      intrinsicWreathMap m (MulAut.conjNormal h x) := by
  change wreathAction m h (outerWreathMap m (intrinsicCoreEquiv m x)) = _
  rw [wreathAction_evaluation]
  rfl

theorem wreathAction_base (m : InnerModel) (h : firstParabolic) :
    QuaternionSwapModel.base.map (wreathAction m h).toMonoidHom =
      QuaternionSwapModel.base :=
  outerWreathAction_base m (firstParabolic_normalizes_outerCore m)
    (firstParabolic_normalizes_quaternionCore m) h

theorem wreathAction_left (m : InnerModel) (h : firstParabolic) (q : QuaternionGroup 2) :
    wreathAction m h
      (QuaternionSwapModel.wreathMap (QuaternionSwapModel.leftEmbedding q)) =
        outerWreathMap m (outerConjugation (firstParabolic_normalizes_outerCore m) h (outerLeft q)) :=
  outerWreathAction_left m (firstParabolic_normalizes_outerCore m) h q

theorem wreathAction_right (m : InnerModel) (h : firstParabolic) (q : QuaternionGroup 2) :
    wreathAction m h
      (QuaternionSwapModel.wreathMap (QuaternionSwapModel.rightEmbedding q)) =
        outerWreathMap m (outerConjugation (firstParabolic_normalizes_outerCore m) h (outerRight q)) :=
  outerWreathAction_right m (firstParabolic_normalizes_outerCore m) h q

theorem wreathAction_swap_left (m : InnerModel) (q : QuaternionGroup 2) :
    wreathAction m swapActor
      (QuaternionSwapModel.wreathMap (QuaternionSwapModel.leftEmbedding q)) =
        QuaternionSwapModel.wreathMap (QuaternionSwapModel.rightEmbedding q) :=
  outerWreathAction_swap_left m (firstParabolic_normalizes_outerCore m) q

theorem wreathAction_swap_right (m : InnerModel) (q : QuaternionGroup 2) :
    wreathAction m swapActor
      (QuaternionSwapModel.wreathMap (QuaternionSwapModel.rightEmbedding q)) =
        QuaternionSwapModel.wreathMap (QuaternionSwapModel.leftEmbedding q) :=
  outerWreathAction_swap_right m (firstParabolic_normalizes_outerCore m) q

/-- Conjugation by H descends to the actual intrinsic central quotient. -/
def intrinsicQuotientAction (m : InnerModel) :
    firstParabolic →* MulAut ((pCore 2 firstParabolic) ⧸ intrinsicDistinguished) := by
  letI : intrinsicDistinguished.Characteristic := by
    rw [← intrinsicCore_center m]
    infer_instance
  exact (Subgroup.quotientAut intrinsicDistinguished).comp MulAut.conjNormal

theorem intrinsicQuotientAction_mk (m : InnerModel) (h : firstParabolic)
    (x : pCore 2 firstParabolic) :
    intrinsicQuotientAction m h (QuotientGroup.mk' intrinsicDistinguished x) =
      QuotientGroup.mk' intrinsicDistinguished (MulAut.conjNormal h x) := by
  let : intrinsicDistinguished.Characteristic := by
    rw [← intrinsicCore_center m]
    infer_instance
  unfold intrinsicQuotientAction
  exact Subgroup.quotientAut_apply_mk _ _ x

/-- The marked wreath equivalence intertwines the two actual conjugation actions. -/
theorem wreathAction_intrinsicQuotientEquiv (m : InnerModel) (h : firstParabolic)
    (x : (pCore 2 firstParabolic) ⧸ intrinsicDistinguished) :
    wreathAction m h (intrinsicCoreQuotientEquiv m x) =
      intrinsicCoreQuotientEquiv m (intrinsicQuotientAction m h x) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective intrinsicDistinguished x
  rw [intrinsicQuotientAction_mk, intrinsicCoreQuotientEquiv_mk, intrinsicCoreQuotientEquiv_mk]
  exact wreathAction_intrinsic_evaluation m h x

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
