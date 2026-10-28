module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel.NonsplitGeometry
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12.Aut

/-!
# Transport of the nonsplit geometry through the recognized whole pair

The full amalgam isomorphism into Aut(M₁₂) is composed with its proved
concrete realization. Its same left map restricts to the actual two-core and
transports the literal other preimage, original marked Z, quaternion factors,
and square functional. Both inclusion equations retain the whole overlap.
The explicit cubic gives the exact conjugation premise of the core trichotomy.

In the Q=A branch, relative normality supplied by the larger local group makes
the first-parabolic quotient well-defined; its order is 384/16=24. No S₄
classification or elementary-sixteen identification is used.
Source: the corrected model calculation for Aschbacher--Smith 14.2.21,
printed p.988, refs/quasithin.pdf. Recognition and ambient rigidity remain
with their respective source assembly owners.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel.Transport
open Sporadic.Mathieu.M12ExceptionalExtension FirstParabolic Theory.GroupTheory
open SourceQuotientBridge.NonsplitOther
open scoped IsMulCommutative
variable {L B R : Type*} [Group L] [Group B] [Group R]
  {α : RankTwoAmalgam L B R}

/-- Retain both commuting squares and the entire middle group when recognizing the model. -/
def pairIso (r : RankTwoAmalgam.Iso α CFSG.Quasithin.ChapterF.GreenBook.AutMathieuTwelve.autAmalgam) :
    RankTwoAmalgam.Iso α VerifiedPair.amalgam :=
  (r.trans CFSG.Quasithin.ChapterF.GreenBook.AutMathieuTwelve.ambientIso.symm).trans CFSG.Quasithin.ChapterF.GreenBook.AutMathieuTwelve.concreteIso

variable (r : RankTwoAmalgam.Iso α CFSG.Quasithin.ChapterF.GreenBook.AutMathieuTwelve.autAmalgam)

def coreEquiv : pCore 2 L ≃* outerCore :=
  (LocalCoreTransport.coreEquiv 2 (pairIso r).left).trans (intrinsicCoreEquiv innerModel)

theorem coreEquiv_val (x : pCore 2 L) :
    (coreEquiv r x).val = ((pairIso r).left x.val).val := by
  change (intrinsicCoreEquiv innerModel
    (LocalCoreTransport.coreEquiv 2 (pairIso r).left x)).val = _
  rw [intrinsicCoreEquiv_coe, LocalCoreTransport.coreEquiv_apply]

def wreathMap : pCore 2 L →* FourWreathTwo.Wreath :=
  coreWreathMap.comp (coreEquiv r).toMonoidHom

theorem wreathMap_surjective : Function.Surjective (wreathMap r) :=
  coreWreathMap_surjective.comp (coreEquiv r).surjective

def markedCore : Subgroup (pCore 2 L) :=
  (distinguished.subgroupOf outerCore).comap (coreEquiv r).toMonoidHom

def otherCore : Subgroup (pCore 2 L) := FourWreathTwo.other.comap (wreathMap r)

theorem wreathMap_ker : (wreathMap r).ker = markedCore r := by
  rw [wreathMap, ← MonoidHom.comap_ker, coreWreathMap_ker]
  rfl

def otherEquiv : otherCore r ≃* SourceQuotientBridge.otherPreimage innerModel where
  toFun x := ⟨coreEquiv r x.val, x.property⟩
  invFun x := ⟨(coreEquiv r).symm x.val, by
    change coreWreathMap (coreEquiv r ((coreEquiv r).symm x.val)) ∈ FourWreathTwo.other
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((coreEquiv r).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((coreEquiv r).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((coreEquiv r).map_mul x.val y.val)

def otherCoordinates : otherCore r ≃* Coordinates := (otherEquiv r).trans otherPreimageEquiv

theorem otherCore_card : Nat.card (otherCore r) = 16 :=
  (Nat.card_congr (otherEquiv r).toEquiv).trans otherPreimage_card

instance otherCore_commutative : IsMulCommutative (otherCore r) where
  is_comm := ⟨fun a b => (otherCoordinates r).injective (by simp only [map_mul, mul_comm])⟩

/-- The transported z is the image of the original marked element under the same core map. -/
def markedElement : pCore 2 L := (coreEquiv r).symm outerMarked

theorem markedElement_mem : markedElement r ∈ otherCore r := by
  change coreWreathMap (coreEquiv r ((coreEquiv r).symm outerMarked)) ∈ FourWreathTwo.other
  rw [MulEquiv.apply_symm_apply]
  exact SourceQuotientBridge.NonsplitOther.marked_mem innerModel

theorem otherCoordinates_marked :
    otherCoordinates r ⟨markedElement r,markedElement_mem r⟩ = (Multiplicative.ofAdd 2,1) := by
  change otherPreimageEquiv (otherEquiv r ⟨markedElement r,markedElement_mem r⟩) = _
  have he : otherEquiv r ⟨markedElement r,markedElement_mem r⟩ =
      ⟨outerMarked,SourceQuotientBridge.NonsplitOther.marked_mem innerModel⟩ :=
    Subtype.ext ((coreEquiv r).apply_symm_apply outerMarked)
  rw [he]
  exact otherPreimageEquiv_marked

def markedEquiv : markedCore r ≃* distinguished where
  toFun x := ⟨(coreEquiv r x.val).val,x.property⟩
  invFun x := ⟨(coreEquiv r).symm ⟨x.val,distinguished_le_outerCore x.property⟩, by
    change (coreEquiv r ((coreEquiv r).symm _)).val ∈ distinguished
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((coreEquiv r).symm_apply_apply x.val)
  right_inv x := Subtype.ext (congrArg (fun y : outerCore => y.val) ((coreEquiv r).apply_symm_apply _))
  map_mul' x y := Subtype.ext (congrArg (fun a : outerCore => a.val) ((coreEquiv r).map_mul x.val y.val))

abbrev otherZ : Subgroup (otherCore r) := (markedCore r).subgroupOf (otherCore r)

instance otherZ_normal : (otherZ r).Normal := inferInstanceAs
  (((distinguished.subgroupOf outerCore).comap (coreEquiv r).toMonoidHom).subgroupOf
    (otherCore r)).Normal

theorem otherZ_map : (otherZ r).map (otherEquiv r).toMonoidHom = otherMarkedSubgroup := by
  change (otherMarkedSubgroup.comap (otherEquiv r).toMonoidHom).map
    (otherEquiv r).toMonoidHom = otherMarkedSubgroup
  exact Subgroup.map_comap_eq_self_of_surjective (otherEquiv r).surjective _

def quotientEquiv : (otherCore r ⧸ otherZ r) ≃* OtherQuotient :=
  QuotientGroup.congr (otherZ r) (markedSubgroup innerModel) (otherEquiv r) (otherZ_map r)

theorem quotientEquiv_mk (x : otherCore r) :
    quotientEquiv r (QuotientGroup.mk' (otherZ r) x) =
      QuotientGroup.mk' otherMarkedSubgroup (otherEquiv r x) := rfl

theorem quotient_card : Nat.card (otherCore r ⧸ otherZ r) = 8 :=
  (Nat.card_congr (quotientEquiv r).toEquiv).trans otherQuotient_card

instance quotient_elementary : IsElementaryAbelian 2 (otherCore r ⧸ otherZ r) where
  is_comm := ⟨fun a b => (quotientEquiv r).injective (by simp only [map_mul, mul_comm])⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
    apply (quotientEquiv r).injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 OtherQuotient) _)

/-- The transported functional has values in the actual transported Z. -/
def squareMap : (otherCore r ⧸ otherZ r) →* markedCore r :=
  (markedEquiv r).symm.toMonoidHom.comp (otherSquare.comp (quotientEquiv r).toMonoidHom)

theorem squareMap_mk (x : otherCore r) :
    (squareMap r (QuotientGroup.mk' (otherZ r) x)).val = x.val ^ 2 := by
  apply (coreEquiv r).injective
  apply Subtype.ext
  change (coreEquiv r ((markedEquiv r).symm
    (otherSquare (quotientEquiv r (QuotientGroup.mk' (otherZ r) x))))).val =
      (coreEquiv r (x.val ^ 2)).val
  have he := congrArg Subtype.val ((markedEquiv r).apply_symm_apply
    (otherSquare (quotientEquiv r (QuotientGroup.mk' (otherZ r) x))))
  change (coreEquiv r ((markedEquiv r).symm _).val).val = _ at he
  rw [he, quotientEquiv_mk]
  change (coreEquiv r x.val).val ^ 2 = (coreEquiv r (x.val ^ 2)).val
  rw [map_pow]
  rfl

theorem squareMap_surjective : Function.Surjective (squareMap r) :=
  (markedEquiv r).symm.surjective.comp
    ((SourceQuotientBridge.NonsplitOther.squareMap_surjective innerModel).comp
      (quotientEquiv r).surjective)

theorem squareMap_ker_card : Nat.card (squareMap r).ker = 4 := by
  have hc := (squareMap r).ker.card_mul_index
  have hi : (squareMap r).ker.index = 2 := by
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (squareMap_surjective r)).toEquiv,
      Nat.card_congr (markedEquiv r).toEquiv, card_distinguished]
  rw [hi, quotient_card] at hc
  omega

theorem squareMap_nonzero : squareMap r ≠ 1 := by
  intro h
  apply otherSquare_nonzero
  apply MonoidHom.ext
  intro q
  obtain ⟨v,rfl⟩ := (quotientEquiv r).surjective q
  have hv : squareMap r v = 1 := congrArg (fun f : (otherCore r ⧸ otherZ r) →* markedCore r => f v) h
  have he := congrArg (markedEquiv r) hv
  change markedEquiv r ((markedEquiv r).symm (otherSquare (quotientEquiv r v))) =
    markedEquiv r 1 at he
  rw [MulEquiv.apply_symm_apply, map_one] at he
  exact he

def cubic : L := (pairIso r).left.symm coreCubic

theorem cubic_conjugation (x : pCore 2 L) :
    wreathMap r (MulAut.conjNormal (cubic r) x) = FourWreathTwo.cubic (wreathMap r x) := by
  have he : coreEquiv r (MulAut.conjNormal (cubic r) x) =
      outerConjugation (firstParabolic_normalizes_outerCore innerModel) coreCubic (coreEquiv r x) := by
    apply Subtype.ext
    rw [coreEquiv_val]
    change ((pairIso r).left (cubic r * x.val * (cubic r)⁻¹)).val =
      coreCubic.val * (coreEquiv r x).val * coreCubic.val⁻¹
    simp only [map_mul, map_inv, cubic, MulEquiv.apply_symm_apply, coreEquiv_val]
    rfl
  change coreWreathMap (coreEquiv r (MulAut.conjNormal (cubic r) x)) = _
  rw [he, coreCubic_conjugation]
  rfl

/-- The order-sixteen subgroup inside the recognized first parabolic. -/
def other : Subgroup L := (otherCore r).map (pCore 2 L).subtype

theorem other_card : Nat.card (other r) = 16 := by
  rw [other, Subgroup.card_map_of_injective Subtype.val_injective, otherCore_card]

include r in
theorem first_card : Nat.card L = 384 :=
  (Nat.card_congr (pairIso r).left.toEquiv).trans firstParabolic_card

/-- In the Q=A branch, normality comes from the larger local two-core. -/
theorem first_quotient_card [(other r).Normal] : Nat.card (L ⧸ other r) = 24 := by
  have hc := (other r).card_mul_index
  rw [other_card, first_card r, Subgroup.index_eq_card] at hc
  omega

/-- The chosen recognition respects the entire left overlap inclusion. -/
theorem pair_left (b : B) : ((pairIso r).left (α.left b)).val =
    ((pairIso r).middle b).val :=
  congrArg Subtype.val ((pairIso r).left_commutes b)

/-- It respects the right inclusion of the very same middle group. -/
theorem pair_right (b : B) : ((pairIso r).right (α.right b)).val =
    ((pairIso r).middle b).val :=
  congrArg Subtype.val ((pairIso r).right_commutes b)

/-- The marked subgroup of the recognized first parabolic, before restriction to its core. -/
def marked : Subgroup L :=
  (distinguished.subgroupOf firstParabolic).comap (pairIso r).left.toMonoidHom

theorem markedCore_eq : markedCore r = (marked r).subgroupOf (pCore 2 L) := by
  ext x
  change (coreEquiv r x).val ∈ distinguished ↔ ((pairIso r).left x.val).val ∈ distinguished
  rw [coreEquiv_val]

theorem marked_overlap (b : B) : α.left b ∈ marked r ↔
    ((pairIso r).middle b).val ∈ distinguished := by
  change ((pairIso r).left (α.left b)).val ∈ distinguished ↔ _
  rw [pair_left]

/-- Both quaternion maps use the fixed embeddings in the actual model. -/
def leftQuaternion : QuaternionGroup 2 →* pCore 2 L :=
  (coreEquiv r).symm.toMonoidHom.comp outerLeft

def rightQuaternion : QuaternionGroup 2 →* pCore 2 L :=
  (coreEquiv r).symm.toMonoidHom.comp outerRight

theorem leftQuaternion_marking (q : QuaternionGroup 2) :
    ((pairIso r).left (leftQuaternion r q).val).val = leftLift q := by
  rw [← coreEquiv_val]
  exact congrArg (fun x : outerCore => x.val) ((coreEquiv r).apply_symm_apply (outerLeft q))

theorem rightQuaternion_marking (q : QuaternionGroup 2) :
    ((pairIso r).left (rightQuaternion r q).val).val = rightLift q := by
  rw [← coreEquiv_val]
  exact congrArg (fun x : outerCore => x.val) ((coreEquiv r).apply_symm_apply (outerRight q))

/-- The quaternion base remains the literal preimage under the transported wreath map. -/
theorem wreathMap_mem_base (x : pCore 2 L) : wreathMap r x ∈ FourWreathTwo.base ↔
    ((pairIso r).left x.val).val ∈ FirstParabolic.quaternionCore := by
  rw [← coreEquiv_val]
  exact SourceQuotientBridge.wreathMap_mem_base innerModel (coreEquiv r x)

/-- The model count applies to the actual Q once the Q=A branch has been established. -/
theorem quotient_card_of_eq_other (Q : Subgroup L) [Q.Normal] (hQ : Q = other r) :
    Nat.card (L ⧸ Q) = 24 := by
  subst Q
  exact first_quotient_card r

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel.Transport
