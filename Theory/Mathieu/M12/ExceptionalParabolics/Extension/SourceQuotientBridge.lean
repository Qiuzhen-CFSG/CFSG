module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.Intrinsic
public import Theory.GroupTheory.QuaternionSwapModel.WreathCoordinates

/-!
# The actual first-core quotient and the obstruction to an elementary lift

The marked quotient of the concrete first two-core is written in the pair
coordinates used by the invariant-subgroup calculation. The quotient map,
its kernel, the quaternion-base correspondence and the actual conjugation
action are retained.

The literal preimage of the diagonal-plus-swap eight-group has order sixteen,
but is not elementary: its actual swap lift squares to the original nonidentity
z. More generally every elementary subgroup of the first core lies in the
quaternion core and therefore has image in the wreath base. Thus changing
coordinates cannot produce an elementary preimage outside that base.

This distinguishes the actual nonsplit first core from the split movement
subgroup of the whole overlap. It obstructs a proposed unconditional E₁₆
model construction, without refuting the full ambient implication in the
proof of Aschbacher--Smith 14.2.21, printed p.988, refs/quasithin.pdf.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SourceQuotientBridge
open FirstParabolic
open QuaternionSwapModel.WreathCoordinates
attribute [local irreducible] z

/-- The quotient by the original Z, in the coordinates of the core trichotomy. -/
def quotientEquiv (m : InnerModel) : OuterQuotient ≃* FourWreathTwo.Wreath :=
  (outerQuotientEquiv m).trans wreathEquiv

/-- The actual first-core quotient map, with the same literal kernel. -/
def wreathMap (m : InnerModel) : outerCore →* FourWreathTwo.Wreath :=
  wreathEquiv.toMonoidHom.comp (outerWreathMap m)

theorem quotientEquiv_mk (m : InnerModel) (x : outerCore) :
    quotientEquiv m (outerProjection x) = wreathMap m x := rfl

theorem wreathMap_surjective (m : InnerModel) : Function.Surjective (wreathMap m) :=
  wreathEquiv.surjective.comp (outerWreathMap_surjective m)

theorem wreathMap_ker (m : InnerModel) :
    (wreathMap m).ker = distinguished.subgroupOf outerCore := by
  unfold wreathMap outerWreathMap outerProjection
  rw [MonoidHom.ker_comp_of_injective _ _ wreathEquiv.injective,
    MonoidHom.ker_comp_of_injective _ _ (outerQuotientEquiv m).injective,
    QuotientGroup.ker_mk']

theorem wreathMap_mem_base (m : InnerModel) (x : outerCore) :
    wreathMap m x ∈ FourWreathTwo.base ↔ x.val ∈ quaternionCore :=
  (mem_base _).trans (outerWreathMap_mem_base m x)

theorem wreathMap_base (m : InnerModel) :
    (quaternionCore.subgroupOf outerCore).map (wreathMap m) = FourWreathTwo.base := by
  rw [wreathMap, ← Subgroup.map_map, outerWreathMap_base, map_base]

/-- The literal preimage of the distinguished other eight-group. -/
def otherPreimage (m : InnerModel) : Subgroup outerCore :=
  FourWreathTwo.other.comap (wreathMap m)

theorem otherPreimage_eq (m : InnerModel) :
    otherPreimage m = QuaternionSwapModel.other.comap (outerWreathMap m) := by
  ext x
  exact mem_other _

theorem otherPreimage_image (m : InnerModel) :
    (otherPreimage m).map (wreathMap m) = FourWreathTwo.other :=
  Subgroup.map_comap_eq_self_of_surjective (wreathMap_surjective m) _

theorem otherPreimage_card (m : InnerModel) : Nat.card (otherPreimage m) = 16 := by
  let Z₀ := distinguished.subgroupOf outerCore
  have hZE : Z₀ ≤ otherPreimage m := by
    change distinguished.subgroupOf outerCore ≤ otherPreimage m
    rw [← wreathMap_ker m]
    exact Subgroup.ker_le_comap (wreathMap m) _
  have hZ : Nat.card Z₀ = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe distinguished_le_outerCore).toEquiv).trans
      card_distinguished
  have hquot : Nat.card (otherPreimage m ⧸ Z₀.subgroupOf (otherPreimage m)) = 8 := by
    have h := Subgroup.relIndex_ker (otherPreimage m) (wreathMap m)
    rw [wreathMap_ker, otherPreimage_image, FourWreathTwo.card_other] at h
    exact h
  have hmul := (Z₀.subgroupOf (otherPreimage m)).card_mul_index
  have hZ' : Nat.card (Z₀.subgroupOf (otherPreimage m)) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv).trans hZ
  rw [Subgroup.index_eq_card, hquot, hZ'] at hmul
  omega

/-- The actual lift of the pure swap lies in this preimage. -/
theorem outerSwap_mem_otherPreimage (m : InnerModel) : outerSwap ∈ otherPreimage m := by
  rw [otherPreimage_eq]
  change outerWreathMap m outerSwap ∈ QuaternionSwapModel.other
  rw [outerWreathMap_swap]
  rfl

theorem outerSwap_square : outerSwap ^ 2 = outerMarked :=
  Subtype.ext nonsplitSwap_square

theorem outerMarked_ne_one : outerMarked ≠ 1 := by
  intro h
  exact z_ne_one (congrArg Subtype.val h)

/-- Every square-one subgroup of the actual core lies over the wreath base. -/
theorem square_one_subgroup_le_quaternion (m : InnerModel) (E : Subgroup outerCore)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : E ≤ quaternionCore.subgroupOf outerCore := by
  intro x hx
  exact outerCore_square_one_mem_quaternionCore m x.val x.property
    (congrArg Subtype.val (hE x hx))

theorem elementary_subgroup_image_le_base (m : InnerModel) (E : Subgroup outerCore)
    [IsElementaryAbelian 2 E] : E.map (wreathMap m) ≤ FourWreathTwo.base := by
  rw [← wreathMap_base m]
  exact Subgroup.map_mono (square_one_subgroup_le_quaternion m E
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx))

/-- This holds for every elementary subgroup and any outside-base image, regardless of markings. -/
theorem not_elementary_of_image_not_le_base (m : InnerModel) (E : Subgroup outerCore)
    (hE : ¬ E.map (wreathMap m) ≤ FourWreathTwo.base) : ¬ IsElementaryAbelian 2 E := by
  intro h
  let := h
  exact hE (elementary_subgroup_image_le_base m E)

/-- The marked other preimage is not elementary: its swap lift has order four. -/
theorem otherPreimage_not_elementary (m : InnerModel) :
    ¬ IsElementaryAbelian 2 (otherPreimage m) := by
  intro h
  let := h
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) outerSwap
    (outerSwap_mem_otherPreimage m)
  rw [outerSwap_square] at hs
  exact outerMarked_ne_one hs

/-- In particular the E₁₆ identification required by the proposed source model is impossible. -/
theorem otherPreimage_not_equiv_E16 (m : InnerModel) :
    ¬ Nonempty (otherPreimage m ≃* QuaternionSwapModel.E16) := by
  rintro ⟨e⟩
  let s : otherPreimage m := ⟨outerSwap,outerSwap_mem_otherPreimage m⟩
  have hs : s ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    have h : ∀ v : QuaternionSwapModel.E16, v ^ 2 = 1 := by decide +kernel
    exact h (e s)
  have ho : outerSwap ^ 2 = 1 := congrArg (fun x : otherPreimage m => x.val) hs
  rw [outerSwap_square] at ho
  exact outerMarked_ne_one ho

/-- Transported action, still induced by literal first-parabolic conjugation. -/
def action (m : InnerModel) : firstParabolic →* MulAut FourWreathTwo.Wreath :=
  (MulAut.congr wreathEquiv).toMonoidHom.comp (FirstParabolic.wreathAction m)

theorem action_evaluation (m : InnerModel) (h : firstParabolic) (x : outerCore) :
    action m h (wreathMap m x) = wreathMap m
      (outerConjugation (firstParabolic_normalizes_outerCore m) h x) := by
  change wreathEquiv (FirstParabolic.wreathAction m h
    (wreathEquiv.symm (wreathEquiv (outerWreathMap m x)))) = _
  rw [MulEquiv.symm_apply_apply, FirstParabolic.wreathAction_evaluation]
  rfl

end Sporadic.Mathieu.M12ExceptionalExtension.SourceQuotientBridge
