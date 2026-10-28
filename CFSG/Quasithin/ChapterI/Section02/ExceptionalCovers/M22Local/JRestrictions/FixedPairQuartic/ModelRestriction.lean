module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic.ModelTransport
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic.Residual

/-!
# The second elementary restriction as an actual model subgroup

The literal core of the preimage of the native pair stabilizer of {0,4}
lies in the preimage of the incident hexad `m22Hexad234`. Its image under the
constructed split-extension coordinates is a subgroup of the fixed intrinsic
model. The original core is multiplicatively equivalent to this image, with
its ambient map into K explicitly retained.

This image has order 64, contains the embedded central C₄, and has all squares
in the embedded sign subgroup. The last assertion uses the already proved
fixed-pair Frattini equality. It does not identify the pair E₁₆ with the hexad
pointwise kernel.

Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412. What remains is a
pure model calculation: identify such an order-64 restriction with the genuine
C₄ ∗ Q₈ ∗ Q₈ Clifford group. This module proves the native consumer premises;
it does not assume or assert that remaining isomorphism.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
variable {K : Type*} [Group K] [Finite K]
variable (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
variable (rec : Recognition e m22Hexad234_mem)

/-- Inclusion of the literal pair core in the proved incident hexad overgroup. -/
noncomputable def coreInHexad : pCore 2 (preimage e m22DisjointPairStabilizer) →*
    hexadPreimage e m22Hexad234 where
  toFun x := ⟨(x.val : K), fixed_pair_core_le_hexad234 e hZ ⟨x.val, x.property, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coreInHexad_injective : Function.Injective (coreInHexad e hZ) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : hexadPreimage e m22Hexad234 => (z : K)) h

noncomputable def coreInModel : pCore 2 (preimage e m22DisjointPairStabilizer) →*
    EvenCliffordSix.SplitExtension :=
  (rec.modelToHexad e m22Hexad234_mem).symm.toMonoidHom.comp (coreInHexad e hZ)

theorem coreInModel_injective : Function.Injective (coreInModel e hZ rec) :=
  (rec.modelToHexad e m22Hexad234_mem).symm.injective.comp (coreInHexad_injective e hZ)

/-- The actual second E₁₆ pullback, transported to the intrinsic extension. -/
noncomputable def coreImage : Subgroup EvenCliffordSix.SplitExtension := (coreInModel e hZ rec).range

/-- A multiplicative equivalence with the image, retaining the original native core. -/
noncomputable def coreImageEquiv : pCore 2 (preimage e m22DisjointPairStabilizer) ≃*
    coreImage e hZ rec := MonoidHom.ofInjective (coreInModel_injective e hZ rec)

@[simp] theorem coreImageEquiv_ambient (x : pCore 2 (preimage e m22DisjointPairStabilizer)) :
    (rec.modelToHexad e m22Hexad234_mem (coreImageEquiv e hZ rec x).val : K) =
      (x.val : K) := by
  change ((rec.modelToHexad e m22Hexad234_mem)
    ((rec.modelToHexad e m22Hexad234_mem).symm (coreInHexad e hZ x)) : K) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem coreImage_card : Nat.card (coreImage e hZ rec) = 64 :=
  (Nat.card_congr (coreImageEquiv e hZ rec).toEquiv).symm.trans (fixed_pair_core_card e hZ)

include hZ in
private theorem center_le_core : center K ≤
    (pCore 2 (preimage e m22DisjointPairStabilizer)).map
      (preimage e m22DisjointPairStabilizer).subtype := by
  rw [← preimage_twoCore e (IsPGroup.of_card (n := 2) (by simpa using hZ))]
  exact center_le_preimage e _

theorem coreImage_contains_central : EvenCliffordSix.SplitExtension.central ≤ coreImage e hZ rec := by
  intro z hz
  have hc := rec.modelToHexad_central e m22Hexad234_mem z hz
  obtain ⟨x, hx, he⟩ := center_le_core e hZ hc
  refine ⟨⟨x, hx⟩, ?_⟩
  apply (rec.modelToHexad e m22Hexad234_mem).injective
  change rec.modelToHexad e m22Hexad234_mem ((coreImageEquiv e hZ rec ⟨x,hx⟩).val) = _
  exact Subtype.ext ((coreImageEquiv_ambient e hZ rec ⟨x,hx⟩).trans he)

variable [IsCyclic (center K)]

/-- The existing fixed-pair Frattini theorem supplies the intrinsic square bound. -/
theorem coreImage_square (x : EvenCliffordSix.SplitExtension) (hx : x ∈ coreImage e hZ rec) :
    x ^ 2 ∈ EvenCliffordSix.SplitExtension.sign := by
  obtain ⟨q, rfl⟩ := hx
  apply (rec.modelToHexad_mem_squares e m22Hexad234_mem hZ _).mp
  have hs : ((q.val : K) ^ 2) ∈ centralSquares K := by
    change ((q.val : K) ^ 2) ∈ centerSquares K
    rw [← fixed_pair_frattini e hZ]
    let : Fact (IsPGroup 2 (pCore 2 (preimage e m22DisjointPairStabilizer))) := ⟨pCore_isPGroup⟩
    exact ⟨q.val ^ 2, ⟨q ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) q, rfl⟩, rfl⟩
  rw [map_pow]
  change ((rec.modelToHexad e m22Hexad234_mem (coreImageEquiv e hZ rec q).val) ^ 2 :
    hexadPreimage e m22Hexad234).val ∈ centralSquares K
  simpa only [Subgroup.coe_pow, coreImageEquiv_ambient] using hs

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
