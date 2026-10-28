module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic.Recognition
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension
public import Theory.Frattini.OmegaProducts

/-!
# The actual hexad preimage in intrinsic split coordinates

The section and equivariant radical coordinates construct an isomorphism
from the intrinsic signed split extension onto the original hexad preimage.
The actor is reparametrized by the inverse pentad automorphism; its image in
the literal six-point quotient is recorded explicitly. The ambient product
formula retains both original subgroup embeddings.

The embedded model center maps into the actual center of K. The model sign
subgroup corresponds exactly to the actual central squares, using the proved
Frattini calculation on the hexad radical. These are transport facts for
Aschbacher–Smith I.2.2(6a), printed pp.410 and 412; no pair-core recognition
is assumed or concluded here.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open BinaryPermutation GLS3.Chapter5
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
variable {K : Type*} [Group K]
variable (e : (K ⧸ center K) ≃* M22)
variable {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (rec : Recognition e hB)

/-- Constructed from the actual complement and its equivariant radical coordinates. -/
noncomputable def Recognition.modelToHexad : EvenCliffordSix.SplitExtension ≃* hexadPreimage e B :=
  (SemidirectProduct.congr rec.coordinates.symm outerAltAut.symm (fun a => by
    apply MulEquiv.ext
    intro r
    apply rec.coordinates.injective
    change rec.coordinates (rec.coordinates.symm (EvenCliffordSix.action a r)) =
      rec.coordinates (hexadConjugation e B (rec.sectionMap (outerAltAut.symm a))
        (rec.coordinates.symm r))
    rw [rec.equivariant]
    simp only [MulEquiv.apply_symm_apply, EvenCliffordSix.precomposedAction_apply])).trans
      (MulEquiv.ofBijective (hexadSplitHom e B rec.sectionMap)
        (hexadSplitHom_bijective e hB (MulEquiv.refl _) rec.sectionMap rec.section_eq))

@[simp] theorem Recognition.modelToHexad_coe (x : EvenCliffordSix.SplitExtension) :
    (rec.modelToHexad e hB x : K) =
      (rec.coordinates.symm x.left : K) * (rec.sectionMap (outerAltAut.symm x.right) : K) := rfl

@[simp] theorem Recognition.modelToHexad_inl (x : EvenCliffordSix.Model) :
    (rec.modelToHexad e hB (EvenCliffordSix.SplitExtension.radicalEmbedding x) : K) =
      (rec.coordinates.symm x : K) := by
  rw [Recognition.modelToHexad_coe]
  simp

/-- The actual six-point quotient retains the comparison automorphism. -/
theorem Recognition.modelToHexad_six (x : EvenCliffordSix.SplitExtension) :
    hexadSixMap e hB (rec.modelToHexad e hB x) = outerAltAut.symm x.right := by
  change hexadSixMap e hB
    (Subgroup.inclusion (hexadRadical_le e B) (rec.coordinates.symm x.left) *
      rec.sectionMap (outerAltAut.symm x.right)) = _
  rw [map_mul, rec.section_eq]
  have hn : hexadSixMap e hB (Subgroup.inclusion (hexadRadical_le e B)
      (rec.coordinates.symm x.left)) = 1 := by
    apply (hexadSixMap_ker e hB).ge
    exact (rec.coordinates.symm x.left).property
  rw [hn, one_mul]

theorem Recognition.modelToHexad_central (x : EvenCliffordSix.SplitExtension)
    (hx : x ∈ EvenCliffordSix.SplitExtension.central) :
    (rec.modelToHexad e hB x : K) ∈ center K := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [Recognition.modelToHexad_inl]
  apply (rec.center_eq _).mpr
  rwa [MulEquiv.apply_symm_apply]

variable [Finite K] [IsCyclic (center K)]
variable (hZ : Nat.card (center K) = 4)

include hZ in
/-- The shared sign involution is precisely the actual square subgroup of the center. -/
theorem Recognition.modelToHexad_mem_squares (x : EvenCliffordSix.SplitExtension) :
    (rec.modelToHexad e hB x : K) ∈ centralSquares K ↔
      x ∈ EvenCliffordSix.SplitExtension.sign := by
  have hr (r : hexadRadical e B) :
      (r : K) ∈ centralSquares K ↔ rec.coordinates r ∈ EvenCliffordSix.signKernel := by
    rw [← Quartic.radical_frattini_map e hZ hB,
      ← EvenCliffordSix.frattini_eq_signKernel,
      ← frattini_map_equiv rec.coordinates]
    exact (mem_map_iff_mem (hexadRadical e B).subtype_injective).trans
      (mem_map_iff_mem rec.coordinates.injective).symm
  constructor
  · intro hx
    have hn : hexadSixMap e hB (rec.modelToHexad e hB x) = 1 := by
      apply (hexadSixMap_ker e hB).ge
      exact center_le_hexadRadical e B (centralSquares_le_center hx)
    rw [Recognition.modelToHexad_six, map_eq_one_iff _ outerAltAut.symm.injective] at hn
    apply (EvenCliffordSix.SplitExtension.mem_sign_iff x).mpr
    refine ⟨?_, hn⟩
    rw [Recognition.modelToHexad_coe, hn, map_one, map_one] at hx
    simp only [OneMemClass.coe_one, mul_one] at hx
    simpa using (hr (rec.coordinates.symm x.left)).mp hx
  · rintro ⟨z, hz, rfl⟩
    rw [Recognition.modelToHexad_inl]
    exact (hr _).mpr (by simpa using hz)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
