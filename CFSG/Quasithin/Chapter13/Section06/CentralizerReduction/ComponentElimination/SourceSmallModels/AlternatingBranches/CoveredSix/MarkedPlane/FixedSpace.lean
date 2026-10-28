module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.NormalizerTransport
public import Theory.Representation.HexacodeAction.Field

/-!
# Ambient fixed subgroups in the original covered-six module

For an actual subgroup A of K/O₂(K), the subgroup fixed by its full
preimage is constructed inside U(K). Its binary coordinates are exactly
the fixed space of the original action. The explicit hexacode coordinates
identify that space with an F₄-submodule; binary dimension four therefore
means vector dimension two over F₄. No subgroup A is selected here.

Source: Aschbacher–Smith, combined manuscript, the covered-six paragraph
of 13.6.22, printed p.932; K.1.3, printed p.453.
-/

@[expose] public section
open Subgroup CFSG.Quasithin.ChapterC Representation
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
variable {G : Type*} [Group G] (K : Subgroup G)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]

/-- The fixed subgroup uses the full inverse image under the two-core map. -/
def fixedSubgroup (A : Subgroup (K ⧸ pCore 2 K)) : Subgroup G :=
  (blockU K ⊓ centralizer (A.comap (QuotientGroup.mk' (pCore 2 K)) : Set K)).map K.subtype

omit [IsElementaryAbelian 2 (blockU K)] in
theorem fixedSubgroup_le (A : Subgroup (K ⧸ pCore 2 K)) :
    fixedSubgroup K A ≤ (blockU K).map K.subtype := map_mono inf_le_left

/-- No elements or kernel are discarded in passing to binary coordinates. -/
theorem ambientSubspace_fixedSubgroup (A : Subgroup (K ⧸ pCore 2 K)) :
    ambientSubspace K (fixedSubgroup K A) = fixedSpace (binaryAction h) A := by
  ext u
  have hc := NormalElementaryQuotient.mem_fixedSpace_image (blockU K)
    (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk', h.centralizer])
    (A.comap (QuotientGroup.mk' (pCore 2 K))) u
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hc
  change u ∈ fixedSpace (binaryAction h) A ↔ _ at hc
  rw [hc]
  change ((u.toMul : K) : G) ∈ fixedSubgroup K A ↔ _
  change (u.toMul : K) ∈ (fixedSubgroup K A).comap K.subtype ↔ _
  rw [fixedSubgroup, comap_map_eq_self_of_injective K.subtype_injective]
  exact and_iff_right u.toMul.property

/-- The full relative ambient normalizer has exactly the binary stabilizer image. -/
theorem fixedSubgroup_normalizer_image (A : Subgroup (K ⧸ pCore 2 K)) :
    ((K ⊓ normalizer (fixedSubgroup K A : Set G)).subgroupOf K).map
      (QuotientGroup.mk' (pCore 2 K)) =
        subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) A) := by
  rw [ambientNormalizer_image K h _ (fixedSubgroup_le K A), ambientSubspace_fixedSubgroup K h]

/-- Recognizing the four-group as the full pointwise kernel of its fixed
plane supplies the needed finite normalizer containment. This is the
pointwise-kernel conclusion of B.4.2(8), on the actual binary action. -/
theorem fixedSpace_stabilizer_le_normalizer_of_kernel
    (A : Subgroup (K ⧸ pCore 2 K))
    (he : A = subspaceKernel (binaryAction h) (fixedSpace (binaryAction h) A) ⊤) :
    subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) A) ≤
      normalizer (A : Set _) := by
  apply le_normalizer_iff.mpr
  intro g hg a ha
  apply he.ge
  refine ⟨mem_top _, ?_⟩
  intro u hu
  have hi := (subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) A)).inv_mem hg
  have hfix := (he.le ha).2 _ ((hi u).mpr hu)
  change binaryAction h (g * a * g⁻¹) u = u
  simp only [map_mul, Module.End.mul_apply]
  rw [hfix]
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable (m : HexacodeModel h)

/-- The literal field fixed space in the chosen representation coordinates. -/
noncomputable def fieldFixedSpace (A : Subgroup (K ⧸ pCore 2 K)) :
    Submodule Hexacode.F Atlas.Codes.hexacode where
  carrier := {w | ∀ a : A, Hexacode.action (m.quotientIso a).val w = w}
  zero_mem' := fun a => map_zero _
  add_mem' hx hy a := by rw [map_add, hx a, hy a]
  smul_mem' c w hw a := by
    rw [Hexacode.action_even_smul _ (m.quotientIso a).property, hw a]

/-- The fixed-space coordinates are the restriction of the given model map. -/
noncomputable def fixedCoordinates (A : Subgroup (K ⧸ pCore 2 K)) :
    fixedSpace (binaryAction h) A ≃ₗ[ZMod 2] fieldFixedSpace K h m A where
  toFun u := ⟨m.coordinates u, fun a => by
    rw [← m.intertwining]
    exact congrArg m.coordinates (u.property a)⟩
  invFun w := ⟨m.coordinates.symm w, fun a => by
    apply m.coordinates.injective
    change m.coordinates (binaryAction h (a : K ⧸ pCore 2 K) (m.coordinates.symm w)) = _
    rw [m.intertwining, m.coordinates.apply_symm_apply]
    exact w.property a⟩
  left_inv u := Subtype.ext (m.coordinates.symm_apply_apply u)
  right_inv w := Subtype.ext (m.coordinates.apply_symm_apply w)
  map_add' x y := Subtype.ext (m.coordinates.map_add x y)
  map_smul' c x := Subtype.ext (m.coordinates.map_smul c x)

/-- The source's projective F₄-line has vector dimension two, not one. -/
theorem fieldFixedSpace_finrank_two (A : Subgroup (K ⧸ pCore 2 K))
    (hd : Module.finrank (ZMod 2) (fixedSpace (binaryAction h) A) = 4) :
    Module.finrank Hexacode.F (fieldFixedSpace K h m A) = 2 := by
  have hb := (fixedCoordinates K h m A).finrank_eq
  let _ : Module.Free Hexacode.F (fieldFixedSpace K h m A) :=
    Module.Free.of_divisionRing Hexacode.F (fieldFixedSpace K h m A)
  have ht := Module.finrank_mul_finrank (ZMod 2) Hexacode.F (fieldFixedSpace K h m A)
  have hf : Module.finrank (ZMod 2) Hexacode.F = 2 := QuadraticAlgebra.finrank_eq_two _ _
  rw [hf, ← hb, hd] at ht
  omega

/-- The constructed ambient subgroup has sixteen elements when its binary
fixed space has dimension four. -/
theorem fixedSubgroup_card (A : Subgroup (K ⧸ pCore 2 K))
    (hd : Module.finrank (ZMod 2) (fixedSpace (binaryAction h) A) = 4) :
    Nat.card (fixedSubgroup K A) = 16 := by
  let := h.1.finite
  rw [← Nat.card_congr (ambientSubspaceEquiv K _ (fixedSubgroup_le K A))]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    ambientSubspace_fixedSubgroup K h, hd]
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
