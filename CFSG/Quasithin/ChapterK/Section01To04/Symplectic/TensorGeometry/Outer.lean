module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Diagram
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Bounds
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Exclusion
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Assembly.Sections

/-!
# Outer actions on the descended symplectic tensor

The native b₁ and a₂ fixed dimensions force the literal extension action to
preserve both parabolic types. The canonical Hermitian model is descended to
the original module, where outer involutions fix 10s dimensions and their
component centralizers act faithfully on the two literal sections.

Every elementary outer actor meets the component in index two. Model common
fixed-space estimates give codimension at least 8s, strictly greater at maximal
rank, including s = 1. Together with the sharp rank bound 3s+1, this proves the
exact placement interface consumed by `TensorReduction`. The only independent
inputs retained in that interface are the permitted native b₁/a₂ dimensions;
no outer representation estimate or recognition certificate remains.
Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  {L : Subgroup G} [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
  [Field F] [Algebra (SchurField (ρ.comp L.subtype)) F]

omit [Finite G] in
theorem TensorIdentification.preservesDiagram_of_native_fixed_dimensions
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    (hb : ∀ j : L, IsB1 (h.groupEquiv j) →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j.val)) = 10 * s)
    (ha : ∀ j : L, IsA2 (h.groupEquiv j) →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j.val)) = 8 * s)
    (g : G) : PreservesDiagram (extensionAction L h.groupEquiv.symm g) := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  apply TensorGeometry.Outer.preservesDiagram_of_native_fixed_dimensions ρ L h.groupEquiv.symm hs
      (fun x hx => hb (h.groupEquiv.symm x) (by simpa only [MulEquiv.apply_symm_apply] using hx))
      (fun x hx => ha (h.groupEquiv.symm x) (by simpa only [MulEquiv.apply_symm_apply] using hx)) g

omit [L.Normal] in
theorem TensorIdentification.elementary_le_component_of_outer_estimates
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    (hb : ∀ j : L, IsB1 (h.groupEquiv j) →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j.val)) = 10 * s)
    (ha : ∀ j : L, IsA2 (h.groupEquiv j) →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j.val)) = 8 * s)
    (hsingle : ∀ t : G, orderOf t = 2 → t ∉ L →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 10 * s)
    (hproper : ∀ (A : Subgroup G), IsElementaryTwo A →
      ∀ t : G, orderOf t = 2 → t ∉ L → zpowers t < A →
      8 * s ≤ fixedCodim ρ A ∧ (rank A = 3 * s + 1 → 8 * s < fixedCodim ρ A)) :
    ∀ A : Subgroup G, IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → A ≤ L := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  have hC := TensorGeometry.Outer.component_centralizer_eq_bot ρ L hS h.groupEquiv.symm
  have hD := h.preservesDiagram_of_native_fixed_dimensions hs hb ha
  apply TensorGeometry.Outer.elementary_le_of_outer_estimates ρ L hs h.binary_finrank
      (fun A hA t ht hout => TensorGeometry.Outer.outer_elementary_rank_le L hs h.field_card
        h.groupEquiv.symm hC hD A hA t ht hout) hsingle hproper

omit [L.Normal] in
/-- The outer field involution fixes exactly `10s` binary dimensions. -/
theorem TensorIdentification.outer_fixed_finrank
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 10 * s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  exact TensorGeometry.Outer.Assembly.outer_fixed_finrank ρ L hS hs h t ht hout

omit [L.Normal] in
/-- The strict bound includes the maximal-rank case over the binary Schur field. -/
theorem TensorIdentification.proper_outer_codimension
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) (hproper : zpowers t < A) :
    8 * s ≤ fixedCodim ρ A ∧ (rank A = 3 * s + 1 → 8 * s < fixedCodim ρ A) := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  exact TensorGeometry.Outer.Assembly.proper_outer_codimension ρ L hS hs h A hA t ht hout hproper

omit [L.Normal] in
/-- K.3.4.2's outer exclusion in the exact placement form consumed by
`TensorReduction`: every elementary actor of ratio at most two lies in the
component. The only independent inputs are the native b₁/a₂ dimensions. -/
theorem TensorIdentification.elementary_le_component
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    (hb : ∀ j : L, IsB1 (h.groupEquiv j) →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j.val)) = 10 * s)
    (ha : ∀ j : L, IsA2 (h.groupEquiv j) →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j.val)) = 8 * s) :
    ∀ A : Subgroup G, IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → A ≤ L := by
  exact h.elementary_le_component_of_outer_estimates hS hs hb ha
    (h.outer_fixed_finrank hS hs) (h.proper_outer_codimension hS hs)

omit [L.Normal] in
/-- The actual component centralizer acts faithfully on both original-module
sections of every outer involution. -/
theorem TensorIdentification.outer_sections_faithful
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    Function.Injective (InvolutionHomology.moved ρ t (L ⊓ centralizer {t}) inf_le_right).toRepresentation ∧
      Function.Injective (InvolutionHomology.homology ρ t (L ⊓ centralizer {t}) inf_le_right) := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  exact TensorGeometry.Outer.Assembly.outer_sections_faithful ρ L hS hs h t ht hout

omit [L.Normal] in
/-- Dimensions of the literal displacement and fixed/displacement quotient. -/
theorem TensorIdentification.outer_section_finranks
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 6 * s ∧
    Module.finrank (ZMod 2)
      ((fixedSpace ρ (zpowers t)) ⧸
        (LinearMap.range (ρ t - LinearMap.id)).comap (fixedSpace ρ (zpowers t)).subtype) = 4 * s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  exact TensorGeometry.Outer.Assembly.outer_section_finranks ρ L hS hs h t ht hout

end CFSG.Quasithin.ChapterK.Symplectic
