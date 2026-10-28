module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Control
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.SubspaceQuotient

/-!
# The actual binary line section and its fixed-subgroup images

`SectionSpace V E` is the binary quotient of the original conjugate span
`U = V_E` by its subgroup `E`. Its action is induced by ambient conjugation
in `G_E = N_G(E)` and descends to the original core quotient once
`[U,Q_E] ≤ E`. The summands are defined as images of the original fixed
subgroups; no fixed-point lifting or direct-sum assertion is built into the
definitions. Right conjugation carries the first such image to the second.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170, before the temporary replacement.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
variable {G : Type*} [Group G]
variable (V E : Subgroup G) [IsElementaryAbelian 2 (lineV V E)]

/-- The original `G_E` action on `U`, by left conjugation. -/
noncomputable def spanRepresentation :
    Representation (ZMod 2) (lineNormalizer E) (Additive (lineV V E)) :=
  Representation.BinaryInternalFixedSpaceCodimension.representation
    (lineV V E) (lineNormalizer E) (le_normalizer_conjugateSpanBy V _)

/-- Evaluation retains actual ambient conjugation. -/
theorem spanRepresentation_apply (g : lineNormalizer E) (v : Additive (lineV V E)) :
    ((spanRepresentation V E g v).toMul : G) = (g : G) * (v.toMul : G) * (g : G)⁻¹ := rfl

/-- The binary subspace of `E ∩ U`; in the source `E ≤ V ≤ U`. -/
noncomputable def lineSubspace : Submodule (ZMod 2) (Additive (lineV V E)) :=
  Representation.NormalElementaryQuotient.subspace (lineV V E) (E.subgroupOf (lineV V E))

/-- Relative normality of `E` makes its subspace invariant under `G_E`. -/
noncomputable def lineSubrepresentation : Subrepresentation (spanRepresentation V E) where
  toSubmodule := lineSubspace V E
  apply_mem_toSubmodule g := by
    intro v hv
    change (g : G) * (v.toMul : G) * (g : G)⁻¹ ∈ E
    exact (g.property (v.toMul : G)).mp hv

/-- The binary vector space of the original section `U/E`. -/
abbrev SectionSpace := Additive (lineV V E) ⧸ lineSubspace V E

/-- The induced action of the original line normalizer on `U/E`. -/
noncomputable def sectionRepresentation :
    Representation (ZMod 2) (lineNormalizer E) (SectionSpace V E) :=
  (lineSubrepresentation V E).quotientRepresentation

/-- The canonical binary quotient map. -/
noncomputable def sectionProjection :
    Additive (lineV V E) →ₗ[ZMod 2] SectionSpace V E := (lineSubspace V E).mkQ

/-- Every quotient vector has a representative in the original `U`. -/
theorem sectionProjection_surjective : Function.Surjective (sectionProjection V E) :=
  (lineSubspace V E).mkQ_surjective

/-- The quotient map has exactly the specified line as kernel. -/
theorem sectionProjection_ker : (sectionProjection V E).ker = lineSubspace V E :=
  Submodule.ker_mkQ _

/-- The original projection is equivariant for conjugation. -/
theorem sectionRepresentation_projection (g : lineNormalizer E) (v : Additive (lineV V E)) :
    sectionRepresentation V E g (sectionProjection V E v) =
      sectionProjection V E (spanRepresentation V E g v) := rfl

/-- The image of `C_U(t)` in the actual quotient, before fixed-point lifting. -/
noncomputable def fixedImage (t : G) : Submodule (ZMod 2) (SectionSpace V E) :=
  (Representation.NormalElementaryQuotient.subspace (lineV V E)
    ((centralizer ({t} : Set G)).subgroupOf (lineV V E))).map (sectionProjection V E)

/-- Membership supplies a lift centralizing the original element. -/
theorem mem_fixedImage (t : G) (x : SectionSpace V E) :
    x ∈ fixedImage V E t ↔ ∃ u : lineV V E, (u : G) * t = t * (u : G) ∧
      sectionProjection V E (Additive.ofMul u) = x := by
  change (∃ u : Additive (lineV V E), (u.toMul : G) ∈ centralizer ({t} : Set G) ∧ _) ↔ _
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, eq_comm (a := t * _)]
  rfl

/-- The commutator bound makes the original two-core act trivially. -/
theorem core_le_sectionRepresentation_ker
    (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E) :
    pCore 2 (lineNormalizer E) ≤ (sectionRepresentation V E).ker := by
  intro g hg
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := sectionProjection_surjective V E x
  rw [sectionRepresentation_projection]
  change sectionProjection V E (spanRepresentation V E g v) = sectionProjection V E v
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, sectionProjection_ker]
  change ((spanRepresentation V E g v).toMul : G) / (v.toMul : G) ∈ E
  rw [div_eq_mul_inv, spanRepresentation_apply]
  have hcomm' : ⁅lineQ E, lineV V E⁆ ≤ E := by rwa [commutator_comm]
  exact hcomm' (commutator_mem_commutator
    (mem_map_of_mem (lineNormalizer E).subtype hg) v.toMul.property)

/-- Descent to `G_E/Q_E`, retaining the same binary section. -/
noncomputable def coreQuotientRepresentation
    (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E) :
    Representation (ZMod 2) (lineNormalizer E ⧸ pCore 2 (lineNormalizer E))
      (SectionSpace V E) :=
  QuotientGroup.lift (pCore 2 (lineNormalizer E)) (sectionRepresentation V E)
    (core_le_sectionRepresentation_ker V E hcomm)

/-- Descent preserves the action of each original normalizer element. -/
theorem coreQuotientRepresentation_mk
    (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E) (g : lineNormalizer E) :
    coreQuotientRepresentation V E hcomm (QuotientGroup.mk' (pCore 2 (lineNormalizer E)) g) =
      sectionRepresentation V E g := rfl

/-- Right conjugation carries the images of the original fixed subgroups. -/
theorem fixedImage_rightConjugate (y : lineNormalizer E) (t : G) :
    (fixedImage V E t).map (sectionRepresentation V E y⁻¹) =
      fixedImage V E ((y : G)⁻¹ * t * y) := by
  apply le_antisymm
  · rintro x ⟨z, hz, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (mem_fixedImage V E t z).mp hz
    apply (mem_fixedImage V E _ _).mpr
    refine ⟨(spanRepresentation V E y⁻¹ (Additive.ofMul u)).toMul, ?_, rfl⟩
    rw [spanRepresentation_apply]
    simp only [Subgroup.coe_inv, toMul_ofMul, inv_inv]
    have hh := congrArg (fun a : G => (y : G)⁻¹ * a * y) hu
    convert hh using 1 <;> group
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_fixedImage V E _ _).mp hx
    refine ⟨sectionProjection V E (spanRepresentation V E y (Additive.ofMul u)), ?_, ?_⟩
    · apply (mem_fixedImage V E _ _).mpr
      refine ⟨(spanRepresentation V E y (Additive.ofMul u)).toMul, ?_, rfl⟩
      change ((y : G) * (u : G) * (y : G)⁻¹) * t =
        t * ((y : G) * (u : G) * (y : G)⁻¹)
      have hh := congrArg (fun a : G => (y : G) * a * (y : G)⁻¹) hu
      convert hh using 1 <;> group
    · rw [← sectionRepresentation_projection]
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
