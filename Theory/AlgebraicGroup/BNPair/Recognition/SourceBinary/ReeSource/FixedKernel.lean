module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.JointKernels
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanReflection

/-!
# Fixed Cartan elements and the faithful panel kernel

The actual source reflection conjugates the Cartan projection by its
image in the faithful endpoint quotient. Its image is outside the full
quotient Borel. The kernel already centralizes the root-generated R_i,
so it fixes the reflection. Conversely, an element fixed by the reflection
and inverted in its faithful image has image of order dividing two;
oddness forces that image to be trivial.

This proves the fixed-kernel identification in Fong–Seitz I (6H)(a), p.51,
from rank-one inversion. The concrete linear and Suzuki applications in
RankOneCartan discharge inversion, including the binary case. Natural
rank-one markings and the earlier source RootReflection remain inputs;
this is not the common-field or complete (6H) theorem.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The chosen root-group reflection, viewed in the actual endpoint. -/
def rootReflectionEndpoint (i : Fin 2) (s : RootReflection Q split i) : Endpoint Q i :=
  ⟨s.val, Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
    (Q.tits.representative_mem_bruhatCell _ s.val s.class_eq)⟩

@[simp] theorem cartanPanelMap_reflection (i : Fin 2) (s : RootReflection Q split i)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    cartanPanelMap Q i (simpleCartanAction Q split i h) =
      (QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s))⁻¹ *
        cartanPanelMap Q i h *
          QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s) := by
  simp only [cartanPanelMap_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (QuotientGroup.mk' (panelKernel Q i))
  apply Subtype.ext
  exact simpleCartanAction_apply Q split i s.val s.class_eq h

theorem cartanPanelMap_mem_borel (i : Fin 2)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    cartanPanelMap Q i h ∈ quotientBorel Q i :=
  mem_map_of_mem _ h.property.1

theorem rootReflectionProjection_not_mem_borel (i : Fin 2) (s : RootReflection Q split i) :
    QuotientGroup.mk' (panelKernel Q i) (rootReflectionEndpoint Q split i s) ∉ quotientBorel Q i := by
  intro hm
  have hmem : rootReflectionEndpoint Q split i s ∈
      (quotientBorel Q i).comap (QuotientGroup.mk' (panelKernel Q i)) := hm
  rw [quotientBorel_comap] at hmem
  exact Q.tits.representative_not_mem_B (Q.simple_mem i) s.val s.class_eq hmem

/-- The exact panel kernel fixes the source reflection pointwise on H. -/
theorem cartanPanelMap_kernel_le_fixed (i : Fin 2) (s : RootReflection Q split i) :
    (cartanPanelMap Q i).ker ≤ reflectionFixed Q split i := by
  intro h hh
  have hk : (h : X ⧸ Q.D) ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q i := by
    refine ⟨h.property, ?_⟩
    change h ∈ (embeddedPanelKernel Q i).subgroupOf (Q.tits.B ⊓ Q.tits.N)
    rwa [← cartanPanelMap_kernel]
  rw [← cartan_centralizer_rankOneRootGroup Q split i] at hk
  have he : (s.val : X ⧸ Q.D) * h = (h : X ⧸ Q.D) * s.val :=
    (mem_centralizer_iff.mp hk.2) _ s.mem_rankOne
  change simpleCartanAction Q split i h = h
  apply Subtype.ext
  rw [simpleCartanAction_apply Q split i s.val s.class_eq]
  rw [mul_assoc, ← he, inv_mul_cancel_left]

/-- Inversion in the faithful rank-one image identifies the fixed factor.
The inversion premise is discharged by the actual rank-one model action. -/
theorem reflectionFixed_eq_kernel (i : Fin 2) (s : RootReflection Q split i)
    (hinv : ∀ h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
      cartanPanelMap Q i (simpleCartanAction Q split i h) = (cartanPanelMap Q i h)⁻¹) :
    reflectionFixed Q split i = (cartanPanelMap Q i).ker := by
  apply le_antisymm ?_ (cartanPanelMap_kernel_le_fixed Q split i s)
  intro h hh
  have hf : simpleCartanAction Q split i h = h := hh
  have he : cartanPanelMap Q i h = (cartanPanelMap Q i h)⁻¹ := by
    simpa only [hf] using hinv h
  let y : (cartanPanelMap Q i).range := ⟨cartanPanelMap Q i h, ⟨h,rfl⟩⟩
  have hy : y^2 = 1 := by
    apply Subtype.ext
    change (cartanPanelMap Q i h)^2 = 1
    rw [pow_two]
    exact (congrArg (cartanPanelMap Q i h * ·) he).trans (mul_inv_cancel _)
  have hod : Nat.Coprime 2 (Nat.card (cartanPanelMap Q i).range) :=
    split.odd.of_dvd_right (Subgroup.card_dvd_of_surjective
      (cartanPanelMap Q i).rangeRestrict (cartanPanelMap Q i).rangeRestrict_surjective)
  have hz : y = 1 := hod.symm.pow_left_bijective.injective (hy.trans (one_pow 2).symm)
  exact congrArg Subtype.val hz

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
