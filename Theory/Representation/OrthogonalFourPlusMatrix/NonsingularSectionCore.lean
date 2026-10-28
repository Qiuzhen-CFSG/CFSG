module
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointCore
public import Theory.Representation.BinaryConjugationSection.InvariantImages

/-!
# Two-cores of nonsingular literal section normalizers

For a binary conjugation section with its exact kernel, a subgroup whose
section image has order two is normalized precisely when the unique
nonzero image vector is fixed. Transporting the literal conjugation action
to the determinant module therefore identifies its relative normalizer
with a point fixer. If the full inner orthogonal group is in the action
image, its point stabilizer also lies in that fixer. The nonsingular-point
core bound, followed through the same action's two-group kernel, bounds
the image of the original relative normalizer's two-core by two.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. The original reciprocal-plane application is in
`LocalReduction.BinaryPlaneCore`.
-/

public noncomputable section
open Subgroup Representation
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.PointCore
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup D} {ρ : Representation (ZMod 2) H W}

omit [Finite D] in
/-- A two-element section image detects its relative normalizer by fixing
its unique nonzero vector, retaining the original conjugation map. -/
theorem section_normalizer_iff
    (s : BinaryConjugationSection H U Z ρ)
    (π : H →* BinaryAut) (E : W ≃ₗ[ZMod 2] V)
    (hE : ∀ x w, E (ρ x w) = π x (E w))
    (P : Subgroup D) (hPU : P ≤ U) (hZP : Z ≤ P)
    (hc : Nat.card (s.imageSpace P) = 2)
    (w : W) (hw : w ∈ s.imageSpace P) (hw0 : w ≠ 0) (x : H) :
    (x : D) ∈ normalizer (P : Set D) ↔ π x (E w) = E w := by
  have hsmall (v : W) (hv : v ∈ s.imageSpace P) : v = 0 ∨ v = w := by
    by_cases hz : v = 0
    · exact Or.inl hz
    · right
      obtain ⟨a,ha,hu⟩ := (Nat.card_eq_two_iff' (0 : s.imageSpace P)).mp hc
      have hvn : (⟨v,hv⟩ : s.imageSpace P) ≠ 0 := fun h => hz (congrArg Subtype.val h)
      have hwn : (⟨w,hw⟩ : s.imageSpace P) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
      exact congrArg Subtype.val ((hu _ hvn).trans (hu _ hwn).symm)
  have hpres (y : H) (hy : π y (E w) = E w) (v : D) (hv : v ∈ P) :
      (y : D)*v*(y : D)⁻¹ ∈ P := by
    let u : U := ⟨v,hPU hv⟩
    have hu : (s.coordinates u).toAdd ∈ s.imageSpace P :=
      (s.mem_imageSpace_iff _ _).mpr ⟨u,hv,rfl⟩
    have hfixed : ρ y (s.coordinates u).toAdd = (s.coordinates u).toAdd := by
      apply E.injective
      rw [hE]
      rcases hsmall _ hu with he | he
      · rw [he,map_zero,map_zero]
      · rw [he]; exact hy
    let u' : U := ⟨(y:D)*v*(y:D)⁻¹,(mem_normalizer_iff.mp (s.normalized y.property) v).mp u.property⟩
    apply (s.coordinates_mem_imageSpace_iff_of_kernel_le P hZP u').mp
    change (s.coordinates ⟨(y:D)*u*(y:D)⁻¹,_⟩).toAdd ∈ _
    rw [s.equivariant,hfixed]
    exact hu
  constructor
  · intro hx
    have hm := s.imageSpace_apply_mem P x hx w hw
    rcases hsmall _ hm with he | he
    · have hn : E w ≠ 0 := fun hz => hw0 (E.injective (hz.trans E.map_zero.symm))
      have hz : π x (E w) = 0 := by rw [←hE,he,map_zero]
      exact (hn ((π x).injective (hz.trans (map_zero (π x)).symm))).elim
    · rw [←hE,he]
  · intro hx
    have hi : π x⁻¹ (E w) = E w := by
      rw [map_inv]
      exact (π x).injective (by change π x ((π x).symm (E w)) = π x (E w); rw [(π x).apply_symm_apply,hx])
    apply mem_normalizer_iff.mpr
    intro v
    constructor
    · exact hpres x hx v
    · intro hv
      have hh := hpres x⁻¹ hi ((x:D)*v*(x:D)⁻¹) hv
      simpa only [Subgroup.coe_inv,inv_inv,inv_mul_cancel_left,mul_assoc,
        inv_mul_cancel,mul_one] using hh

/-- The literal relative plane normalizer has quotient two-core of order
at most two whenever its section point is nonsingular. -/
theorem section_normalizer_core_card
    (s : BinaryConjugationSection H U Z ρ)
    (π : H →* BinaryAut) (E : W ≃ₗ[ZMod 2] V)
    (hE : ∀ x w, E (ρ x w) = π x (E w))
    (hn : π.range ≤ normalizer (linearAction.range : Set BinaryAut))
    (hi : linearAction.range ≤ π.range) (hk : IsPGroup 2 π.ker)
    (P : Subgroup D) (hPU : P ≤ U) (hZP : Z ≤ P)
    (hc : Nat.card (s.imageSpace P) = 2)
    (w : W) (hw : w ∈ s.imageSpace P) (hw0 : w ≠ 0) (hwd : (E w).det ≠ 0) :
    Nat.card ((((normalizer (P : Set D)).subgroupOf H).pCoreIn 2).map π) ≤ 2 := by
  let : Finite BinaryAut := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let A := (normalizer (P : Set D)).subgroupOf H
  have hfix : ∀ a ∈ A.map π, a (E w) = E w := by
    rintro _ ⟨x,hx,rfl⟩
    exact (section_normalizer_iff s π E hE P hPU hZP hc w hw hw0 x).mp hx
  have hinner : (pointStabilizer (E w)).map linearAction ≤ A.map π := by
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨x,hx⟩ := hi ⟨g,rfl⟩
    refine ⟨x,?_,hx⟩
    exact (section_normalizer_iff s π E hE P hPU hZP hc w hw hw0 x).mpr
      (by rw [hx]; exact (mem_pointStabilizer g (E w)).mp hg)
  have hb := nonsingular_point_core_card (A.map π)
    ((map_le_range _ _).trans hn) (E w) hwd hfix hinner
  rwa [←map_pCoreIn_of_ker_isPGroup π hk A] at hb
end ClassicalOrthogonal.FourPlusMatrix.Binary.PointCore
