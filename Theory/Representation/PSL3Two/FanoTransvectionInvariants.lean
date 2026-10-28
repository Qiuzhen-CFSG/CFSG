module
public import Theory.Representation.PSL3Two.FanoTransvectionTensors
/-!
# Intrinsic invariants of the four Fano-core families

The even seven-point words have tensor image sizes 2, 4, 4 and 8.
Alternation distinguishes the two families of image size four. The small
coordinate certificates use the proved rank-one tensor formula, and the
existing orbit partition gives a complete invariant. For any injective
embedding into a finite-dimensional nondegenerate bilinear space, restriction
of the pairing is surjective, so the tensor and actual displacement have
the same image size and alternation. This is used for the four involution
classes in Aschbacher–Smith 13.4.9, printed p.906, using H.5.3(3–4).
-/

@[expose] public section
open Matrix
namespace BinaryLinearThree.FanoTransvection
open FanoLocalStructure FanoDecomposition FanoCoreStructure

def tensorImage (a : Core) : Finset Vector := Finset.univ.image (tensor a *ᵥ ·)
def tensorSignature (a : Core) : ℕ × Bool :=
  ((tensorImage a).card, decide (∀ v : Vector, v ⬝ᵥ (tensor a *ᵥ v) = 0))

private theorem point_tensor (p : Point) :
    tensor (pointSpike p) = fun i j => p.val i * p.val j := by
  ext i j
  exact tensor_pointSpike p i j

private theorem point_signature : ∀ p : Point, tensorSignature (pointSpike p) = (2, false) := by
  simp only [tensorSignature,tensorImage,point_tensor]
  decide +kernel

private theorem line_signature : ∀ l : Matrix.PSL3Two.Fano.Line,
    tensorSignature (lineComplement l) = (4, true) := by
  simp only [tensorSignature,tensorImage]
  decide +kernel

private theorem pair_signature : ∀ p q : Point, p ≠ q →
    tensorSignature (pointSpike p + pointSpike q) = (4, false) := by
  simp only [tensorSignature,tensorImage,tensor_add,point_tensor]
  decide +kernel

private theorem basis_signature : ∀ b : Fin 3 → Point, IsBasisTriple b →
    tensorSignature (pointSpike (b 0) + pointSpike (b 1) + pointSpike (b 2)) = (8, false) := by
  simp only [tensorSignature,tensorImage,tensor_add,point_tensor]
  decide +kernel
end BinaryLinearThree.FanoTransvection

namespace BinaryLinearThree.FanoTransvection
open FanoLocalStructure FanoDecomposition FanoCoreStructure

theorem four_families_signatures :
    (∀ a ∈ pointComplements, tensorSignature a = (2, false)) ∧
    (∀ a ∈ lineComplements, tensorSignature a = (4, true)) ∧
    (∀ a ∈ weightTwo, tensorSignature a = (4, false)) ∧
    (∀ a ∈ basisComplements, tensorSignature a = (8, false)) := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro _ ⟨p,rfl⟩
    exact point_signature p
  · rintro _ ⟨l,rfl⟩
    exact line_signature l
  · intro a ha
    obtain ⟨p,q,hpq,rfl⟩ := (mem_weightTwo_iff a).mp ha
    exact pair_signature p q hpq
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := (mem_basisComplements_iff a).mp ha
    exact basis_signature b hb

private theorem tensorSignature_zero : tensorSignature 0 = (1, true) := by
  simp [tensorSignature,tensorImage,tensor_zero]
  decide +kernel

/-- Displacement size and alternation identify all four literal families. -/
theorem four_families_signature_iff (a : Core) :
    (a ∈ pointComplements ↔ tensorSignature a = (2, false)) ∧
    (a ∈ lineComplements ↔ tensorSignature a = (4, true)) ∧
    (a ∈ weightTwo ↔ tensorSignature a = (4, false)) ∧
    (a ∈ basisComplements ↔ tensorSignature a = (8, false)) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := four_families_signatures
  by_cases ha : a = 0
  · subst a
    have hn := (nonzero_iff_mem_four_families (0 : Core))
    simp only [ne_eq,not_true_eq_false,false_iff,not_or] at hn
    simp only [hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,tensorSignature_zero]
    decide
  · rcases (nonzero_iff_mem_four_families a).mp ha with h | h | h | h
    · have he := h₁ a h
      have hnot₂ : a ∉ lineComplements := fun k => by have := (h₂ a k).symm.trans he; contradiction
      have hnot₃ : a ∉ weightTwo := fun k => by have := (h₃ a k).symm.trans he; contradiction
      have hnot₄ : a ∉ basisComplements := fun k => by have := (h₄ a k).symm.trans he; contradiction
      simp [h,hnot₂,hnot₃,hnot₄,he]
    · have he := h₂ a h
      have hnot₁ : a ∉ pointComplements := fun k => by have := (h₁ a k).symm.trans he; contradiction
      have hnot₃ : a ∉ weightTwo := fun k => by have := (h₃ a k).symm.trans he; contradiction
      have hnot₄ : a ∉ basisComplements := fun k => by have := (h₄ a k).symm.trans he; contradiction
      simp [h,hnot₁,hnot₃,hnot₄,he]
    · have he := h₃ a h
      have hnot₁ : a ∉ pointComplements := fun k => by have := (h₁ a k).symm.trans he; contradiction
      have hnot₂ : a ∉ lineComplements := fun k => by have := (h₂ a k).symm.trans he; contradiction
      have hnot₄ : a ∉ basisComplements := fun k => by have := (h₄ a k).symm.trans he; contradiction
      simp [h,hnot₁,hnot₂,hnot₄,he]
    · have he := h₄ a h
      have hnot₁ : a ∉ pointComplements := fun k => by have := (h₁ a k).symm.trans he; contradiction
      have hnot₂ : a ∉ lineComplements := fun k => by have := (h₂ a k).symm.trans he; contradiction
      have hnot₃ : a ∉ weightTwo := fun k => by have := (h₃ a k).symm.trans he; contradiction
      simp [h,hnot₁,hnot₂,hnot₃,he]

/-- Equality of these intrinsic invariants is exactly equality of Fano orbits. -/
theorem tensorSignature_eq_iff_orbit_eq (a c : Core) :
    tensorSignature a = tensorSignature c ↔ orbit a = orbit c := by
  constructor
  · intro he
    by_cases ha : a = 0
    · subst a
      by_cases hc : c = 0
      · rw [hc]
      · rcases (nonzero_iff_mem_four_families c).mp hc with h | h | h | h <;>
          obtain ⟨h₁,h₂,h₃,h₄⟩ := four_families_signatures
        all_goals first
          | have hh := h₁ c h
          | have hh := h₂ c h
          | have hh := h₃ c h
          | have hh := h₄ c h
        all_goals rw [tensorSignature_zero,hh] at he; contradiction
    · obtain ⟨h₁,h₂,h₃,h₄⟩ := four_families_signature_iff a
      obtain ⟨k₁,k₂,k₃,k₄⟩ := four_families_signature_iff c
      have hm := (nonzero_iff_mem_four_families a).mp ha
      rcases hm with h | h | h | h
      · have hc := k₁.mpr (he.symm.trans (h₁.mp h))
        rw [pointComplements_eq_orbit] at h hc
        exact (orbit_eq_of_mem h).trans (orbit_eq_of_mem hc).symm
      · have hc := k₂.mpr (he.symm.trans (h₂.mp h))
        rw [lineComplements_eq_orbit] at h hc
        exact (orbit_eq_of_mem h).trans (orbit_eq_of_mem hc).symm
      · have hc := k₃.mpr (he.symm.trans (h₃.mp h))
        rw [weightTwo_eq_orbit] at h hc
        exact (orbit_eq_of_mem h).trans (orbit_eq_of_mem hc).symm
      · have hc := k₄.mpr (he.symm.trans (h₄.mp h))
        rw [basisComplements_eq_orbit] at h hc
        exact (orbit_eq_of_mem h).trans (orbit_eq_of_mem hc).symm
  · intro ho
    by_cases ha : a = 0
    · subst a
      have hc : c ∈ orbit c := ⟨1,by rw [map_one]; rfl⟩
      rw [←ho] at hc
      obtain ⟨g,hg⟩ := hc
      rw [map_zero] at hg
      rw [←hg]
    · obtain ⟨h₁,h₂,h₃,h₄⟩ := four_families_signatures
      have hc : c ∈ orbit c := ⟨1,by rw [map_one]; rfl⟩
      have haa : a ∈ orbit a := ⟨1,by rw [map_one]; rfl⟩
      rcases (nonzero_orbits a).mp ha with h | h | h | h <;> rw [←ho,h] at hc <;> rw [h] at haa
      · exact (h₁ a haa).trans (h₁ c hc).symm
      · exact (h₂ a haa).trans (h₂ c hc).symm
      · exact (h₃ a haa).trans (h₃ c hc).symm
      · exact (h₄ a haa).trans (h₄ c hc).symm
end BinaryLinearThree.FanoTransvection

namespace BinaryLinearThree.FanoTransvection
open Matrix
local notation "F" => ZMod 2
variable {M : Type*} [AddCommGroup M] [Module F M]

private theorem tensor_mulVec (a : Core) (v : Vector) :
    tensor a *ᵥ v = ∑ p : Point, (a.val p * (v ⬝ᵥ p.val)) • p.val := by
  ext i
  simp only [mulVec,dotProduct,tensor,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def pairCoordinates (B : LinearMap.BilinForm F M) (b : Vector →ₗ[F] M) :
    M →ₗ[F] Vector :=
  (dotProductEquiv F (Fin 3)).symm.toLinearMap.comp (b.dualMap.comp B)

theorem pairCoordinates_dot (B : LinearMap.BilinForm F M) (b : Vector →ₗ[F] M)
    (x : M) (v : Vector) : pairCoordinates B b x ⬝ᵥ v = B x (b v) :=
  LinearMap.congr_fun ((dotProductEquiv F (Fin 3)).apply_symm_apply (b.dualMap (B x))) v

theorem displacement_tensor (B : LinearMap.BilinForm F M) (b : Vector →ₗ[F] M)
    (a : Core) (x : M) :
    displacement B b a x = b (tensor a *ᵥ pairCoordinates B b x) := by
  rw [displacement_apply,tensor_mulVec]
  simp_rw [pairCoordinates_dot]

variable [FiniteDimensional F M]

theorem pairCoordinates_surjective (B : LinearMap.BilinForm F M) (hB : B.Nondegenerate)
    (b : Vector →ₗ[F] M) (hb : Function.Injective b) :
    Function.Surjective (pairCoordinates B b) := by
  intro v
  obtain ⟨f,hf⟩ := LinearMap.dualMap_surjective_of_injective hb (dotProductEquiv F (Fin 3) v)
  refine ⟨(B.toDual hB).symm f,?_⟩
  apply (dotProductEquiv F (Fin 3)).injective
  change dotProductEquiv F (Fin 3)
      ((dotProductEquiv F (Fin 3)).symm (b.dualMap (B ((B.toDual hB).symm f)))) = _
  rw [LinearEquiv.apply_symm_apply]
  have hdual : B ((B.toDual hB).symm f) = f := by
    ext y
    exact B.apply_toDual_symm_apply f y
  rw [hdual,hf]

theorem displacement_image_card (B : LinearMap.BilinForm F M) (hB : B.Nondegenerate)
    (b : Vector →ₗ[F] M) (hb : Function.Injective b) (a : Core) :
    Nat.card (Set.range (displacement B b a)) = (tensorImage a).card := by
  have hr : Set.range (displacement B b a) = b '' Set.range (tensor a *ᵥ ·) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨_,⟨pairCoordinates B b x,rfl⟩,(displacement_tensor B b a x).symm⟩
    · rintro ⟨_,⟨v,rfl⟩,rfl⟩
      obtain ⟨x,rfl⟩ := pairCoordinates_surjective B hB b hb v
      exact ⟨x,displacement_tensor B b a x⟩
  rw [hr,Nat.card_image_of_injective hb]
  have he : Set.range (tensor a *ᵥ ·) = (tensorImage a : Set Vector) := by
    ext v
    simp [tensorImage]
  rw [he]
  exact Nat.card_eq_finsetCard _

theorem displacement_alternating_iff (B : LinearMap.BilinForm F M) (hB : B.Nondegenerate)
    (b : Vector →ₗ[F] M) (hb : Function.Injective b) (a : Core) :
    (∀ x : M, B x (displacement B b a x) = 0) ↔
      ∀ v : Vector, v ⬝ᵥ (tensor a *ᵥ v) = 0 := by
  simp_rw [displacement_tensor,←pairCoordinates_dot]
  constructor
  · intro h v
    obtain ⟨x,rfl⟩ := pairCoordinates_surjective B hB b hb v
    exact h x
  · intro h x
    exact h (pairCoordinates B b x)

end BinaryLinearThree.FanoTransvection
