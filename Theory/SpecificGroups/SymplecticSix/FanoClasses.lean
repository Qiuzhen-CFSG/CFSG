module
public import Theory.SpecificGroups.SymplecticSix.FanoCore
public import Theory.Representation.PSL3Two.FanoTransvectionInvariants
/-!
# The four binary symplectic involution invariants

Image size of the displacement and alternation of its induced quadratic
function are invariant under conjugation. The explicit Fano-core shear
has exactly the previously calculated tensor invariants. Thus conjugacy
in the full symplectic group cannot fuse two different Fano-core orbits.
The four retained representatives have types b₁, a₂, c₂ and b₃.
Source: Aschbacher–Smith 13.4.9, printed pp.906–907 and H.5.3(3–4).
-/

@[expose] public section

namespace Theory.SpecificGroups.SymplecticSix
open TwoLocalCover
local notation "F" => ZMod 2

/-- The actual displacement on the natural six-space. -/
noncomputable def involutionDisplacement (g : Sp F) : Module.End F (Vector F) :=
  (toLinear g).toLinearMap - LinearMap.id

/-- Image size and alternation distinguish Suzuki's four binary involution types. -/
noncomputable def involutionSignature (g : Sp F) : ℕ × Bool := by
  classical
  exact (Nat.card (Set.range (involutionDisplacement g)),
    decide (∀ x : Vector F, form F x (involutionDisplacement g x) = 0))

theorem involutionDisplacement_conjugate (g a : Sp F) (x : Vector F) :
    involutionDisplacement (g * a * g⁻¹) (g • x) = g • involutionDisplacement a x := by
  change (g * a * g⁻¹) • (g • x) - g • x = toLinear g (a • x - x)
  rw [map_sub]
  simp only [mul_smul,inv_smul_smul,toLinear_apply]

theorem involutionSignature_conjugate (g a : Sp F) :
    involutionSignature (g * a * g⁻¹) = involutionSignature a := by
  classical
  have hr : Set.range (involutionDisplacement (g * a * g⁻¹)) =
      toLinear g '' Set.range (involutionDisplacement a) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      obtain ⟨v,rfl⟩ := (toLinear g).surjective x
      exact ⟨_,⟨v,rfl⟩,(involutionDisplacement_conjugate g a v).symm⟩
    · rintro ⟨_,⟨v,rfl⟩,rfl⟩
      exact ⟨g • v,involutionDisplacement_conjugate g a v⟩
  have ha : (∀ x : Vector F, form F x (involutionDisplacement (g * a * g⁻¹) x) = 0) ↔
      ∀ x : Vector F, form F x (involutionDisplacement a x) = 0 := by
    constructor
    · intro h x
      have hh := h (g • x)
      rw [involutionDisplacement_conjugate,preserves_form] at hh
      exact hh
    · intro h x
      obtain ⟨v,rfl⟩ := (toLinear g).surjective x
      change form F (g • v) (involutionDisplacement _ (g • v)) = 0
      rw [involutionDisplacement_conjugate,preserves_form]
      exact h v
  simp only [involutionSignature,hr,Nat.card_image_of_injective (toLinear g).injective,ha]

theorem involutionSignature_eq_of_isConj {a c : Sp F} (h : IsConj a c) :
    involutionSignature a = involutionSignature c := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact (involutionSignature_conjugate g a).symm

end Theory.SpecificGroups.SymplecticSix

namespace BinaryLinearThree.FanoTransvection
open Theory.SpecificGroups.SymplecticSix
open Theory.SpecificGroups.SymplecticSix.TwoLocalCover
local notation "F" => ZMod 2
variable (b : BinaryLinearThree.Vector →ₗ[F] Theory.SpecificGroups.SymplecticSix.Vector F)
    (hb : ∀ v w, form F (b v) (b w) = 0)

theorem shear_signature (hi : Function.Injective b) (a : Core) :
    involutionSignature (shear b hb (Multiplicative.ofAdd a)) = tensorSignature a := by
  classical
  have hd : involutionDisplacement (shear b hb (Multiplicative.ofAdd a)) =
      displacement (form F) b a := by
    apply LinearMap.ext
    intro x
    change shearElement b hb a • x - x = _
    rw [shearElement_apply]
    abel
  simp only [involutionSignature,hd,displacement_image_card _ form_nondegenerate _ hi,
    displacement_alternating_iff _ form_nondegenerate _ hi,tensorSignature]

/-- Ambient symplectic conjugacy cannot fuse distinct Fano-core orbits. -/
theorem orbit_eq_of_shear_isConj (hi : Function.Injective b) (a c : Core)
    (h : IsConj (shear b hb (Multiplicative.ofAdd a))
      (shear b hb (Multiplicative.ofAdd c))) :
    BinaryLinearThree.FanoLocalStructure.orbit a = BinaryLinearThree.FanoLocalStructure.orbit c := by
  apply (tensorSignature_eq_iff_orbit_eq a c).mp
  have he := involutionSignature_eq_of_isConj h
  simpa only [shear_signature b hb hi] using he

end BinaryLinearThree.FanoTransvection

namespace BinaryLinearThree.FanoTransvection
open FanoLocalStructure FanoDecomposition FanoCoreStructure

/-- Representatives of b₁, a₂, c₂ and b₃ in the original seven-point core. -/
def fourRepresentatives : Fin 4 → Core :=
  ![pointSpike Matrix.PSL3Two.flagPoint, lineComplement Matrix.PSL3Two.flagLine,
    weightTwoRepresentative, basisComplementRepresentative]

/-- The four representative signatures are distinct. -/
theorem fourRepresentatives_signatures (i : Fin 4) :
    tensorSignature (fourRepresentatives i) = ![(2,false),(4,true),(4,false),(8,false)] i := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := four_families_signatures
  fin_cases i
  · exact h₁ _ ⟨_,rfl⟩
  · exact h₂ _ ⟨_,rfl⟩
  · apply h₃
    rw [weightTwo_eq_orbit]
    exact ⟨1,by rw [map_one]; rfl⟩
  · apply h₄
    rw [basisComplements_eq_orbit]
    exact ⟨1,by rw [map_one]; rfl⟩

theorem fourRepresentatives_signature_injective :
    Function.Injective (fun i => tensorSignature (fourRepresentatives i)) := by
  intro i j h
  simp only [fourRepresentatives_signatures] at h
  have hi : Function.Injective (![(2,false),(4,true),(4,false),(8,false)] : Fin 4 → ℕ × Bool) := by
    decide +kernel
  exact hi h

theorem fourRepresentatives_ne_zero (i : Fin 4) : fourRepresentatives i ≠ 0 := by
  intro h
  have he := fourRepresentatives_signatures i
  rw [h] at he
  have hz : tensorSignature (0 : Core) = (1,true) := by
    simp [tensorSignature,tensorImage,tensor_zero]
    decide +kernel
  rw [hz] at he
  fin_cases i <;> simp at he

/-- The four representatives exhaust the nonzero core under the literal Fano action. -/
theorem exists_fourRepresentatives_orbit (a : Core) (ha : a ≠ 0) :
    ∃ i : Fin 4, a ∈ orbit (fourRepresentatives i) := by
  rcases (nonzero_iff_mem_four_families a).mp ha with h | h | h | h
  · exact ⟨0,pointComplements_eq_orbit ▸ h⟩
  · exact ⟨1,lineComplements_eq_orbit ▸ h⟩
  · exact ⟨2,weightTwo_eq_orbit ▸ h⟩
  · exact ⟨3,basisComplements_eq_orbit ▸ h⟩

end BinaryLinearThree.FanoTransvection
