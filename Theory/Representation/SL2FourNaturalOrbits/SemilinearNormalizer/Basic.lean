module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.SpecificGroups.GL2.Semilinear
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic.FinCases

/-!
# The faithful natural semilinear action on F₄²

The actual matrix semidirect product GL₂(F₄) ⋊ Aut(F₄) acts by a matrix after
coordinatewise field automorphism. The action is faithful and its image consists
of exactly the invertible semilinear maps. We identify both coefficient
automorphisms and retain the literal SL₂ and Frobenius embeddings.

The construction follows the natural-action part of the repository's
`ChapterHLocalActions.HexSemilinear`, without importing its hexacode geometry.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), 6.2.5,
printed pp.680--681 (PDF pp.697--698).
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural.SemilinearNormalizer
open Matrix.GeneralLinearGroup

abbrev LinearGroup := Matrix.GeneralLinearGroup (Fin 2) F
abbrev Gamma := GammaL2 F
abbrev BinaryGL := V ≃ₗ[ZMod 2] V

def omega : F := ⟨0, 1⟩

def glEquiv : LinearGroup ≃* (V ≃ₗ[F] V) :=
  toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv F V)

def linear : LinearGroup →* (V ≃ₗ[ZMod 2] V) where
  toFun A := (glEquiv A).restrictScalars (ZMod 2)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact LinearEquiv.congr_fun glEquiv.map_one v
  map_mul' A B := by
    apply LinearEquiv.ext
    intro v
    exact LinearEquiv.congr_fun (glEquiv.map_mul A B) v

def coefficient : (F ≃+* F) →* (V ≃ₗ[ZMod 2] V) where
  toFun σ :=
    { toFun v i := σ (v i)
      invFun v i := σ.symm (v i)
      left_inv v := by funext i; exact σ.symm_apply_apply _
      right_inv v := by funext i; exact σ.apply_symm_apply _
      map_add' v w := by funext i; exact map_add σ _ _
      map_smul' c v := by
        funext i
        fin_cases c
        · change σ ((0 : ZMod 2) • v i) = (0 : ZMod 2) • σ (v i)
          simp
        · change σ ((1 : ZMod 2) • v i) = (1 : ZMod 2) • σ (v i)
          simp }
  map_one' := by apply LinearEquiv.ext; intro v; rfl
  map_mul' σ τ := by apply LinearEquiv.ext; intro v; rfl

/-- The natural action of ΓL₂(4) on the binary restriction of its F₄ plane. -/
def natural : Gamma →* (V ≃ₗ[ZMod 2] V) :=
  SemidirectProduct.lift linear coefficient (by
    intro σ
    apply MonoidHom.ext
    intro A
    apply LinearEquiv.ext
    intro v
    change ((A.val.map σ).mulVec v) =
      (fun i => σ (A.val.mulVec (fun j => σ.symm (v j)) i))
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul,
      RingEquiv.apply_symm_apply, Matrix.map_apply])

/-- The action is literally matrix multiplication after entrywise field automorphism. -/
theorem natural_apply (g : Gamma) (v : V) :
    natural g v = g.left.val.mulVec (fun i => g.right (v i)) := by rfl

theorem field_cases (x : F) : x = 0 ∨ x = 1 ∨ x = omega ∨ x = 1 + omega := by
  revert x
  decide

/-- All automorphisms of the four-element field are identity or Frobenius. -/
theorem fieldAutomorphism_cases (σ : F ≃+* F) : σ = 1 ∨ σ = fieldFrobenius := by
  have determine (σ τ : F ≃+* F) (h : σ omega = τ omega) : σ = τ := by
    apply RingEquiv.ext
    intro x
    rcases field_cases x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact h
    · simpa only [map_add, map_one] using congrArg (1 + ·) h
  rcases field_cases (σ omega) with h | h | h | h
  · exact False.elim ((by decide : omega ≠ 0) (σ.injective (h.trans σ.map_zero.symm)))
  · exact False.elim ((by decide : omega ≠ 1) (σ.injective (h.trans σ.map_one.symm)))
  · exact Or.inl (determine σ 1 h)
  · exact Or.inr (determine σ fieldFrobenius (h.trans (by decide : 1 + omega = fieldFrobenius omega)))

theorem fieldFrobenius_ne_one : fieldFrobenius ≠ 1 := by
  intro h
  have := congrArg (fun σ : F ≃+* F => σ omega) h
  exact (by decide +kernel : fieldFrobenius omega ≠ omega) this

theorem automorphism_card : Nat.card (F ≃+* F) = 2 := by
  let f : Bool → (F ≃+* F) := fun b => if b then fieldFrobenius else 1
  have hf : Function.Bijective f := by
    constructor
    · intro b c h
      cases b <;> cases c
      · rfl
      · exact False.elim (fieldFrobenius_ne_one h.symm)
      · exact False.elim (fieldFrobenius_ne_one h)
      · rfl
    · intro σ
      rcases fieldAutomorphism_cases σ with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (by simp)

theorem gamma_card : Nat.card Gamma = 360 := by
  rw [SemidirectProduct.card, Matrix.card_GL_field, card_field, automorphism_card]
  decide

/-- The coefficient component is the field automorphism of the natural semilinear action. -/
theorem natural_smul (g : Gamma) (c : F) (v : V) :
    natural g (c • v) = g.right c • natural g v := by
  change glEquiv g.left (fun i => g.right (c * v i)) = _
  simp only [map_mul]
  exact (glEquiv g.left).map_smul (g.right c) _

theorem linear_injective : Function.Injective linear := by
  intro A B h
  apply glEquiv.injective
  apply LinearEquiv.ext
  intro v
  exact LinearEquiv.congr_fun h v

/-- The natural semilinear action is faithful, including its field component. -/
theorem natural_injective : Function.Injective natural := by
  intro g h he
  have hr : g.right = h.right := by
    apply RingEquiv.ext
    intro c
    obtain ⟨v, hv⟩ := (natural g).surjective (fun _ => 1)
    have hc := LinearEquiv.congr_fun he (c • v)
    rw [natural_smul, natural_smul, ← he, hv] at hc
    simpa using congrFun hc 0
  apply SemidirectProduct.ext
  · apply linear_injective
    have hm : linear g.left * coefficient g.right = linear h.left * coefficient h.right := he
    rw [hr] at hm
    exact mul_right_cancel hm
  · exact hr

theorem natural_exists (e : V ≃ₗ[ZMod 2] V) (σ : F ≃+* F)
    (he : ∀ (c : F) (v : V), e (c • v) = σ c • e v) :
    ∃ g : Gamma, natural g = e := by
  let L : V ≃ₗ[F] V :=
    { ((coefficient σ).symm.trans e).toAddEquiv with
      map_smul' := by
        intro c v
        change e (fun i => σ.symm (c * v i)) = c • _
        simp only [map_mul]
        change e (σ.symm c • (fun i => σ.symm (v i))) = _
        rw [he, RingEquiv.apply_symm_apply]
        rfl }
  refine ⟨⟨glEquiv.symm L, σ⟩, ?_⟩
  apply LinearEquiv.ext
  intro v
  change glEquiv (glEquiv.symm L) (coefficient σ v) = e v
  rw [glEquiv.apply_symm_apply]
  change e ((coefficient σ).symm (coefficient σ v)) = e v
  rw [LinearEquiv.symm_apply_apply]

/-- The semilinear normalizer candidate, as an actual subgroup of binary GL. -/
def semilinear : Subgroup BinaryGL := natural.range

/-- The literal binary-linear normalizer appearing in 6.2.5. -/
def normalizer : Subgroup BinaryGL := Subgroup.normalizer (action.range : Set BinaryGL)

/-- The determinant-one layer inside the semidirect product. -/
def special : SL →* Gamma := SemidirectProduct.inl.comp Matrix.SpecialLinearGroup.toGL

/-- The specified coordinate field involution in the semidirect product. -/
def fieldElement : Gamma := SemidirectProduct.inr fieldFrobenius

@[simp] theorem natural_special (A : SL) : natural (special A) = action A := by
  apply LinearEquiv.ext
  intro v
  rfl

@[simp] theorem natural_fieldElement : natural fieldElement = frobeniusLinear := by
  apply LinearEquiv.ext
  intro v
  change (1 : Matrix (Fin 2) (Fin 2) F).mulVec _ = _
  rw [Matrix.one_mulVec]
  rfl

/-- The binary subgroup generated by SL₂ and the specified Frobenius. -/
def specialField : Subgroup BinaryGL := action.range ⊔ Subgroup.zpowers frobeniusLinear

end Representation.SL2FourNatural.SemilinearNormalizer
