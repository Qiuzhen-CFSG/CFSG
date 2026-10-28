module

public import Theory.SpecificGroups.Monster.Construction.Symmetric
public import Mathlib.Tactic.FinCases

/-!
# The five-block trilinear assembly

The construction takes the two pure blocks and the three mixed blocks
of Aschbacher 28.12. Each mixed block contributes its three placements,
with coefficient one. Pullback along the actual summand projections
preserves trilinearity. Symmetry in each pure block and in the two repeated
slots of each mixed block gives invariance under every permutation of
three arguments. The symmetric-matrix block is bundled from the existing
`symmetricProductMap` and `symmetricGammaForm`.

The remaining blocks and projections are explicit inputs here. Their
specialization to the fixed source space belongs to the carrier assembly.

Source: Aschbacher, *Sporadic Groups*, Remark 9.6 and 28.7–28.12,
printed pp. 152–154.
-/

@[expose] public section

namespace Sporadic.Monster.Construction.Griess

variable {V S R W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup S] [Module ℝ S]
variable [AddCommGroup R] [Module ℝ R]
variable [AddCommGroup W] [Module ℝ W]

/-- Pull a trilinear block back along three independent linear maps. -/
def pullback3 (f : S →ₗ[ℝ] R →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (p : V →ₗ[ℝ] S) (q : V →ₗ[ℝ] R) (r : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun y := (f (p x) (q y)).comp r
      map_add' y z := by ext t; simp
      map_smul' a y := by ext t; simp }
  map_add' x y := by ext z t; simp
  map_smul' a x := by ext y z; simp

@[simp] theorem pullback3_apply (f : S →ₗ[ℝ] R →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (p : V →ₗ[ℝ] S) (q : V →ₗ[ℝ] R) (r : V →ₗ[ℝ] W) (x y z : V) :
    pullback3 f p q r x y z = f (p x) (q y) (r z) := rfl

/-- The three placements of the distinguished slot. No averaging factor occurs. -/
def mixedBlock (f : S →ₗ[ℝ] R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (p : V →ₗ[ℝ] S) (q : V →ₗ[ℝ] R) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  pullback3 f p q q + (pullback3 f p q q).flip +
    (LinearMap.lflip.toLinearMap.comp (pullback3 f p q q).flip)

@[simp] theorem mixedBlock_apply (f : S →ₗ[ℝ] R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (p : V →ₗ[ℝ] S) (q : V →ₗ[ℝ] R) (x y z : V) :
    mixedBlock f p q x y z =
      f (p x) (q y) (q z) + f (p y) (q x) (q z) + f (p z) (q x) (q y) := rfl

theorem mixedBlock_swap_left (f : S →ₗ[ℝ] R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (hf : ∀ s a b, f s a b = f s b a)
    (p : V →ₗ[ℝ] S) (q : V →ₗ[ℝ] R) (x y z : V) :
    mixedBlock f p q x y z = mixedBlock f p q y x z := by
  simp only [mixedBlock_apply, hf (p z), add_comm]

theorem mixedBlock_swap_right (f : S →ₗ[ℝ] R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (hf : ∀ s a b, f s a b = f s b a)
    (p : V →ₗ[ℝ] S) (q : V →ₗ[ℝ] R) (x y z : V) :
    mixedBlock f p q x y z = mixedBlock f p q x z y := by
  simp only [mixedBlock_apply, hf (p x) (q y) (q z)]
  abel

/-- Assembly of exactly the five homogeneous blocks in (28.12). Projections
are supplied by the source orthogonal sum, so this does not define new spaces. -/
def fiveBlockForm
    (sss : S →ₗ[ℝ] S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
    (rrr : R →ₗ[ℝ] R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (srr : S →ₗ[ℝ] R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (sww : S →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (rww : R →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (ps : V →ₗ[ℝ] S) (pr : V →ₗ[ℝ] R) (pw : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  pullback3 sss ps ps ps + pullback3 rrr pr pr pr +
    mixedBlock srr ps pr + mixedBlock sww ps pw + mixedBlock rww pr pw

variable
    (sss : S →ₗ[ℝ] S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
    (rrr : R →ₗ[ℝ] R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (srr : S →ₗ[ℝ] R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (sww : S →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (rww : R →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (ps : V →ₗ[ℝ] S) (pr : V →ₗ[ℝ] R) (pw : V →ₗ[ℝ] W)

theorem fiveBlockForm_swap_left
    (hs : ∀ x y z, sss x y z = sss y x z)
    (hr : ∀ x y z, rrr x y z = rrr y x z)
    (hsr : ∀ x y z, srr x y z = srr x z y)
    (hsw : ∀ x y z, sww x y z = sww x z y)
    (hrw : ∀ x y z, rww x y z = rww x z y) (x y z : V) :
    fiveBlockForm sss rrr srr sww rww ps pr pw x y z =
      fiveBlockForm sss rrr srr sww rww ps pr pw y x z := by
  unfold fiveBlockForm
  simp only [LinearMap.add_apply, pullback3_apply, hs (ps x) (ps y), hr (pr x) (pr y),
    mixedBlock_swap_left srr hsr ps pr x y z,
    mixedBlock_swap_left sww hsw ps pw x y z,
    mixedBlock_swap_left rww hrw pr pw x y z]

theorem fiveBlockForm_swap_right
    (hs : ∀ x y z, sss x y z = sss x z y)
    (hr : ∀ x y z, rrr x y z = rrr x z y)
    (hsr : ∀ x y z, srr x y z = srr x z y)
    (hsw : ∀ x y z, sww x y z = sww x z y)
    (hrw : ∀ x y z, rww x y z = rww x z y) (x y z : V) :
    fiveBlockForm sss rrr srr sww rww ps pr pw x y z =
      fiveBlockForm sss rrr srr sww rww ps pr pw x z y := by
  unfold fiveBlockForm
  simp only [LinearMap.add_apply, pullback3_apply, hs (ps x) (ps y), hr (pr x) (pr y),
    mixedBlock_swap_right srr hsr ps pr x y z,
    mixedBlock_swap_right sww hsw ps pw x y z,
    mixedBlock_swap_right rww hrw pr pw x y z]

/-- The two adjacent transpositions give invariance under every permutation. -/
theorem permute_of_swap (f : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hl : ∀ x y z, f x y z = f y x z)
    (hr : ∀ x y z, f x y z = f x z y)
    (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → V) :
    f (v (σ 0)) (v (σ 1)) (v (σ 2)) = f (v 0) (v 1) (v 2) := by
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h)
  generalize σ 0 = a, σ 1 = b, σ 2 = c at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> first
  | exact (h01 rfl).elim
  | exact (h02 rfl).elim
  | exact (h12 rfl).elim
  | rfl
  | exact hr _ _ _
  | exact hl _ _ _
  | exact (hr _ _ _).trans (hl _ _ _)
  | exact (hl _ _ _).trans (hr _ _ _)
  | exact (hl _ _ _).trans ((hr _ _ _).trans (hl _ _ _))

/-- Full symmetry of the five-block extension. -/
theorem fiveBlockForm_permute
    (hsl : ∀ x y z, sss x y z = sss y x z)
    (hsr : ∀ x y z, sss x y z = sss x z y)
    (hrl : ∀ x y z, rrr x y z = rrr y x z)
    (hrr : ∀ x y z, rrr x y z = rrr x z y)
    (hsrr : ∀ x y z, srr x y z = srr x z y)
    (hsww : ∀ x y z, sww x y z = sww x z y)
    (hrww : ∀ x y z, rww x y z = rww x z y)
    (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → V) :
    fiveBlockForm sss rrr srr sww rww ps pr pw (v (σ 0)) (v (σ 1)) (v (σ 2)) =
      fiveBlockForm sss rrr srr sww rww ps pr pw (v 0) (v 1) (v 2) :=
  permute_of_swap _
    (fiveBlockForm_swap_left sss rrr srr sww rww ps pr pw hsl hrl hsrr hsww hrww)
    (fiveBlockForm_swap_right sss rrr srr sww rww ps pr pw hsr hrr hsrr hsww hrww) σ v

/-- The already constructed source symmetric block, now bundled as trilinear. -/
def symmetricBlock : SymmetricPart →ₗ[ℝ] SymmetricPart →ₗ[ℝ] SymmetricPart →ₗ[ℝ] ℝ :=
  symmetricProductMap.compr₂ symmetricGammaForm

@[simp] theorem symmetricBlock_apply (A B C : SymmetricPart) :
    symmetricBlock A B C = symmetricBeta A B C := rfl

theorem symmetricBlock_permute (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → SymmetricPart) :
    symmetricBlock (v (σ 0)) (v (σ 1)) (v (σ 2)) = symmetricBlock (v 0) (v 1) (v 2) :=
  permute_of_swap _ symmetricBeta_swap_left symmetricBeta_swap_right σ v

end Sporadic.Monster.Construction.Griess
