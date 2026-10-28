module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Row-subspace actions for the O'Nan orbit certificate

Preimages under right multiplication define a left action on row subspaces.
A scalar matrix preserves every submodule, so this action descends from GL to
PGL. Equivalently, the action sends a row span to its product by the inverse
matrix (`smul_range`).

The transition lemmas turn matrix identities into equalities of subspaces.
Over a finite ring, injectivity suffices for surjectivity, so a square change
of row coordinates needs no separately supplied inverse certificate. These
lemmas support the concrete basis in `../FixedPlane.lean`; the source matrices
and attribution are preserved in `refs/original/onan/`.
-/

@[expose] public section

open Matrix
namespace ONan.OrderCertificate.RowSpaces
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
/-- Row subspaces of the coordinate module. -/
abbrev Space (n R : Type*) [CommRing R] := Submodule R (n → R)
/-- Pullback by right multiplication is a left GL action. -/
instance glAction : MulAction (GeneralLinearGroup n R) (Space n R) where
  smul g S := S.comap (vecMulLinear (g : Matrix n n R))
  one_smul S := by
    apply Submodule.ext
    intro v
    change v ᵥ* (1 : Matrix n n R) ∈ S ↔ v ∈ S
    rw [vecMul_one]
  mul_smul g h S := by
    apply Submodule.ext
    intro v
    change v ᵥ* ((g * h : GeneralLinearGroup n R) : Matrix n n R) ∈ S ↔
      (v ᵥ* (g : Matrix n n R)) ᵥ* (h : Matrix n n R) ∈ S
    simp only [GeneralLinearGroup.coe_mul, vecMul_vecMul]

/-- Units scale a submodule onto itself. -/
lemma scalar_smul (u : Rˣ) (S : Space n R) :
    GeneralLinearGroup.scalar n u • S = S := by
  change S.comap _ = S
  apply Submodule.ext
  intro v
  change v ᵥ* (GeneralLinearGroup.scalar n u : Matrix n n R) ∈ S ↔ v ∈ S
  have h : v ᵥ* (GeneralLinearGroup.scalar n u : Matrix n n R) = (u : R) • v := by
    ext j
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, vecMul_diagonal, mul_comm]
  rw [h]
  exact S.smul_mem_iff_of_isUnit u.isUnit

/-- The induced projective action on row subspaces. -/
instance pglAction : MulAction (ProjGenLinGroup n R) (Space n R) :=
  ProjGenLinGroup.mulActionOfGL scalar_smul

/-- An invariant row span is fixed by the inverse-image action. -/
lemma fixed_of_mul [Finite R] {m : Type*} [Fintype m]
    (W : Matrix m n R) (g : GeneralLinearGroup n R)
    (C : Matrix m m R) (h : W * (g : Matrix n n R) = C * W) :
    g • LinearMap.range W.vecMulLinear = LinearMap.range W.vecMulLinear := by
  let S := LinearMap.range W.vecMulLinear
  have hm : ∀ v ∈ S, v ᵥ* (g : Matrix n n R) ∈ S := by
    rintro _ ⟨c, rfl⟩
    refine ⟨c ᵥ* C, ?_⟩
    simpa only [vecMulLinear_apply, vecMul_vecMul] using
      congrArg (fun M : Matrix m n R => c ᵥ* M) h.symm
  have hi : Function.Injective (vecMul · (g : Matrix n n R)) :=
    Matrix.vecMul_injective_of_isUnit g.isUnit
  let f : S → S := fun v => ⟨v.val ᵥ* (g : Matrix n n R), hm v.val v.property⟩
  have hf : Function.Injective f := fun v w hvw => Subtype.ext (hi (congrArg Subtype.val hvw))
  have hs := Finite.surjective_of_injective hf
  change S.comap _ = S
  apply Submodule.ext
  intro v
  change v ᵥ* (g : Matrix n n R) ∈ S ↔ v ∈ S
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := hs ⟨_, hv⟩
    have he : w.val = v := hi (congrArg Subtype.val hw)
    exact he ▸ w.property
  · exact hm v
/-- On row spans, the action multiplies the basis by the inverse matrix. -/
lemma smul_range {m : Type*} [Fintype m]
    (g : GeneralLinearGroup n R) (W : Matrix m n R) :
    g • LinearMap.range W.vecMulLinear =
      LinearMap.range (W * ((g⁻¹ : GeneralLinearGroup n R) : Matrix n n R)).vecMulLinear := by
  apply Submodule.ext
  intro v
  change (∃ c, c ᵥ* W = v ᵥ* (g : Matrix n n R)) ↔
    ∃ c, c ᵥ* (W * ((g⁻¹ : GeneralLinearGroup n R) : Matrix n n R)) = v
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← vecMul_vecMul, hc, vecMul_vecMul, ← GeneralLinearGroup.coe_mul]
    simp
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc, vecMul_vecMul, Matrix.mul_assoc, ← GeneralLinearGroup.coe_mul]
    simp

omit [Fintype n] [DecidableEq n] in
/-- An injective row family remains a basis after a square row-coordinate change. -/
lemma range_mul_eq_of_injective [Finite R] {m : Type*} [Fintype m]
    (W V : Matrix m n R) (C : Matrix m m R)
    (hW : Function.Injective W.vecMul) (h : W = C * V) :
    LinearMap.range W.vecMulLinear = LinearMap.range V.vecMulLinear := by
  have hi : Function.Injective C.vecMul := by
    intro c d hcd
    apply hW
    change c ᵥ* W = d ᵥ* W
    change c ᵥ* C = d ᵥ* C at hcd
    rw [h, ← vecMul_vecMul, ← vecMul_vecMul, hcd]
  have hs := Finite.surjective_of_injective hi
  apply Submodule.ext
  intro v
  change (∃ c, c ᵥ* W = v) ↔ ∃ c, c ᵥ* V = v
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c ᵥ* C, by rw [vecMul_vecMul, ← h]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hs c
    change d ᵥ* C = c at hd
    exact ⟨d, by rw [h, ← vecMul_vecMul, hd]⟩

/-- A checked matrix transition gives the corresponding projective-orbit edge. -/
lemma inv_smul_range_of_mul [Finite R] {m : Type*} [Fintype m]
    (W V : Matrix m n R) (g : GeneralLinearGroup n R) (C : Matrix m m R)
    (hW : Function.Injective W.vecMul) (h : W * (g : Matrix n n R) = C * V) :
    g⁻¹ • LinearMap.range W.vecMulLinear = LinearMap.range V.vecMulLinear := by
  rw [smul_range, inv_inv]
  apply range_mul_eq_of_injective _ _ C ?_ h
  have hg := Matrix.vecMul_injective_of_isUnit g.isUnit
  intro c d hcd
  apply hW
  apply hg
  simpa only [vecMul_vecMul] using hcd
omit [Fintype n] [DecidableEq n] in
/-- An identity minor certifies independence of the rows. -/
lemma vecMul_injective_of_pivots {m : Type*} [Fintype m] [DecidableEq m]
    (W : Matrix m n R) (p : m → n)
    (hp : ∀ i j, W i (p j) = if i = j then 1 else 0) :
    Function.Injective W.vecMul := by
  have h (c : m → R) (j : m) : (c ᵥ* W) (p j) = c j := by
    simp [Matrix.vecMul, dotProduct, hp]
  intro c d hcd
  funext j
  exact (h c j).symm.trans ((congrFun hcd (p j)).trans (h d j))
end ONan.OrderCertificate.RowSpaces
