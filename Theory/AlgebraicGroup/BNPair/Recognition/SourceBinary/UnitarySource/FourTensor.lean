module
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.Model
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourPositive

/-!+# Positive U4 relations from the actual Hermitian tensor module

The abelian complementary root section in Fong--Seitz I (6A)(b) and II
(8B) is the fixed-field form of Gamma tensor Gamma-bar. Its three root
summands are the two diagonal entries and the off-diagonal entry of a
Hermitian two-by-two matrix. The upper transvection action gives both
mixed polynomial relations, including the nonzero short-short trace.

Given a realization of this module in a group, we construct its four root
maps and prove all positive relations and generation of the module image.
The realization, its source placement and its normalization are not proved
here; they remain obligations of the original-source reconstruction.
Source: Fong--Seitz I pp.20--21 and II pp.201--202, (8.7)--(8.9).
-/

@[expose] public noncomputable section
open Matrix Subgroup
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FourTensor

variable (E : Type*) [Field E] [CharP E 2]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "K" => UnitaryFourSylow.FixedField E σ

def conjugation : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := σ) (fun a => a.property)

/-- The actual fixed-field Hermitian form of the tensor module. -/
abbrev Core : Type _ := (hermitian (conjugation E σ) hσ).toSubmodule

def diagonalTop : K →+ Core E σ hσ where
  toFun d := ⟨!![(d:E),0;0,0], by
    have hd : σ (d:E) = (d:E) := d.property
    change adjoint σ !![(d:E),0;0,0] = !![(d:E),0;0,0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjoint, hd]⟩
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' d e := by ext i j; fin_cases i <;> fin_cases j <;> simp

def diagonalBottom : K →+ Core E σ hσ where
  toFun b := ⟨!![0,0;0,(b:E)], by
    have hb : σ (b:E) = (b:E) := b.property
    change adjoint σ !![0,0;0,(b:E)] = !![0,0;0,(b:E)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjoint, hb]⟩
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' d e := by ext i j; fin_cases i <;> fin_cases j <;> simp

def offDiagonal : E →+ Core E σ hσ where
  toFun c := ⟨!![0,c;σ c,0], by
    change adjoint σ !![0,c;σ c,0] = !![0,c;σ c,0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjoint, hσ c]⟩
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' c e := by ext i j; fin_cases i <;> fin_cases j <;> simp

omit [CharP E 2] in
/-- Every vector of the actual four-dimensional module has the three
specified root components; no source group collection is assumed. -/
theorem core_decomposition (X : Core E σ hσ) :
    ∃ d c b, X = diagonalTop E σ hσ d + offDiagonal E σ hσ c + diagonalBottom E σ hσ b := by
  have hx (i j : Fin 2) : σ (X.val j i) = X.val i j :=
    congrFun (congrFun X.property i) j
  refine ⟨⟨X.val 0 0, hx 0 0⟩, X.val 0 1, ⟨X.val 1 1, hx 1 1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalTop, offDiagonal, diagonalBottom, hx]

def upper (a : E) : SpecialLinearGroup (Fin 2) E :=
  SpecialLinearGroup.upperUnipotentHom E (Multiplicative.ofAdd a)

omit [CharP E 2] in
theorem upper_val (a : E) : (upper E a).val = !![1,a;0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, SpecialLinearGroup.upperUnipotentHom, SpecialLinearGroup.transvection_coe]

omit [CharP E 2] in
theorem upper_top (a : E) (d : K) :
    hermitianAction (conjugation E σ) hσ (upper E a) (diagonalTop E σ hσ d) =
      diagonalTop E σ hσ d := by
  apply Subtype.ext
  change (upper E a).val * !![(d:E),0;0,0] * adjoint σ (upper E a).val = !![(d:E),0;0,0]
  rw [upper_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjoint, Matrix.mul_apply, Fin.sum_univ_succ]

omit [CharP E 2] in
theorem upper_offDiagonal (a c : E) :
    hermitianAction (conjugation E σ) hσ (upper E a) (offDiagonal E σ hσ c) =
      diagonalTop E σ hσ (FourPositive.traceParameter E σ hσ a c) + offDiagonal E σ hσ c := by
  apply Subtype.ext
  change (upper E a).val * !![0,c;σ c,0] * adjoint σ (upper E a).val =
    !![a*σ c+σ a*c,0;0,0] + !![0,c;σ c,0]
  rw [upper_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjoint, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]

omit [CharP E 2] in
theorem upper_bottom (a : E) (b : K) :
    hermitianAction (conjugation E σ) hσ (upper E a) (diagonalBottom E σ hσ b) =
      diagonalTop E σ hσ (FourPositive.normParameter E σ hσ a b) +
        offDiagonal E σ hσ (a*(b:E)) + diagonalBottom E σ hσ b := by
  have hb : σ (b:E) = (b:E) := b.property
  apply Subtype.ext
  change (upper E a).val * !![0,0;0,(b:E)] * adjoint σ (upper E a).val =
    !![a*σ a*(b:E),0;0,0] + !![0,a*(b:E);σ (a*(b:E)),0] + !![0,0;0,(b:E)]
  rw [upper_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjoint, Matrix.mul_apply, Fin.sum_univ_succ, hb, mul_comm, mul_left_comm, mul_assoc]

variable {Y : Type*} [Group Y]
variable (l : SpecialLinearGroup (Fin 2) E →* Y)
variable (v : Multiplicative (Core E σ hσ) →* Y)

/-- Root maps extracted from one rank-one actor and its actual module. -/
def roots : PositiveMaps Y (Multiplicative E) (Multiplicative K) (Multiplicative E)
    (Multiplicative K) where
  A := l.comp (SpecialLinearGroup.upperUnipotentHom E)
  D := v.comp (diagonalTop E σ hσ).toMultiplicative
  C := v.comp (offDiagonal E σ hσ).toMultiplicative
  B := v.comp (diagonalBottom E σ hσ).toMultiplicative

omit [CharP E 2] in
/-- The three module roots generate the full image of the actual tensor
module. This is a consequence of its vector coordinates. -/
theorem core_image_mem_generated (X : Core E σ hσ) :
    v (Multiplicative.ofAdd X) ∈ (roots E σ hσ l v).generated := by
  obtain ⟨d,c,b,hX⟩ := core_decomposition E σ hσ X
  have hm := (roots E σ hσ l v).word_mem 1 (Multiplicative.ofAdd d)
    (Multiplicative.ofAdd c) (Multiplicative.ofAdd b)
  change (l.comp (SpecialLinearGroup.upperUnipotentHom E)) 1 *
    v (Multiplicative.ofAdd (diagonalTop E σ hσ d)) *
    v (Multiplicative.ofAdd (offDiagonal E σ hσ c)) *
    v (Multiplicative.ofAdd (diagonalBottom E σ hσ b)) ∈ _ at hm
  rw [map_one, one_mul, ← map_mul, ← map_mul] at hm
  rw [hX]
  exact hm

omit [CharP E 2] in
/-- Generation reduces to the actual simple root and the actual
complementary module image, without a positive-generation premise. -/
theorem generated_eq : (roots E σ hσ l v).generated =
    (roots E σ hσ l v).A.range ⊔ v.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro z hz
    rcases hz with ((⟨a,rfl⟩ | ⟨d,rfl⟩) | ⟨c,rfl⟩) | ⟨b,rfl⟩
    · exact Subgroup.mem_sup_left ⟨a,rfl⟩
    · exact Subgroup.mem_sup_right ⟨_,rfl⟩
    · exact Subgroup.mem_sup_right ⟨_,rfl⟩
    · exact Subgroup.mem_sup_right ⟨_,rfl⟩
  · apply sup_le
    · rintro z ⟨a,rfl⟩
      exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨a,rfl⟩)))
    · rintro z ⟨X,rfl⟩
      exact core_image_mem_generated E σ hσ l v X.toAdd

omit [CharP E 2] in
private theorem image_commute (p q : Multiplicative (Core E σ hσ)) :
    Commute (v p) (v q) := by
  show v p*v q = v q*v p
  rw [← map_mul, ← map_mul, mul_comm]

private theorem upper_image_inv (a : E) : (l (upper E a))⁻¹ = l (upper E a) := by
  rw [← map_inv]
  congr 1
  unfold upper
  rw [← map_inv]
  congr 1
  exact congrArg Multiplicative.ofAdd (CharTwo.neg_eq a)

variable (hequiv : ∀ (g : SpecialLinearGroup (Fin 2) E) (p : Core E σ hσ),
  l g * v (Multiplicative.ofAdd p) * (l g)⁻¹ =
    v (Multiplicative.ofAdd (hermitianAction (conjugation E σ) hσ g p)))

include hequiv in
/-- The two nontrivial polynomial laws are derived from tensor action;
no positive crossing equation is an input. -/
theorem relations : FourPositive.Relations E σ hσ (roots E σ hσ l v) where
  AD a d := by
    have he := hequiv (upper E a.toAdd) (diagonalTop E σ hσ d.toAdd)
    rw [upper_top] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  CD c d := image_commute E σ hσ v _ _
  BC b c := image_commute E σ hσ v _ _
  BD b d := image_commute E σ hσ v _ _
  CA a c := by
    change v (Multiplicative.ofAdd (offDiagonal E σ hσ c))*l (upper E a) =
      l (upper E a)*v (Multiplicative.ofAdd (diagonalTop E σ hσ
        (FourPositive.traceParameter E σ hσ a c)))*v (Multiplicative.ofAdd (offDiagonal E σ hσ c))
    have he := hequiv (upper E a) (offDiagonal E σ hσ c)
    rw [upper_offDiagonal] at he
    change l (upper E a)*v (Multiplicative.ofAdd (offDiagonal E σ hσ c))*(l (upper E a))⁻¹ =
      v (Multiplicative.ofAdd (diagonalTop E σ hσ _)*Multiplicative.ofAdd (offDiagonal E σ hσ c)) at he
    rw [map_mul, upper_image_inv] at he
    have he' := congrArg (fun z => (l (upper E a))⁻¹*z) he
    simp only [mul_assoc, inv_mul_cancel_left] at he'
    simpa only [upper_image_inv, mul_assoc] using he'
  BA a b := by
    change v (Multiplicative.ofAdd (diagonalBottom E σ hσ b))*l (upper E a) =
      l (upper E a)*v (Multiplicative.ofAdd (diagonalTop E σ hσ
        (FourPositive.normParameter E σ hσ a b)))*
        v (Multiplicative.ofAdd (offDiagonal E σ hσ (a*(b:E))))*
        v (Multiplicative.ofAdd (diagonalBottom E σ hσ b))
    have he := hequiv (upper E a) (diagonalBottom E σ hσ b)
    rw [upper_bottom] at he
    change l (upper E a)*v (Multiplicative.ofAdd (diagonalBottom E σ hσ b))*(l (upper E a))⁻¹ =
      v ((Multiplicative.ofAdd (diagonalTop E σ hσ _)*Multiplicative.ofAdd (offDiagonal E σ hσ _))*
        Multiplicative.ofAdd (diagonalBottom E σ hσ b)) at he
    rw [map_mul, map_mul, upper_image_inv] at he
    have he' := congrArg (fun z => (l (upper E a))⁻¹*z) he
    simp only [mul_assoc, inv_mul_cancel_left] at he'
    simpa only [upper_image_inv, mul_assoc] using he'

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FourTensor
