module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourTensor
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourTorus
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelCells
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters
public import Mathlib.FieldTheory.Finite.Basic
public import BenderSuzuki.Converse.PSL2
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Full U₄ torus and linear Weyl laws from the Hermitian tensor action

For a fixed-product parameter (a,b), take the unique fixed-field square
root r of ab and put u=a/r. Then a=ru and b=r/u. The full torus element
is the product of the scalar ab and the SL₂ diagonal (u,u⁻¹). The tensor
action gives all four exact weights, and the same SL₂ Weyl element gives
the B/D exchange, conjugation on C, torus swap and A-root Bruhat word.
No lower bound on the field order is used.

TensorScalars constructs the scalar map from the actual source Cartan
kernel, rather than assuming scalar conjugation. CartanApplication uses
these equations on the original split quotient with its common Weyl
section. Module realization, compatibility with the other endpoint, and
the remaining nonlinear reflection laws are separate source obligations.

Source: Fong--Seitz II (8B), printed pp.201--202; the precise generator
conventions are FourPresentation.parameters and FourTensor.
-/

@[expose] public noncomputable section
open Matrix Subgroup Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FourCartan
open FourTensor
variable (E : Type*) [Field E] [Finite E] [CharP E 2]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "K" => UnitaryFourSylow.FixedField E σ
local notation "H" => FourWeyl.torusParameters E σ

def determinant : H →* Kˣ where
  toFun p := Units.mk0 ⟨(p.val.1:E)*(p.val.2:E),p.property⟩
    (fun hz => mul_ne_zero p.val.1.ne_zero p.val.2.ne_zero (congrArg Subtype.val hz))
  map_one' := by apply Units.ext; apply Subtype.ext; simp
  map_mul' p q := by apply Units.ext; apply Subtype.ext; change _ * _ = _ * _; simp; ring

def squareRoot : Kˣ →* Kˣ := Units.map (frobeniusEquiv K 2).symm.toMonoidHom

theorem squareRoot_square (a : Kˣ) : (squareRoot E σ a : K)^2 = a :=
  frobeniusEquiv_symm_pow_p K 2 a

def halfDeterminant : H →* Eˣ :=
  (Units.map (FixedBy.subfield E σ).subtype.toMonoidHom).comp
    ((squareRoot E σ).comp (determinant E σ))

def coroot : H →* Eˣ :=
  ((MonoidHom.fst Eˣ Eˣ).comp (FourWeyl.torusParameters E σ).subtype) /
    halfDeterminant E σ

@[simp] theorem halfDeterminant_fixed (p : H) :
    σ (halfDeterminant E σ p : E) = (halfDeterminant E σ p : E) :=
  (squareRoot E σ (determinant E σ p) : K).property

theorem halfDeterminant_square (p : H) :
    (halfDeterminant E σ p : E)^2 = (p.val.1:E)*(p.val.2:E) :=
  congrArg Subtype.val (squareRoot_square E σ (determinant E σ p))

theorem first_factor (p : H) :
    (p.val.1:E) = (halfDeterminant E σ p:E)*(coroot E σ p:E) := by
  simp only [coroot,MonoidHom.div_apply,MonoidHom.comp_apply,MonoidHom.coe_fst,
    Subgroup.coe_subtype,Units.val_div_eq_div_val]
  exact (mul_div_cancel₀ _ (halfDeterminant E σ p).ne_zero).symm

theorem second_factor (p : H) :
    (p.val.2:E) = (halfDeterminant E σ p:E)*(↑((coroot E σ p)⁻¹):E) := by
  simp only [coroot,MonoidHom.div_apply,MonoidHom.comp_apply,MonoidHom.coe_fst,
    Subgroup.coe_subtype,Units.val_inv_eq_inv_val,Units.val_div_eq_div_val]
  rw [inv_div,←mul_div_assoc]
  apply (eq_div_iff p.val.1.ne_zero).2
  have he := halfDeterminant_square E σ p
  simpa only [pow_two,mul_div_assoc,mul_comm] using he.symm

-- Coordinates of the fixed-product diagonal.
theorem coroot_weight (p : H) :
    (coroot E σ p:E)^2 = (p.val.1:E)/(p.val.2:E) := by
  rw [first_factor E σ p,second_factor E σ p]
  simp only [Units.val_inv_eq_inv_val]
  field_simp

omit [Finite E] [CharP E 2] in
private theorem diagonal_tensor (r : E) (u : Eˣ) (hr : σ r = r)
    (X : Matrix (Fin 2) (Fin 2) E) :
    (r*r) • (!![(u:E),0;0,(↑u⁻¹:E)] * X * adjoint σ !![(u:E),0;0,(↑u⁻¹:E)]) =
    !![r*(u:E),0;0,r*(↑u⁻¹:E)] * X * adjoint σ !![r*(u:E),0;0,r*(↑u⁻¹:E)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hr,mul_comm,mul_left_comm,mul_assoc]

theorem scalarMap_tensor (p : H) (X : Matrix (Fin 2) (Fin 2) E) :
    ((p.val.1:E)*(p.val.2:E)) •
      (!![(coroot E σ p:E),0;0,(↑((coroot E σ p)⁻¹):E)] * X *
        adjoint σ !![(coroot E σ p:E),0;0,(↑((coroot E σ p)⁻¹):E)]) =
    !![(p.val.1:E),0;0,(p.val.2:E)] * X *
      adjoint σ !![(p.val.1:E),0;0,(p.val.2:E)] := by
  have he := diagonal_tensor E σ (halfDeterminant E σ p) (coroot E σ p)
    (halfDeterminant_fixed E σ p) X
  rw [←first_factor E σ p,←second_factor E σ p,←pow_two,halfDeterminant_square] at he
  exact he

variable {Y : Type*} [Group Y]
variable (l : SpecialLinearGroup (Fin 2) E →* Y) (scalarMap : (UnitaryFourSylow.FixedField E σ)ˣ →* Y)
variable (hcl : ∀ (k : (UnitaryFourSylow.FixedField E σ)ˣ) (g : SpecialLinearGroup (Fin 2) E), Commute (scalarMap k) (l g))

def hom : H →* Y :=
  (scalarMap.noncommCoprod l hcl).comp
    ((determinant E σ).prod ((BenderSuzuki.Converse.torHom E).comp (coroot E σ)))

@[simp] theorem hom_apply (p : H) :
    hom E σ l scalarMap hcl p = scalarMap (determinant E σ p) * l (tor (coroot E σ p)) := rfl

variable (v : Multiplicative (Core E σ hσ) →* Y)
variable (hequiv : ∀ g X, l g * v (.ofAdd X) * (l g)⁻¹ =
  v (.ofAdd (hermitianAction (conjugation E σ) hσ g X)))
variable (hscalarMap : ∀ k X, scalarMap k * v (.ofAdd X) * (scalarMap k)⁻¹ = v (.ofAdd ((k : UnitaryFourSylow.FixedField E σ) • X)))

include hequiv hscalarMap in
theorem hom_core (p : H) (X : Core E σ hσ) :
    hom E σ l scalarMap hcl p * v (.ofAdd X) * (hom E σ l scalarMap hcl p)⁻¹ =
      v (.ofAdd ((determinant E σ p : K) •
        hermitianAction (conjugation E σ) hσ (tor (coroot E σ p)) X)) := by
  rw [hom_apply,_root_.mul_inv_rev]
  calc
    _ = scalarMap (determinant E σ p) *
        (l (tor (coroot E σ p)) * v (.ofAdd X) * (l (tor (coroot E σ p)))⁻¹) *
        (scalarMap (determinant E σ p))⁻¹ := by group
    _ = _ := by rw [hequiv,hscalarMap]

include hcl in
theorem hom_actor (p : H) (g : SpecialLinearGroup (Fin 2) E) :
    hom E σ l scalarMap hcl p * l g * (hom E σ l scalarMap hcl p)⁻¹ =
      l (tor (coroot E σ p) * g * (tor (coroot E σ p))⁻¹) := by
  rw [hom_apply,_root_.mul_inv_rev]
  calc
    _ = scalarMap (determinant E σ p) *
        (l (tor (coroot E σ p)) * l g * (l (tor (coroot E σ p)))⁻¹) *
        (scalarMap (determinant E σ p))⁻¹ := by group
    _ = scalarMap (determinant E σ p) * l (tor (coroot E σ p) * g * (tor (coroot E σ p))⁻¹) *
        (scalarMap (determinant E σ p))⁻¹ := by simp only [map_mul,map_inv]
    _ = _ := by rw [(hcl _ _).eq,mul_assoc,mul_inv_cancel,mul_one]

theorem hom_A (p : H) (a : E) :
    hom E σ l scalarMap hcl p * (roots E σ hσ l v).A (.ofAdd a) *
      (hom E σ l scalarMap hcl p)⁻¹ =
    (roots E σ hσ l v).A (.ofAdd (((p.val.1:E)/(p.val.2:E))*a)) := by
  change hom E σ l scalarMap hcl p * l (uni a) * (hom E σ l scalarMap hcl p)⁻¹ = l (uni _)
  rw [hom_actor,Borel_conj_uni (by rw [mem_Borel_iff]; rfl)]
  change l (uni ((coroot E σ p:E)^2*a)) = _
  rw [coroot_weight]
  rfl

private theorem scaled_top (p : H) (a : K) :
    (determinant E σ p : K) •
      hermitianAction (conjugation E σ) hσ (tor (coroot E σ p)) (diagonalTop E σ hσ a) =
      diagonalTop E σ hσ (FourPositive.normParameter E σ hσ p.val.1 a) := by
  apply Subtype.ext
  change ((p.val.1:E)*(p.val.2:E)) •
    (!![(coroot E σ p:E),0;0,(↑((coroot E σ p)⁻¹):E)] * !![(a:E),0;0,0] *
      adjoint σ !![(coroot E σ p:E),0;0,(↑((coroot E σ p)⁻¹):E)]) = _
  rw [scalarMap_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalTop,FourPositive.normParameter,adjoint,Matrix.mul_apply,Fin.sum_univ_two,mul_comm,mul_assoc]

private theorem scaled_bottom (p : H) (a : K) :
    (determinant E σ p : K) •
      hermitianAction (conjugation E σ) hσ (tor (coroot E σ p)) (diagonalBottom E σ hσ a) =
      diagonalBottom E σ hσ (FourPositive.normParameter E σ hσ p.val.2 a) := by
  apply Subtype.ext
  change ((p.val.1:E)*(p.val.2:E)) •
    (!![(coroot E σ p:E),0;0,(↑((coroot E σ p)⁻¹):E)] * !![0,0;0,(a:E)] *
      adjoint σ !![(coroot E σ p:E),0;0,(↑((coroot E σ p)⁻¹):E)]) = _
  rw [scalarMap_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalBottom,FourPositive.normParameter,adjoint,Matrix.mul_apply,Fin.sum_univ_two,mul_comm,mul_assoc]

private theorem scaled_off (p : H) (a : E) :
    (determinant E σ p : K) •
      hermitianAction (conjugation E σ) hσ (tor (coroot E σ p)) (offDiagonal E σ hσ a) =
      offDiagonal E σ hσ (((p.val.1:E)*σ (p.val.2:E))*a) := by
  apply Subtype.ext
  change ((p.val.1:E)*(p.val.2:E)) •
    (!![(coroot E σ p:E),0;0,(↑((coroot E σ p)⁻¹):E)] * !![0,a;σ a,0] *
      adjoint σ !![(coroot E σ p:E),0;0,(↑((coroot E σ p)⁻¹):E)]) = _
  rw [scalarMap_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonal,adjoint,Matrix.mul_apply,Fin.sum_univ_two,hσ (p.val.2:E),mul_comm,mul_left_comm,mul_assoc]

include hequiv hscalarMap in
theorem hom_D (p : H) (d : K) :
    hom E σ l scalarMap hcl p * (roots E σ hσ l v).D (.ofAdd d) *
      (hom E σ l scalarMap hcl p)⁻¹ =
    (roots E σ hσ l v).D (.ofAdd (FourPositive.normParameter E σ hσ p.val.1 d)) := by
  change _ * v (.ofAdd (diagonalTop E σ hσ d)) * _ = _
  rw [hom_core E σ hσ l scalarMap hcl v hequiv hscalarMap,scaled_top]
  rfl

include hequiv hscalarMap in
theorem hom_B (p : H) (b : K) :
    hom E σ l scalarMap hcl p * (roots E σ hσ l v).B (.ofAdd b) *
      (hom E σ l scalarMap hcl p)⁻¹ =
    (roots E σ hσ l v).B (.ofAdd (FourPositive.normParameter E σ hσ p.val.2 b)) := by
  change _ * v (.ofAdd (diagonalBottom E σ hσ b)) * _ = _
  rw [hom_core E σ hσ l scalarMap hcl v hequiv hscalarMap,scaled_bottom]
  rfl

include hequiv hscalarMap in
theorem hom_C (p : H) (c : E) :
    hom E σ l scalarMap hcl p * (roots E σ hσ l v).C (.ofAdd c) *
      (hom E σ l scalarMap hcl p)⁻¹ =
    (roots E σ hσ l v).C (.ofAdd (((p.val.1:E)*σ (p.val.2:E))*c)) := by
  change _ * v (.ofAdd (offDiagonal E σ hσ c)) * _ = _
  rw [hom_core E σ hσ l scalarMap hcl v hequiv hscalarMap,scaled_off]
  rfl

include hequiv hscalarMap in
theorem torusLaws : (roots E σ hσ l v).TorusLaws (hom E σ l scalarMap hcl) where
  A p a := ⟨_,hom_A E σ hσ l scalarMap hcl v p a.toAdd⟩
  D p d := ⟨_,hom_D E σ hσ l scalarMap hcl v hequiv hscalarMap p d.toAdd⟩
  C p c := ⟨_,hom_C E σ hσ l scalarMap hcl v hequiv hscalarMap p c.toAdd⟩
  B p b := ⟨_,hom_B E σ hσ l scalarMap hcl v hequiv hscalarMap p b.toAdd⟩

omit [Finite E] in
private theorem weyl_bottom (b : K) :
    hermitianAction (conjugation E σ) hσ (weyl E) (diagonalBottom E σ hσ b) =
      diagonalTop E σ hσ b := by
  apply Subtype.ext
  change !![0,1;1,0] * !![0,0;0,(b:E)] * adjoint σ !![0,1;1,0] = !![(b:E),0;0,0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjoint,Matrix.mul_apply,Fin.sum_univ_two]

omit [Finite E] in
private theorem weyl_off (c : E) :
    hermitianAction (conjugation E σ) hσ (weyl E) (offDiagonal E σ hσ c) =
      offDiagonal E σ hσ (σ c) := by
  apply Subtype.ext
  change !![0,1;1,0] * !![0,c;σ c,0] * adjoint σ !![0,1;1,0] = !![0,σ c;σ (σ c),0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjoint,Matrix.mul_apply,Fin.sum_univ_two,hσ c]

omit [Finite E] in
include hequiv in
theorem weyl_B (b : K) :
    l (weyl E) * (roots E σ hσ l v).B (.ofAdd b) * l (weyl E) =
      (roots E σ hσ l v).D (.ofAdd b) := by
  have he := hequiv (weyl E) (diagonalBottom E σ hσ b)
  rw [weyl_bottom,show (l (weyl E))⁻¹ = l (weyl E) from
    inv_eq_of_mul_eq_one_right (by rw [←map_mul,weyl_sq,map_one])] at he
  exact he

omit [Finite E] in
include hequiv in
theorem weyl_C (c : E) :
    l (weyl E) * (roots E σ hσ l v).C (.ofAdd c) * l (weyl E) =
      (roots E σ hσ l v).C (.ofAdd (σ c)) := by
  have he := hequiv (weyl E) (offDiagonal E σ hσ c)
  rw [weyl_off,show (l (weyl E))⁻¹ = l (weyl E) from
    inv_eq_of_mul_eq_one_right (by rw [←map_mul,weyl_sq,map_one])] at he
  exact he

omit [Finite E] [CharP E 2] in
@[simp] theorem determinant_swap (p : H) :
    determinant E σ (FourCells.swapParameter E σ p) = determinant E σ p := by
  apply Units.ext
  apply Subtype.ext
  exact mul_comm _ _

@[simp] theorem halfDeterminant_swap (p : H) :
    halfDeterminant E σ (FourCells.swapParameter E σ p) = halfDeterminant E σ p := by
  simp only [halfDeterminant,MonoidHom.comp_apply,determinant_swap]

@[simp] theorem coroot_swap (p : H) :
    coroot E σ (FourCells.swapParameter E σ p) = (coroot E σ p)⁻¹ := by
  rw [coroot,MonoidHom.div_apply]
  apply Units.ext
  simp only [Units.val_div_eq_div_val]
  change (p.val.2:E) / (halfDeterminant E σ (FourCells.swapParameter E σ p):E) = _
  rw [halfDeterminant_swap,second_factor E σ p]
  exact mul_div_cancel_left₀ _ (halfDeterminant E σ p).ne_zero

theorem weyl_hom (p : H) :
    l (weyl E) * hom E σ l scalarMap hcl p * l (weyl E) =
      hom E σ l scalarMap hcl (FourCells.swapParameter E σ p) := by
  have hw (u : Eˣ) : weyl E * tor u * weyl E = tor u⁻¹ := by
    ext j k
    fin_cases j <;> fin_cases k <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  simp only [hom_apply,determinant_swap,coroot_swap]
  calc
    _ = scalarMap (determinant E σ p) * (l (weyl E) * l (tor (coroot E σ p)) * l (weyl E)) := by
      rw [←mul_assoc,←(hcl _ _).eq]
      simp only [mul_assoc]
    _ = _ := by rw [←map_mul,←map_mul,hw]

omit [Finite E] [CharP E 2] in
@[simp] theorem determinant_aTorus (a : E) (ha : a ≠ 0) :
    determinant E σ (FourBruhat.aTorus E σ a ha) = 1 := by
  apply Units.ext
  apply Subtype.ext
  exact inv_mul_cancel₀ ha

@[simp] theorem halfDeterminant_aTorus (a : E) (ha : a ≠ 0) :
    halfDeterminant E σ (FourBruhat.aTorus E σ a ha) = 1 := by
  simp only [halfDeterminant,MonoidHom.comp_apply,determinant_aTorus,map_one]

@[simp] theorem coroot_aTorus (a : E) (ha : a ≠ 0) :
    coroot E σ (FourBruhat.aTorus E σ a ha) = (Units.mk0 a ha)⁻¹ := by
  simp only [coroot,MonoidHom.div_apply,halfDeterminant_aTorus,div_one]
  rfl

theorem hom_aTorus (a : E) (ha : a ≠ 0) :
    hom E σ l scalarMap hcl (FourBruhat.aTorus E σ a ha) =
      l (tor (Units.mk0 a ha)⁻¹) := by
  simp only [hom_apply,determinant_aTorus,coroot_aTorus,map_one,one_mul]

/-- The exact A-root Bruhat word of the presentation, with the constructed torus. -/
theorem weyl_A (a : E) (ha : a ≠ 0) :
    l (weyl E) * (roots E σ hσ l v).A (.ofAdd a) * l (weyl E) =
      (roots E σ hσ l v).A (.ofAdd a⁻¹) *
        hom E σ l scalarMap hcl (FourBruhat.aTorus E σ a ha) *
        l (weyl E) * (roots E σ hσ l v).A (.ofAdd a⁻¹) := by
  rw [hom_aTorus]
  change l (weyl E) * l (uni a) * l (weyl E) =
    l (uni a⁻¹) * l (tor (Units.mk0 a ha)⁻¹) * l (weyl E) * l (uni a⁻¹)
  simp only [←map_mul]
  congr 1
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,ha,CharTwo.add_self_eq_zero]


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FourCartan
