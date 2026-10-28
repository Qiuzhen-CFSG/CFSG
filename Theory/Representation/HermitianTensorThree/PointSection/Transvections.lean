module
public import Theory.Representation.HermitianTensorThree.PointSection.Movement
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The full transvection group on the Hermitian point five-space

The point radical has fixed line the first diagonal matrix. A vector is fixed
modulo that line exactly when it is supported on the first row and column.
On this five-space, the two off-diagonal entries give the quotient by the line.
Reading the remaining diagonal displacement gives a homomorphism from the
point radical to the binary dual of that quotient. The nondegenerate quadratic
trace pairing proves injectivity, and both groups have order sixteen.

This is the point-radical calculation in Aschbacher–Smith H.4.6(4,6), printed
p.382, used in 8.2.11(4) and 8.2.12, printed p.722, refs/quasithin.pdf.
The source extension transports the full action and its kernel to the original
centralizer residual. Natural and orthogonal quotient recognition are separate.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Matrix.PSL3Even.UnipotentGeometry
open Representation.HermitianTensorThree.ImageOuter
namespace Representation.HermitianTensorThree.PointSection
set_option backward.isDefEq.respectTransparency false
local instance : SMul (ZMod 2) (Space 1) := (binaryModule 1).toSMul

/-- The literal central line. -/
def line : Submodule (ZMod 2) (Space 1) := Submodule.span (ZMod 2) {pointVector}

theorem mem_line_iff (X : Space 1) : X ∈ line ↔ X = 0 ∨ X = pointVector := by
  rw [line,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a,rfl⟩
    fin_cases a <;> simp
  · rintro (rfl|rfl)
    · exact ⟨0,_root_.zero_smul _ _⟩
    · exact ⟨1,_root_.one_smul _ _⟩

theorem point_fixed_eq_line :
    fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.point 1) = line := by
  ext X
  rw [UnipotentRadicals.mem_point_fixed_iff,mem_line_iff]
  constructor
  · rintro ⟨h11,h22,h01,h02,h12⟩
    have hd : (X.val 0 0)^2 = X.val 0 0 := entry_conjugate 1 X 0 0
    rcases eq_zero_or_one_of_sq_eq_self hd with h00|h00
    · left
      apply (coordinates 1).injective
      apply Prod.ext
      · ext i; fin_cases i <;> assumption
      · ext i; fin_cases i <;> assumption
    · right
      apply (coordinates 1).injective
      apply Prod.ext
      · ext i; fin_cases i <;> assumption
      · ext i; fin_cases i <;> assumption
  · rintro (rfl|rfl) <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem line_le_moved : line ≤ moved := by
  rw [line,Submodule.span_le]
  intro X hX
  rw [Set.mem_singleton_iff] at hX
  subst X
  exact (mem_moved _).mpr ⟨rfl,rfl,rfl⟩

/-- The actual second fixed space of the point radical is the five-space. -/
theorem displacement_mem_line_iff (X : Space 1) :
    (∀ t ∈ UnipotentRadicals.point 1, t X - X ∈ line) ↔ X ∈ moved := by
  have hz (Y : Space 1) (hY : Y ∈ line) : Y.val 0 1=0 ∧ Y.val 0 2=0 := by
    rcases (mem_line_iff Y).mp hY with rfl|rfl <;> exact ⟨rfl,rfl⟩
  constructor
  · intro h
    have h1 := hz _ (h (UnipotentRadicals.unipotentHom 1 ⟨1,0,0⟩)
      (mem_map_of_mem _ ((mem_V₁ _ _).mpr rfl)))
    have h2 := hz _ (h (UnipotentRadicals.unipotentHom 1 ⟨0,0,1⟩)
      (mem_map_of_mem _ ((mem_V₁ _ _).mpr rfl)))
    change (matrix (E 1) ⟨1,0,0⟩ * X.val * adjoint 1 (matrix (E 1) ⟨1,0,0⟩)) 0 1-X.val 0 1=0 ∧
      (matrix (E 1) ⟨1,0,0⟩ * X.val * adjoint 1 (matrix (E 1) ⟨1,0,0⟩)) 0 2-X.val 0 2=0 at h1
    change (matrix (E 1) ⟨0,0,1⟩ * X.val * adjoint 1 (matrix (E 1) ⟨0,0,1⟩)) 0 1-X.val 0 1=0 ∧
      (matrix (E 1) ⟨0,0,1⟩ * X.val * adjoint 1 (matrix (E 1) ⟨0,0,1⟩)) 0 2-X.val 0 2=0 at h2
    simp [matrix,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three] at h1 h2
    exact (mem_moved X).mpr ⟨h1.1,h2.2,h1.2⟩
  · intro hX t ht
    obtain ⟨u,hu,rfl⟩ := ht
    have hy := (mem_V₁ _ _).mp hu
    obtain ⟨h11,h22,h12⟩ := (mem_moved X).mp hX
    have h21 : X.val 2 1=0 := by rw [←entry_conjugate 1 X 2 1,h12,map_zero]
    rw [←point_fixed_eq_line,UnipotentRadicals.mem_point_fixed_iff]
    change ((matrix (E 1) u * X.val * adjoint 1 (matrix (E 1) u)) 1 1-X.val 1 1=0) ∧
      ((matrix (E 1) u * X.val * adjoint 1 (matrix (E 1) u)) 2 2-X.val 2 2=0) ∧
      ((matrix (E 1) u * X.val * adjoint 1 (matrix (E 1) u)) 0 1-X.val 0 1=0) ∧
      ((matrix (E 1) u * X.val * adjoint 1 (matrix (E 1) u)) 0 2-X.val 0 2=0) ∧
      ((matrix (E 1) u * X.val * adjoint 1 (matrix (E 1) u)) 1 2-X.val 1 2=0)
    simp [matrix,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,hy,h11,h22,h12,h21]

/-- The first row is the quotient by the actual central line. -/
def row : moved →ₗ[ZMod 2] (Fin 2 → E 1) where
  toFun X i := X.val.val 0 i.succ
  map_add' _ _ := rfl
  map_smul' a X := by fin_cases a <;> simp; rfl

theorem row_surjective : Function.Surjective row := by
  intro v
  refine ⟨movedCoordinates.symm (0,v 0,v 1),?_⟩
  ext i
  fin_cases i <;> rfl

theorem row_kernel (X : moved) : row X = 0 ↔ X.val ∈ line := by
  rw [←point_fixed_eq_line,UnipotentRadicals.mem_point_fixed_iff]
  constructor
  · intro h
    have hx := (mem_moved X.val).mp X.property
    exact ⟨hx.1,hx.2.1,congrFun h 0,congrFun h 1,hx.2.2⟩
  · rintro ⟨_,_,h0,h1,_⟩
    ext i
    fin_cases i <;> assumption

private def binaryField : F 1 ≃+* ZMod 2 := by
  let : Fintype (F 1) := Fintype.ofFinite _
  exact (ZMod.ringEquiv (F 1) (by rw [←Nat.card_eq_fintype_card,card_F]; norm_num)).symm

/-- Reading the central diagonal as a binary coefficient. -/
def diagonal : Space 1 →ₗ[ZMod 2] ZMod 2 where
  toFun X := binaryField ⟨X.val 0 0,entry_conjugate 1 X 0 0⟩
  map_add' X Y := by
    rw [←map_add]
    apply congrArg binaryField
    exact Subtype.ext rfl
  map_smul' a X := by
    fin_cases a
    · change binaryField ⟨((0 : ZMod 2) • X).val 0 0,_⟩ = (0 : ZMod 2) • _
      simp only [_root_.zero_smul]
      exact (congrArg binaryField (show (⟨0,_⟩ : F 1) = 0 from Subtype.ext rfl)).trans (map_zero _)
    · change binaryField ⟨((1 : ZMod 2) • X).val 0 0,_⟩ = (1 : ZMod 2) • _
      simp only [_root_.one_smul]

@[simp] theorem diagonal_point : diagonal pointVector = 1 := by
  change binaryField _ = 1
  exact (congrArg binaryField (show (⟨pointVector.val 0 0,_⟩ : F 1) = 1 from Subtype.ext rfl)).trans (map_one _)

theorem line_coefficient (X : Space 1) (hX : X ∈ line) : diagonal X • pointVector = X := by
  rcases (mem_line_iff X).mp hX with rfl|rfl
  · rw [map_zero,_root_.zero_smul]
  · rw [diagonal_point,_root_.one_smul]


/-- A section of the row map, with zero central diagonal. -/
def rowLift : (Fin 2 → E 1) →ₗ[ZMod 2] moved where
  toFun v := movedCoordinates.symm (0,v 0,v 1)
  map_add' v w := by
    apply Subtype.ext
    apply (coordinates 1).injective
    change (coordinates 1) ((coordinates 1).symm (0,![(v+w) 0,(v+w) 1,0])) =
      (coordinates 1) ((coordinates 1).symm (0,![v 0,v 1,0]) + (coordinates 1).symm (0,![w 0,w 1,0]))
    simp only [map_add,LinearEquiv.apply_symm_apply]
    ext i <;> fin_cases i <;> simp
  map_smul' a v := by
    fin_cases a <;> simp
    apply Subtype.ext
    apply (coordinates 1).injective
    change (coordinates 1) ((coordinates 1).symm (0,![0,0,0])) = (coordinates 1) 0
    simp

theorem row_rowLift (v : Fin 2 → E 1) : row (rowLift v) = v := by
  ext i
  fin_cases i <;> rfl

/-- The radical's central displacement functional on the four-space. -/
def functional (t : UnipotentRadicals.point 1) : Module.Dual (ZMod 2) (Fin 2 → E 1) :=
  diagonal.comp ((t.val.toLinearMap - LinearMap.id).comp (moved.subtype.comp rowLift))

/-- The action retains the central coordinate, with the row quotient giving
its exact transvection parameter. -/
theorem functional_action (t : UnipotentRadicals.point 1) (X : moved) :
    t.val X.val = X.val + functional t (row X) • pointVector := by
  let Y := rowLift (row X)
  have hr : row (X-Y) = 0 := by rw [map_sub,row_rowLift,sub_self]
  have hz : X.val-Y.val ∈ line := (row_kernel (X-Y)).mp hr
  have hf : t.val (X.val-Y.val) = X.val-Y.val := by
    rw [←point_fixed_eq_line] at hz
    exact hz t
  have he : t.val Y.val-Y.val = t.val X.val-X.val := by
    rw [map_sub] at hf
    exact (sub_eq_sub_iff_sub_eq_sub.mp hf).symm
  have hd : t.val Y.val-Y.val ∈ line :=
    (displacement_mem_line_iff Y.val).mpr Y.property t.val t.property
  have hc := line_coefficient _ hd
  change t.val X.val = X.val + diagonal (t.val Y.val-Y.val) • pointVector
  rw [hc,he,add_sub_cancel]

/-- The point radical acts faithfully on the five-space. -/
theorem point_faithful_on_moved (t : UnipotentRadicals.point 1)
    (ht : ∀ X : moved, t.val X.val = X.val) : t = 1 := by
  obtain ⟨u,hu,he⟩ := t.property
  have hy := (mem_V₁ _ _).mp hu
  have hrel (a b : E 1) :
      u.x * sigma 1 a + a * sigma 1 u.x + u.c * sigma 1 b + b * sigma 1 u.c = 0 := by
    let X := rowLift ![a,b]
    have hh := congrArg (fun Y : Space 1 => Y.val 0 0) (ht X)
    rw [←he] at hh
    change (matrix (E 1) u * X.val.val * adjoint 1 (matrix (E 1) u)) 0 0 = X.val.val 0 0 at hh
    simpa [X,rowLift,movedCoordinates,coordinates,matrix,adjoint,Matrix.mul_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_three,hy,add_assoc,add_comm,add_left_comm] using hh
  have hzero (a : E 1) (ha : ∀ b, a*sigma 1 b+b*sigma 1 a=0) : a=0 := by
    obtain ⟨s,hs⟩ := FieldSections.exists_trace_one 1
    have heq : a*sigma 1 (a*s)+(a*s)*sigma 1 a = a*sigma 1 a*(sigma 1 s+s) := by
      rw [map_mul]
      ring
    have hh : a*sigma 1 a=0 := by
      have h := ha (a*s)
      rw [heq,hs,mul_one] at h
      exact h
    exact (mul_eq_zero.mp hh).elim id
      (fun h => (sigma 1).injective (h.trans (map_zero _).symm))
  have hx : u.x=0 := hzero u.x (fun a => by simpa using hrel a 0)
  have hc : u.c=0 := hzero u.c (fun b => by simpa using hrel 0 b)
  have hu1 : u=1 := U.ext hx hy hc
  apply Subtype.ext
  rw [←he,hu1,map_one]
  rfl

/-- Multiplication of point actors adds their exact displacement functionals. -/
def dualHom : UnipotentRadicals.point 1 →* Multiplicative (Module.Dual (ZMod 2) (Fin 2 → E 1)) where
  toFun t := Multiplicative.ofAdd (functional t)
  map_one' := by
    apply LinearMap.ext
    intro v
    change diagonal ((1 : Space 1 ≃ₗ[ZMod 2] Space 1) (rowLift v).val-(rowLift v).val)=0
    simp
  map_mul' t s := by
    apply LinearMap.ext
    intro v
    let X := rowLift v
    have ht := functional_action t X
    have hs := functional_action s X
    have hp : t.val pointVector=pointVector := by
      have h : pointVector ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.point 1) := by
        rw [point_fixed_eq_line]
        exact (mem_line_iff _).mpr (Or.inr rfl)
      exact h t
    change diagonal (t.val (s.val X.val)-X.val)=functional t v+functional s v
    rw [hs,map_add,LinearEquiv.map_smul,hp,ht]
    have hr : row X=v := row_rowLift v
    rw [hr]
    simp only [add_assoc,add_sub_cancel_left,map_add,LinearMap.map_smul,diagonal_point,smul_eq_mul,mul_one]

theorem dualHom_injective : Function.Injective dualHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro t ht
  apply mem_bot.mpr
  apply point_faithful_on_moved t
  intro X
  have hf : functional t=0 := ht
  rw [functional_action,hf,LinearMap.zero_apply,_root_.zero_smul,add_zero]

theorem dualHom_surjective : Function.Surjective dualHom := by
  have hc : Nat.card (UnipotentRadicals.point 1) = 16 := by
    rw [UnipotentRadicals.point,card_map_of_injective (UnipotentRadicals.unipotentHom_injective 1),
      card_V₁,card_E]
    norm_num
  have hd : Module.finrank (ZMod 2) (Fin 2 → E 1) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 2 → E 1)
    rw [Nat.card_zmod,Nat.card_fun,Nat.card_fin,card_E] at hh
    exact (Nat.pow_right_inj (by decide : 1<2)).mp (show 2^Module.finrank (ZMod 2) (Fin 2 → E 1)=2^4 from hh.symm)
  have he : Nat.card (Multiplicative (Module.Dual (ZMod 2) (Fin 2 → E 1))) = 16 := by
    change Nat.card (Module.Dual (ZMod 2) (Fin 2 → E 1))=16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Subspace.dual_finrank_eq,hd]
    norm_num
  let : Finite (Module.Dual (ZMod 2) (Fin 2 → E 1)) := Finite.of_injective _ DFunLike.coe_injective
  exact ((Nat.bijective_iff_injective_and_card dualHom).mpr ⟨dualHom_injective,hc.trans he.symm⟩).surjective

/-- The full point radical, not just a subgroup of transvections, is the
additive dual of the marked four-dimensional row quotient. -/
def pointDualEquiv : UnipotentRadicals.point 1 ≃*
    Multiplicative (Module.Dual (ZMod 2) (Fin 2 → E 1)) :=
  MulEquiv.ofBijective dualHom ⟨dualHom_injective,dualHom_surjective⟩


/-- The dual equivalence describes the literal matrix action, with its
central vector and quotient coordinates retained. -/
theorem pointDualEquiv_action (t : UnipotentRadicals.point 1) (X : moved) :
    t.val X.val = X.val + (pointDualEquiv t).toAdd (row X) • pointVector :=
  functional_action t X

end Representation.HermitianTensorThree.PointSection
