module
public import Theory.Representation.Mathieu.M22James.NoFF
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A four-element bound for the triple Mathieu pointwise fixer

A square-one subgroup fixing the whole fixed space of the native involution
has Hermitian displacements parameterized by two binary diagonal entries and
one F4 entry. Their products vanish, so the parameters add under group
multiplication. Nonidentity involutions have rank two; the resulting
anisotropic binary subspace of Hermitian two-by-two matrices has dimension
at most two. A finite sixteen-parameter calculation proves the last bound.

MathieuTripleBounds uses this to exclude inner near-offenders, supplying the
missing local premise of the original-orbit triple-cover elimination.
Source: Aschbacher--Smith H.12.1(12), Table 7.2.1 and7.5.2, pp.394,698--700.
-/

@[expose] public section
open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu.M22TripleCover.Unitary
open Sporadic.Mathieu.M22TripleCover.NoFF
open scoped Matrix
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTriple
private abbrev Params := (ZMod 2 × ZMod 2) × F

private def smallMatrix (p : Params) : Matrix (Fin 2) (Fin 2) F :=
  !![algebraMap (ZMod 2) F p.1.1, p.2; fieldFrobenius p.2, algebraMap (ZMod 2) F p.1.2]

private def rows : Matrix (Fin 2) (Fin 6) F :=
  (!![1,1,0,3,2,0; 0,0,1,0,0,2] : Matrix _ _ ℕ).map fieldEntry

private def columns : Matrix (Fin 6) (Fin 2) F := rows.transpose.map fieldFrobenius

private def displacement (p : Params) : Matrix (Fin 6) (Fin 6) F := columns * smallMatrix p * rows

private def parameters (D : Matrix (Fin 6) (Fin 6) F) : Params := ((D 0 0 |>.re, D 2 2 |>.re), D 0 2)

private theorem displacement_hermitian (p : Params) :
    (displacement p).transpose.map fieldFrobenius = displacement p := by
  ext i j <;> revert p i j <;> decide +kernel

private theorem displacement_fixed (p : Params) (k : Fin 4) : displacement p *ᵥ fixedBasis k = 0 := by
  apply funext
  intro i
  revert p k i
  decide +kernel

private theorem displacement_parameters (p : Params) : parameters (displacement p) = p := by
  revert p
  decide +kernel

private theorem fixed_re_eq (x : F) (h : fieldFrobenius x = x) :
    algebraMap (ZMod 2) F x.re = x := by
  revert x
  decide +kernel

private theorem displacement_eq (D : Matrix (Fin 6) (Fin 6) F)
    (hh : D.transpose.map fieldFrobenius = D)
    (hf : ∀ k, D *ᵥ fixedBasis k = 0) : displacement (parameters D) = D := by
  apply commonFixer_ext _ _ (displacement_hermitian _) hh (displacement_fixed _) hf
  · have he := congrArg (fun p : Params => p.1.1) (displacement_parameters (parameters D))
    have hd := congrArg (fun M => M 0 0) (displacement_hermitian (parameters D))
    have hD := congrArg (fun M => M 0 0) hh
    exact (fixed_re_eq _ hd).symm.trans ((congrArg (algebraMap (ZMod 2) F) he).trans (fixed_re_eq _ hD))
  · have he := congrArg (fun p : Params => p.1.2) (displacement_parameters (parameters D))
    have hd := congrArg (fun M => M 2 2) (displacement_hermitian (parameters D))
    have hD := congrArg (fun M => M 2 2) hh
    exact (fixed_re_eq _ hd).symm.trans ((congrArg (algebraMap (ZMod 2) F) he).trans (fixed_re_eq _ hD))
  · exact congrArg Prod.snd (displacement_parameters (parameters D))

private theorem displacement_mul (p q : Params) : displacement p * displacement q = 0 := by
  have hz : rows * columns = 0 := by decide +kernel
  simp only [displacement, Matrix.mul_assoc]
  rw [←Matrix.mul_assoc rows columns, hz, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.mul_zero]

private theorem displacement_add (p q : Params) : displacement (p+q) = displacement p + displacement q := by
  have hs : smallMatrix (p+q) = smallMatrix p + smallMatrix q := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [smallMatrix, map_add]
  simp only [displacement, hs, Matrix.mul_add, Matrix.add_mul]

private theorem parameters_add (D E : Matrix (Fin 6) (Fin 6) F) :
    parameters (D+E) = parameters D + parameters E := by rfl

private theorem displacement_zero : displacement 0 = 0 := by decide +kernel

private def good (p : Params) : Prop := p = 0 ∨ (smallMatrix p).det = 1
private instance (p : Params) : Decidable (good p) := inferInstanceAs (Decidable (p = 0 ∨ (smallMatrix p).det = 1))

private theorem good_triple (x y z : Params)
    (hx : good x) (hy : good y) (hz : good z)
    (hxy : good (x+y)) (hxz : good (x+z)) (hyz : good (y+z))
    (hxyz : good (x+y+z)) :
    x = 0 ∨ y = 0 ∨ y = x ∨ z = 0 ∨ z = x ∨ z = y ∨ z = x+y := by
  have cert : ∀ x y z : Params,
      (!(decide (good x) && decide (good y) && decide (good z) &&
        decide (good (x+y)) && decide (good (x+z)) && decide (good (y+z)) &&
        decide (good (x+y+z))) ||
      decide (x = 0 ∨ y = 0 ∨ y = x ∨ z = 0 ∨ z = x ∨ z = y ∨ z = x+y)) = true := by
    decide +kernel
  have hc := cert x y z
  simpa only [hx,hy,hz,hxy,hxz,hyz,hxyz,decide_true,Bool.and_self,
    Bool.not_true,Bool.false_or,decide_eq_true_eq] using hc

private theorem singular_factor (p : Params) (h : (smallMatrix p).det = 0) :
    ∃ u v : Fin 2 → F, smallMatrix p = vecMulVec u v := by
  revert p
  decide +kernel

private theorem good_of_rank_two (p : Params) (hr : (displacement p).rank = 2) : good p := by
  have hd : (smallMatrix p).det = 0 ∨ (smallMatrix p).det = 1 := by
    clear hr
    revert p
    decide +kernel
  rcases hd with hd | hd
  · obtain ⟨u,v,he⟩ := singular_factor p hd
    have hb := (Matrix.rank_mul_le_left (columns * smallMatrix p) rows).trans
      (Matrix.rank_mul_le_right columns (smallMatrix p))
    change (displacement p).rank ≤ (smallMatrix p).rank at hb
    rw [he] at hb
    have hh := hb.trans (Matrix.rank_vecMulVec_le u v)
    omega
  · exact Or.inr hd

noncomputable section

private theorem good_group_card {A : Type*} [Group A] [Finite A]
    (f : A → Params) (hi : Function.Injective f)
    (_h1 : f 1 = 0) (hm : ∀ a b, f (a*b) = f a + f b)
    (hg : ∀ a, good (f a)) : Nat.card A ≤ 4 := by
  classical
  have bound (s : Finset Params) (hs : ∀ a, f a ∈ s) : Nat.card A ≤ s.card := by
    let j : A → s := fun a => ⟨f a,hs a⟩
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      Nat.card_le_card_of_injective j (fun a b he => hi (congrArg Subtype.val he))
  by_cases ha : ∀ a, f a = 0
  · have hb := bound {0} (fun a => by simp [ha a])
    simpa using hb.trans (by decide : ({0} : Finset Params).card ≤ 4)
  push Not at ha
  obtain ⟨a,ha⟩ := ha
  by_cases hb : ∀ b, f b = 0 ∨ f b = f a
  · apply (bound {0,f a} (fun b => by rcases hb b with h | h <;> simp [h])).trans
    exact (Finset.card_insert_le _ _).trans (by simp)
  push Not at hb
  obtain ⟨b,hb0,hba⟩ := hb
  have hc (c : A) : f c ∈ ({0,f a,f b,f a+f b} : Finset Params) := by
    have ht := good_triple (f a) (f b) (f c) (hg a) (hg b) (hg c)
      ((hm a b) ▸ hg (a*b)) ((hm a c) ▸ hg (a*c)) ((hm b c) ▸ hg (b*c))
      (by rw [←hm,←hm]; exact hg _)
    simp only [ha,hb0,hba,false_or] at ht
    rcases ht with h | h | h | h <;> simp [h]
  apply (bound _ hc).trans
  calc
    ({0,f a,f b,f a+f b} : Finset Params).card ≤ ({f a,f b,f a+f b} : Finset Params).card+1 := Finset.card_insert_le _ _
    _ ≤ (({f b,f a+f b} : Finset Params).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) _
    _ ≤ ((({f a+f b} : Finset Params).card+1)+1)+1 := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) _) _
    _ = 4 := by simp


open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu
private theorem actionMatrix_mulVec (g : M22TripleCover) (v : Sporadic.Mathieu.M22TripleCover.Unitary.Vector) :
    (matrixAction g : Matrix (Fin 6) (Fin 6) F) *ᵥ v = fieldAction g v := by
  change LinearMap.toMatrix' (fieldAction g) *ᵥ v = _
  exact LinearMap.toMatrix'_mulVec _ _

private theorem involution_displacement_hermitian (g : M22TripleCover) (hs : g ^ 2 = 1) :
    ((matrixAction g : Matrix (Fin 6) (Fin 6) F) - 1).transpose.map fieldFrobenius =
      (matrixAction g : Matrix (Fin 6) (Fin 6) F) - 1 := by
  let M : Matrix (Fin 6) (Fin 6) F := matrixAction g
  have hsq : M * M = 1 := by
    change ((matrixAction g * matrixAction g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1
    rw [← map_mul, ← pow_two, hs, map_one]
    rfl
  have hm : M.transpose.map fieldFrobenius = M := by
    calc
      M.transpose.map fieldFrobenius = M.transpose.map fieldFrobenius * (M * M) := by
        rw [hsq, mul_one]
      _ = (M.transpose.map fieldFrobenius * M) * M := (mul_assoc _ _ _).symm
      _ = M := by rw [matrixAction_unitary, one_mul]
  apply Matrix.ext
  intro i j
  change fieldFrobenius (M j i - (1 : Matrix (Fin 6) (Fin 6) F) j i) =
    M i j - (1 : Matrix (Fin 6) (Fin 6) F) i j
  rw [map_sub]
  have he : fieldFrobenius (M j i) = M i j := congrArg (fun N => N i j) hm
  rw [he]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

private theorem matrix_displacement_injective {G : Type*} [Group G]
    (f : G →* GL (Fin 6) F) (hf : Function.Injective f) :
    Function.Injective (fun g => (f g : Matrix (Fin 6) (Fin 6) F) - 1) := by
  intro g h he
  apply hf
  apply Units.ext
  exact sub_left_inj.mp he

/-- A square-one subgroup fixing the native involution's whole fixed space
has order at most four. Its displacements form an anisotropic binary
subspace of the sixteen Hermitian two-by-two matrices. -/
theorem commonFixer_card_le_four (A : Subgroup M22TripleCover)
    (hsq : ∀ a : A, (a : M22TripleCover) ^ 2 = 1)
    (hf : ∀ a : A, ∀ v, fieldAction coreGeneratorB v = v →
      fieldAction (a : M22TripleCover) v = v) : Nat.card A ≤ 4 := by
  let D (a : A) : Matrix (Fin 6) (Fin 6) F := matrixAction (a : M22TripleCover) - 1
  have hi : Function.Injective D := by
    intro a b he
    exact Subtype.ext (matrix_displacement_injective matrixAction matrixAction_faithful he)
  have hh (a : A) : (D a).transpose.map fieldFrobenius = D a :=
    involution_displacement_hermitian _ (hsq a)
  have hk (a : A) (k : Fin 4) : D a *ᵥ fixedBasis k = 0 := by
    dsimp only [D]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, actionMatrix_mulVec]
    apply sub_eq_zero.mpr
    apply hf a
    rw [← actionMatrix_mulVec, matrixAction_generatorB]
    exact generatorB_fixedBasis k
  have he (a : A) : displacement (parameters (D a)) = D a := displacement_eq _ (hh a) (hk a)
  have hz (a b : A) : D a * D b = 0 := by
    rw [←he a,←he b]
    exact displacement_mul _ _
  have hm (a b : A) : D (a*b) = D a+D b := by
    have hd : (matrixAction (a : M22TripleCover) : Matrix (Fin 6) (Fin 6) F) = D a+1 := by simp [D]
    have hd' : (matrixAction (b : M22TripleCover) : Matrix (Fin 6) (Fin 6) F) = D b+1 := by simp [D]
    change (matrixAction ((a : M22TripleCover)*(b : M22TripleCover)) : Matrix (Fin 6) (Fin 6) F)-1 = _
    rw [map_mul, Units.val_mul,hd,hd',Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,
      hz,Matrix.one_mul,Matrix.mul_one,Matrix.one_mul,zero_add,←add_assoc,add_sub_cancel_right]
  apply good_group_card (fun a => parameters (D a))
  · intro a b hab
    apply hi
    exact (he a).symm.trans ((congrArg displacement hab).trans (he b))
  · change parameters ((matrixAction (1 : M22TripleCover) : Matrix (Fin 6) (Fin 6) F)-1) = 0
    rw [map_one,Matrix.GeneralLinearGroup.coe_one,sub_self]
    rfl
  · intro a b
    rw [hm,parameters_add]
  · intro a
    by_cases ha : (a : M22TripleCover) = 1
    · left
      dsimp only [D]
      rw [ha,map_one,Matrix.GeneralLinearGroup.coe_one,sub_self]
      rfl
    · apply good_of_rank_two
      rw [he]
      exact matrixRank_involution _ (orderOf_eq_prime (hsq a) ha)

end
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTriple
