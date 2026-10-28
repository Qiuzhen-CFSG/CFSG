module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.ExteriorBound.Permutation
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Tactic.IntervalCases
/-!
# A binary order-five permutation basis in dimension eleven

For an operator of period five, the coprime factors `X - 1` and
`Φ₅ = X⁴ + X³ + X² + X + 1` split the space into fixed and moving kernels.
The quartic is irreducible over F₂, so its kernel carries an actual action
of `F₂[X]/(Φ₅)`. The tower law makes that kernel two-dimensional over this
field when the original and fixed dimensions are eleven and three.

In these coordinates the two lists `(e₀, αⁱe₀)` and `(e₁, αⁱe₁)`
for `0 ≤ i < 5`, together with the third fixed vector, form a basis.
An explicit invertible change of coordinates proves the basis claim;
`α⁵ = 1` proves both wraparound identities. Transport back to the original
space gives the exact cycle marking used by `Permutation` and hence its
bound on the fixed space of the literal exterior square.

This is the auxiliary linear algebra for the order-five step in
Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17. The native Golay and degree-44 applications
are assembled in the parent modules.
-/

open Polynomial Module
open scoped BigOperators
namespace Representation.MathieuM24Degree44.FiveSpace.ExteriorBound
noncomputable section
namespace CyclicBasisConstruction
abbrev K := ZMod 2
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
def q : K[X] := cyclotomic 5 K
lemma q_eq : q = X^4+X^3+X^2+X+1 := by
  rw [q, cyclotomic_prime]
  norm_num [Finset.sum_range_succ]
  ring
lemma q_irred : Irreducible q := by
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (by decide : ¬ 2 ∣ 5) (dvd_refl _)
  have hu : orderOf (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5)) = 4 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
    · decide
    · intro r hr hrd
      have hr_le : r ≤ 4 := Nat.le_of_dvd (by decide) hrd
      interval_cases r <;> try norm_num at hr <;> try norm_num at hrd <;> decide
  rw [hu, natDegree_cyclotomic, Nat.totient_prime (by decide : Nat.Prime 5)]
lemma q_deg : q.natDegree = 4 := by
  rw [q, natDegree_cyclotomic, Nat.totient_prime (by decide : Nat.Prime 5)]
lemma q_monic : q.Monic := cyclotomic.monic 5 K
lemma q_factor : (X - 1) * q = X ^ 5 - 1 := by
  rw [mul_comm]
  exact cyclotomic_prime_mul_X_sub_one K 5
lemma q_coprime : IsCoprime (X - 1) q := by
  refine ⟨X^3+X, 1, ?_⟩
  rw [q_eq]
  have htwo : (2 : K[X]) = 0 := by
    rw [← map_ofNat C, show (2 : K) = 0 by decide, map_zero]
  ring_nf
  rw [htwo]
  simp
local instance : Fact (Irreducible q) := ⟨q_irred⟩
abbrev L := AdjoinRoot q
local instance : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
local instance : Module.Finite K L := q_monic.finite_adjoinRoot
lemma L_dim : Module.finrank K L = 4 := by
  rw [(AdjoinRoot.powerBasis q_irred.ne_zero).finrank]
  exact q_deg
abbrev Flat := (Fin 3 → K) × (Fin 2 → Fin 4 → K)
def pack (x : Fin 11 → K) : Flat :=
  (![x 0+x 1+x 2+x 3+x 4, x 5+x 6+x 7+x 8+x 9, x 10],
    ![![x 0+x 4, x 1+x 4, x 2+x 4, x 3+x 4],
      ![x 5+x 9, x 6+x 9, x 7+x 9, x 8+x 9]])
def unpack (y : Flat) : Fin 11 → K :=
  let a := y.1 0 + y.2 0 0 + y.2 0 1 + y.2 0 2 + y.2 0 3
  let b := y.1 1 + y.2 1 0 + y.2 1 1 + y.2 1 2 + y.2 1 3
  ![y.2 0 0+a, y.2 0 1+a, y.2 0 2+a, y.2 0 3+a, a,
    y.2 1 0+b, y.2 1 1+b, y.2 1 2+b, y.2 1 3+b, b, y.1 2]
lemma recover_fifth (a b c d e : K) :
    (a+b+c+d+e)+(a+e)+(b+e)+(c+e)+(d+e)=e := by
  ring_nf
  simp [show (2:K)=0 by decide, show (5:K)=1 by decide]
lemma recover_fixed (t a b c d : K) :
    (a+(t+a+b+c+d))+(b+(t+a+b+c+d))+(c+(t+a+b+c+d))+
      (d+(t+a+b+c+d))+(t+a+b+c+d)=t := by
  ring_nf
  simp [show (5:K)=1 by decide, show (6:K)=0 by decide]
-- The inverse recovers the fifth coefficient from the total and four differences.
def packing : (Fin 11 → K) ≃ₗ[K] Flat where
  toFun := pack
  invFun := unpack
  left_inv x := by
    ext i
    fin_cases i <;> simp [pack, unpack, recover_fifth, CharTwo.add_cancel_right]
  right_inv y := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [pack, unpack, recover_fixed]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pack, unpack, CharTwo.add_cancel_right]
  map_add' x y := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [pack] <;> ring
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pack] <;> ring
  map_smul' c x := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [pack] <;> ring
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pack] <;> ring


abbrev Model := (Fin 3 → K) × (Fin 2 → L)
abbrev root : L := AdjoinRoot.root q
lemma root_q : root^4+root^3+root^2+root+1=0 := by
  have h : aeval root q = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simpa only [q_eq, map_add, map_pow, aeval_X, map_one] using h
lemma root_four : root^4 = 1+root+root^2+root^3 := by
  have h : root^4 + (root^3+root^2+root+1)=0 := by
    simpa only [add_assoc] using root_q
  calc
    root^4 = -(root^3+root^2+root+1) := eq_neg_of_add_eq_zero_left h
    _ = root^3+root^2+root+1 := CharTwo.neg_eq _
    _ = _ := by ring
lemma root_five : root^5=1 := by
  have h : aeval root ((X-1)*q)=0 := by
    have hq : aeval root q = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [map_mul, hq, mul_zero]
  rw [q_factor] at h
  simpa only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] using h

def fieldBasis : Basis (Fin 4) K L :=
  (AdjoinRoot.powerBasis q_irred.ne_zero).basis.reindex (finCongr q_deg)
lemma fieldBasis_apply (i : Fin 4) : fieldBasis i = root ^ i.val := by
  simp [fieldBasis]
  rfl

def expand : Flat ≃ₗ[K] Model :=
  LinearEquiv.prodCongr (LinearEquiv.refl K _) (LinearEquiv.piCongrRight fun _ => fieldBasis.equivFun.symm)
def modelEquiv : (Fin 11 → K) ≃ₗ[K] Model := packing.trans expand
def modelBasis : Basis (Fin 11) K Model := (Pi.basisFun K (Fin 11)).map modelEquiv

def column : Fin 11 → Model :=
  ![(![1,0,0], ![1,0]), (![1,0,0], ![root,0]),
    (![1,0,0], ![root^2,0]), (![1,0,0], ![root^3,0]),
    (![1,0,0], ![root^4,0]),
    (![0,1,0], ![0,1]), (![0,1,0], ![0,root]),
    (![0,1,0], ![0,root^2]), (![0,1,0], ![0,root^3]),
    (![0,1,0], ![0,root^4]), (![0,0,1], ![0,0])]
lemma modelBasis_formula (i : Fin 11) : modelBasis i =
    ((pack (Pi.single i 1)).1,
      fun j => ∑ k : Fin 4, (pack (Pi.single i 1)).2 j k • root ^ k.val) := by
  rw [modelBasis, Basis.map_apply, Pi.basisFun_apply]
  change ((pack (Pi.single i 1)).1,
    fun j => fieldBasis.equivFun.symm ((pack (Pi.single i 1)).2 j)) = _
  congr 1
  funext j
  rw [Basis.equivFun_symm_apply]
  simp only [fieldBasis_apply]
lemma modelBasis_column (i : Fin 11) : modelBasis i = column i := by
  rw [modelBasis_formula]
  fin_cases i <;> apply Prod.ext
  all_goals (ext j; fin_cases j) <;>
    simp [pack, column, Fin.sum_univ_four, root_four]

def operator (x : Model) : Model := (x.1, root • x.2)
lemma modelBasis_cycle (i : Fin 11) :
    operator (modelBasis i) = modelBasis
      (cycle i) := by
  simp only [modelBasis_column]
  fin_cases i <;> apply Prod.ext
  all_goals (ext j; fin_cases j) <;>
    simp [operator, column, cycle,
      smul_eq_mul] <;> ring_nf <;> simp [root_five]

variable {V : Type*} [AddCommGroup V] [Module K V]
def moving (f : Module.End K V) := LinearMap.ker (aeval f q)
lemma split (f : Module.End K V) (hf : f^5=1) :
    IsCompl (LinearMap.ker (f-1)) (moving f) := by
  have hd := disjoint_ker_aeval_of_isCoprime f q_coprime
  have hs := sup_ker_aeval_eq_ker_aeval_mul_of_coprime f q_coprime
  simp only [map_sub, aeval_X, map_one] at hd
  rw [q_factor] at hs
  simp only [map_sub, aeval_X, map_one, map_pow, hf, sub_self, LinearMap.ker_zero] at hs
  exact ⟨hd, codisjoint_iff.mpr hs⟩
lemma moving_stable (f : Module.End K V) : ∀ x ∈ moving f, f x ∈ moving f := by
  intro x hx
  have hc : aeval f q * f = f * aeval f q := by
    calc
      _ = aeval f (q*X) := by simp
      _ = aeval f (X*q) := by rw [mul_comm]
      _ = _ := by simp
  change aeval f q (f x) = 0
  change aeval f q x = 0 at hx
  simpa only [Module.End.mul_apply, hx, map_zero] using congrArg (fun t => t x) hc

def movingOp (f : Module.End K V) : Module.End K (moving f) := f.restrict (moving_stable f)
lemma movingOp_pow (f : Module.End K V) (n : ℕ) (v : moving f) :
    ((movingOp f ^ n) v : V) = (f^n) v := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [pow_succ', Module.End.mul_apply]; exact congrArg f hn
lemma movingOp_q (f : Module.End K V) : aeval (movingOp f) q = 0 := by
  ext v : 1
  apply Subtype.ext
  have hv : aeval f q v = 0 := v.property
  simp only [q_eq, map_add, map_pow, aeval_X, map_one, LinearMap.add_apply,
    Module.End.one_apply] at hv ⊢
  change (((movingOp f ^ 4) v : V) + ((movingOp f ^ 3) v : V) +
    ((movingOp f ^ 2) v : V) + (movingOp f v : V) + (v : V)) = 0
  have hm : (movingOp f v : V) = f v := rfl
  simpa only [movingOp_pow, hm] using hv

-- Quotient evaluation acts on the actual vector space, including its original F₂ scalars.
def fieldAction (f : Module.End K V) (hf : aeval f q = 0) : L →ₐ[K] Module.End K V :=
  Ideal.Quotient.liftₐ _ (aeval f) (by
    intro p hp
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hp
    rw [map_mul, hf, zero_mul])
lemma fieldAction_root (f : Module.End K V) (hf : aeval f q = 0) :
    fieldAction f hf (AdjoinRoot.root q) = f := by
  change aeval f X = f
  simp

lemma quarticCoordinates [FiniteDimensional K V] (f : Module.End K V)
    (hf : aeval f q = 0) (hd : Module.finrank K V = 8) :
    ∃ e : V ≃ₗ[K] (Fin 2 → L), ∀ v, e (f v) = AdjoinRoot.root q • e v := by
  let a := fieldAction f hf
  let : Module L V := Module.compHom V a.toRingHom
  let : IsScalarTower K L V := IsScalarTower.of_algebraMap_smul (fun r v => by
    change a (algebraMap K L r) v = r • v
    rw [a.commutes]
    rfl)
  let : Module.Finite L V := Module.Finite.of_restrictScalars_finite K L V
  have hdL : Module.finrank L V = 2 := by
    have h := Module.finrank_mul_finrank K L V
    rw [L_dim, hd] at h
    omega
  let b := Module.finBasisOfFinrankEq L V hdL
  refine ⟨b.equivFun.restrictScalars K, ?_⟩
  intro v
  change b.equivFun (f v) = _
  have hroot : AdjoinRoot.root q • v = f v := by
    change a (AdjoinRoot.root q) v = f v
    rw [fieldAction_root]
  rw [← hroot, map_smul]
  rfl
-- Assemble the fixed and moving coordinates before transporting the concrete basis.
lemma intertwiningEquiv [FiniteDimensional K V] (f : Module.End K V)
    (hf : f^5=1) (hd : Module.finrank K V = 11)
    (hfix : Module.finrank K (LinearMap.ker (f-1)) = 3) :
    ∃ e : Model ≃ₗ[K] V, ∀ x, f (e x) = e (operator x) := by
  let F := LinearMap.ker (f-1)
  let W := moving f
  let s : (F × W) ≃ₗ[K] V := F.prodEquivOfIsCompl W (split f hf)
  have hdW : Module.finrank K W = 8 := by
    have h := s.finrank_eq
    rw [Module.finrank_prod, hfix, hd] at h
    omega
  obtain ⟨eW, heW⟩ := quarticCoordinates (movingOp f) (movingOp_q f) hdW
  let eF := (Module.finBasisOfFinrankEq K F hfix).equivFun
  let e : Model ≃ₗ[K] V := (eF.symm.prodCongr eW.symm).trans s
  refine ⟨e, ?_⟩
  intro x
  change f ((eF.symm x.1 : V) + (eW.symm x.2 : V)) =
    (eF.symm x.1 : V) + (eW.symm (root • x.2) : V)
  rw [map_add]
  have hF : f (eF.symm x.1) = (eF.symm x.1 : V) :=
    sub_eq_zero.mp (eF.symm x.1).property
  rw [hF]
  congr 1
  have hw : movingOp f (eW.symm x.2) = eW.symm (root • x.2) := by
    apply eW.injective
    rw [heW, eW.apply_symm_apply, eW.apply_symm_apply]
  exact congrArg Subtype.val hw

end CyclicBasisConstruction

open CyclicBasisConstruction
universe u
/-- Every binary eleven-dimensional operator of period five and fixed
dimension three has the two marked five-cycles and one fixed basis vector. -/
public theorem cyclicBasisClassification : CyclicBasisClassification.{u} := by
  intro V _ _ _ f hf hd hfix
  obtain ⟨e, he⟩ := intertwiningEquiv f hf hd hfix
  refine ⟨modelBasis.map e, ?_⟩
  intro i
  simp only [Basis.map_apply, he, modelBasis_cycle]

/-- Application of the cyclic basis to the literal functorial exterior square. -/
public theorem exterior_fixed_finrank_le_of_order_five
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (f : Module.End (ZMod 2) V)
    (hf : f^5=1) (hd : Module.finrank (ZMod 2) V = 11)
    (hfix : Module.finrank (ZMod 2) (LinearMap.ker (f-1)) = 3) :
    Module.finrank (ZMod 2) (LinearMap.ker (exteriorPower.map 2 f - 1)) ≤ 11 := by
  obtain ⟨b, hb⟩ := cyclicBasisClassification f hf hd hfix
  exact exterior_fixed_finrank_le f b hb

end
end Representation.MathieuM24Degree44.FiveSpace.ExteriorBound
