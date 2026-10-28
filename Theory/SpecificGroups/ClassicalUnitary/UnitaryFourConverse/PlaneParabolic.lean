module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.TwoCore
public import Theory.SpecificGroups.GL2.OddPrimeRank
public import Theory.GroupTheory.QuasithinBasic

/-!
# Local properties of the full unitary-four plane parabolic

For the antidiagonal Hermitian form over a finite field of characteristic two,
the full plane stabilizer is two-local, has odd-prime ranks at most two, and
satisfies `C_P(O₂(P)) ≤ O₂(P)`. These statements hold for every involution of
the field, so in particular for the Frobenius involution of a field of order
`(2^n)^2`, including `n = 1`.

The restriction kernel in the full parabolic is canonically the already
parametrized Hermitian radical in the determinant-one local factor. Its
exponent is two, so odd elementary abelian groups embed under restriction to
GL₂. Its common fixed space is exactly the coordinate plane, giving its full
ambient normalizer. Finally, commuting with the two diagonal Hermitian matrix
units and the off-diagonal Hermitian matrix forces an upper triangular matrix
with one common diagonal entry. Determinant one and characteristic two make
that entry one. Thus the restriction kernel is self-centralizing in the full
parabolic; its containment in the intrinsic two-core gives the required bound.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed pp.4 and 482 of `refs/quasithin.pdf`; the parabolic
local structure in GLS, volume 3, §§3.1–3.2. This proves the plane-parabolic
input to the converse; the two-local cover and the point-parabolic calculation
belong to the assembly and its other inputs.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical
open scoped IsMulCommutative
open scoped Pointwise

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PlaneParabolic
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- Kernel of restriction to the invariant plane, inside the full parabolic. -/
def kernel : Subgroup (planeParabolicSU F (form F σ hσ)) :=
  (restriction F (form F σ hσ)).ker

/-- Normality is intrinsic to the full parabolic. -/
instance kernel_normal : (kernel F σ hσ).Normal :=
  inferInstanceAs (restriction F (form F σ hσ)).ker.Normal

omit [CharP F 2] in
/-- The restriction kernel has identity upper-left block. -/
theorem mem_kernel (g : planeParabolicSU F (form F σ hσ)) :
    g ∈ kernel F σ hσ ↔
      g.val.val.val 0 0 = 1 ∧ g.val.val.val 0 1 = 0 ∧
      g.val.val.val 1 0 = 0 ∧ g.val.val.val 1 1 = 1 := by
  change restriction F (form F σ hσ) g = 1 ↔ _
  rw [Units.ext_iff]
  change restrictionMatrix F (form F σ hσ) g = 1 ↔ _
  constructor
  · intro h
    exact ⟨congrArg (fun M => M 0 0) h, congrArg (fun M => M 0 1) h,
      congrArg (fun M => M 1 0) h, congrArg (fun M => M 1 1) h⟩
  · rintro ⟨h00,h01,h10,h11⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [restrictionMatrix, h00,h01,h10,h11]

/-- The kernels in the full parabolic and its determinant-one factor consist
of the same ambient matrices. No surjectivity of restriction is needed. -/
def kernelEquivRadical : kernel F σ hσ ≃* radical F σ hσ where
  toFun g := ⟨⟨g.val.val, (mem_localFactor F _ _).mpr ⟨g.val.property, by
    have hg : restriction F (form F σ hσ) g.val = 1 := g.property
    have hd := congrArg (fun A : GL (Fin 2) F => A.val.det) hg
    simpa using hd⟩⟩, (mem_radical F σ hσ _).mpr ((mem_kernel F σ hσ _).mp g.property)⟩
  invFun g := ⟨⟨g.val.val, local_le_planeParabolic F _ g.val.property⟩,
    (mem_kernel F σ hσ _).mpr ((mem_radical F σ hσ _).mp g.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The full restriction kernel has exponent dividing two. -/
theorem kernel_sq (g : kernel F σ hσ) : g ^ 2 = 1 := by
  apply (kernelEquivRadical F σ hσ).injective
  simpa using radical_sq F σ hσ (kernelEquivRadical F σ hσ g)

/-- The full restriction kernel is a two-group. -/
theorem kernel_isTwoGroup : IsPGroup 2 (kernel F σ hσ) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  exact ⟨1, by simpa using kernel_sq F σ hσ g⟩

/-- Odd elementary abelian subgroups embed in GL₂ under plane restriction. -/
theorem odd_primeRank_le_two (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p (planeParabolicSU F (form F σ hσ)) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  let f := restriction F (form F σ hσ)
  have hdis : Disjoint E (kernel F σ hσ) :=
    IsPGroup.disjoint_of_ne p 2 (by rintro rfl; exact (by decide : ¬ Odd 2) ho)
      E (kernel F σ hσ) (IsElementaryAbelian.isPGroup p E) (kernel_isTwoGroup F σ hσ)
  have hinj : Function.Injective (f.comp E.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdis x.property hx
  let : IsElementaryAbelian p (E.map f) := IsElementaryAbelian.map f
  have hcard := GeneralLinearGroup.elementaryAbelian_card_le_sq_of_odd F ho (E.map f)
  have hc : Nat.card E = Nat.card (E.map f) := by
    have hc := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    simpa only [MonoidHom.range_comp, Subgroup.range_subtype] using hc
  exact hc.trans_le hcard

/-- A Hermitian unipotent regarded as an element of the full parabolic. -/
def unipotentPlane (X : hermitianMatrices F σ) : planeParabolicSU F (form F σ hσ) :=
  ⟨unipotentSU F σ hσ X,
    local_le_planeParabolic F _ (unipotentSU_mem_local F σ hσ X)⟩

/-- Every Hermitian unipotent acts trivially on the coordinate plane. -/
theorem unipotentPlane_mem_kernel (X : hermitianMatrices F σ) :
    unipotentPlane F σ hσ X ∈ kernel F σ hσ := by
  rw [mem_kernel]
  simp [unipotentPlane, unipotentSU, unipotentMatrix]

/-- The restriction kernel embedded in the ambient special unitary group. -/
def ambientRadical : Subgroup (SU F (form F σ hσ)) :=
  (kernel F σ hσ).map (planeParabolicSU F (form F σ hσ)).subtype

/-- The original literal Hermitian unipotents belong to the ambient radical. -/
theorem unipotentSU_mem_ambientRadical (X : hermitianMatrices F σ) :
    unipotentSU F σ hσ X ∈ ambientRadical F σ hσ :=
  ⟨unipotentPlane F σ hσ X, unipotentPlane_mem_kernel F σ hσ X, rfl⟩

private def hermitianIdentity : hermitianMatrices F σ :=
  ⟨1, by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Representation.OrthogonalFourMinus.adjoint]⟩

/-- The identity Hermitian parameter supplies a nonidentity radical element. -/
theorem ambientRadical_ne_bot : ambientRadical F σ hσ ≠ ⊥ := by
  intro h
  have hm := unipotentSU_mem_ambientRadical F σ hσ (hermitianIdentity F σ)
  rw [h, Subgroup.mem_bot] at hm
  have he := congrArg (fun g : SU F (form F σ hσ) => g.val.val 0 3) hm
  exact one_ne_zero he

/-- The embedded radical remains a two-group. -/
theorem ambientRadical_isTwoGroup : IsPGroup 2 (ambientRadical F σ hσ) :=
  (kernel_isTwoGroup F σ hσ).map _

/-- The common fixed space of the radical is precisely the coordinate plane. -/
theorem fixed_iff_plane (v : Fin 4 → F) :
    (∀ u ∈ ambientRadical F σ hσ, u.val.val.mulVec v = v) ↔ v ∈ planeSpace F := by
  constructor
  · intro h
    have he := h (unipotentSU F σ hσ (hermitianIdentity F σ))
      (unipotentSU_mem_ambientRadical F σ hσ _)
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    simp only [unipotentSU, unipotentMatrix, hermitianIdentity,
      GeneralLinearGroup.val_mkOfDetNeZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h0 h1
    change v 2 = 0 ∧ v 3 = 0
    constructor
    · simpa using h1
    · simpa using h0
  · intro hv u hu
    obtain ⟨g,hg,rfl⟩ := hu
    obtain ⟨v2,v3⟩ := hv
    have hv : v = ![v 0,v 1,0,0] := by
      ext i; fin_cases i <;> simp [v2,v3]
    conv_lhs => rw [hv]
    change g.val.val.val.mulVec ![v 0,v 1,0,0] = v
    rw [show ![v 0,v 1,0,0] = ![(![v 0,v 1] : Fin 2 → F) 0,
      (![v 0,v 1] : Fin 2 → F) 1,0,0] from rfl,
      restriction_mulVec]
    have hg' : restriction F (form F σ hσ) g = 1 := hg
    rw [hg']
    simpa using hv.symm

/-- The full plane stabilizer is exactly the ambient normalizer of the radical. -/
theorem normalizer_ambientRadical :
    Subgroup.normalizer (ambientRadical F σ hσ : Set (SU F (form F σ hσ))) =
      planeParabolicSU F (form F σ hσ) := by
  apply le_antisymm
  · intro g hg
    change g.val ∈ MulAction.stabilizer (GL (Fin 4) F) (planeSpace F : Set (Fin 4 → F))
    rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
    intro v hv
    apply (fixed_iff_plane F σ hσ _).mp
    intro u hu
    have hc := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem hg) u).mp hu
    have he := (fixed_iff_plane F σ hσ v).mpr hv _ hc
    have hh := congrArg (fun w : Fin 4 → F => g.val.val.mulVec w) he
    change g.val.val.mulVec ((g⁻¹ * u * g).val.val.mulVec v) = g.val.val.mulVec v at hh
    change u.val.val.mulVec (g.val.val.mulVec v) = g.val.val.mulVec v
    simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv,
      Matrix.mulVec_mulVec, ← mul_assoc, Units.mul_inv, one_mul] using hh
  · have hn := (kernel F σ hσ).le_normalizer_map
      (planeParabolicSU F (form F σ hσ)).subtype
    simpa only [ambientRadical, Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] using hn

/-- The full plane parabolic is two-local in the ambient SU₄. -/
theorem isTwoLocal : IsTwoLocal (planeParabolicSU F (form F σ hσ)) :=
  ⟨ambientRadical F σ hσ, ambientRadical_ne_bot F σ hσ,
    ambientRadical_isTwoGroup F σ hσ, (normalizer_ambientRadical F σ hσ).symm⟩

private def diagonalFirst : hermitianMatrices F σ :=
  ⟨!![1,0;0,0], by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Representation.OrthogonalFourMinus.adjoint]⟩

private def diagonalSecond : hermitianMatrices F σ :=
  ⟨!![0,0;0,1], by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Representation.OrthogonalFourMinus.adjoint]⟩

private def offDiagonal : hermitianMatrices F σ :=
  ⟨!![0,1;1,0], by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Representation.OrthogonalFourMinus.adjoint]⟩

/-- The Hermitian restriction kernel is self-centralizing inside the full
parabolic, as seen by commuting with three explicit Hermitian unipotents. -/
theorem centralizer_kernel_le :
    Subgroup.centralizer (kernel F σ hσ : Set (planeParabolicSU F (form F σ hσ))) ≤
      kernel F σ hσ := by
  intro g hg
  have he (X : hermitianMatrices F σ) :
      unipotentMatrix F X.val * g.val.val.val = g.val.val.val * unipotentMatrix F X.val := by
    exact congrArg (fun a : planeParabolicSU F (form F σ hσ) => a.val.val.val)
      ((Subgroup.mem_centralizer_iff.mp hg) (unipotentPlane F σ hσ X)
        (unipotentPlane_mem_kernel F σ hσ X))
  have h10 := congrArg (fun M => M 1 3) (he (diagonalFirst F σ))
  have h32 := congrArg (fun M => M 0 2) (he (diagonalFirst F σ))
  have h33 := congrArg (fun M => M 0 3) (he (diagonalFirst F σ))
  have h01 := congrArg (fun M => M 0 2) (he (diagonalSecond F σ))
  have h22 := congrArg (fun M => M 1 2) (he (diagonalSecond F σ))
  have h00 := congrArg (fun M => M 0 2) (he (offDiagonal F σ))
  simp [diagonalFirst, diagonalSecond, offDiagonal, unipotentMatrix,
    Matrix.mul_apply, Fin.sum_univ_succ, add_comm] at h10 h32 h33 h01 h22 h00
  have h33 : g.val.val.val 3 3 = g.val.val.val 0 0 :=
    add_left_cancel (h33.trans (add_comm _ _))
  have h22 : g.val.val.val 2 2 = g.val.val.val 1 1 :=
    add_right_cancel (h22.trans (add_comm _ _))
  have h00 : g.val.val.val 2 2 = g.val.val.val 0 0 :=
    add_right_cancel (h00.trans (add_comm _ _))
  obtain ⟨h20,h30,h21,h31⟩ := (mem_planeParabolicSU F _ g.val).mp g.property
  have hd : g.val.val.val.det = 1 := congrArg Units.val g.val.property.2
  rw [Matrix.det_of_isUpperTriangular] at hd
  · have hp : g.val.val.val 0 0 ^ 4 = 1 := by
      simpa [Fin.prod_univ_succ, h33, ← h22, h00, pow_succ, mul_assoc] using hd
    have ha : g.val.val.val 0 0 = 1 := (iterateFrobeniusEquiv F 2 2).injective (by
      change g.val.val.val 0 0 ^ (2 ^ 2) = (1 : F) ^ (2 ^ 2)
      simpa using hp)
    apply (mem_kernel F σ hσ g).mpr
    exact ⟨ha,h01,h10, by rw [← h22, h00, ha]⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Relative normality and the two-group property put the kernel in `O₂(P)`. -/
theorem kernel_le_twoCore : kernel F σ hσ ≤
    pCore 2 (planeParabolicSU F (form F σ hσ)) :=
  le_sSup ⟨inferInstance, kernel_isTwoGroup F σ hσ⟩

/-- The intrinsic two-core of the full plane parabolic contains its centralizer. -/
theorem centralizer_twoCore_le :
    Subgroup.centralizer (pCore 2 (planeParabolicSU F (form F σ hσ)) :
      Set (planeParabolicSU F (form F σ hσ))) ≤
        pCore 2 (planeParabolicSU F (form F σ hσ)) :=
  (Subgroup.centralizer_le (kernel_le_twoCore F σ hσ)).trans
    ((centralizer_kernel_le F σ hσ).trans (kernel_le_twoCore F σ hσ))

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PlaneParabolic
