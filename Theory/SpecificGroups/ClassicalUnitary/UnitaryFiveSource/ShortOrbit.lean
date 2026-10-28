module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortNormalizer
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# The local long-root orbit inside the U₅ short-root centralizer

Nonzero pairs over the fixed field parametrize the compatible long-root
class. Its order q²−1 is odd, so a Sylow subgroup of the whole residual
short-root centralizer centralizes that same long root. The literal Levi
commutator action also puts the entire orthogonal three-space in the
perfect solvable residual when q>3. These are the Sylow and perfect-group
inputs for the second F.4.42 quotient.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of refs/quasithin.pdf;
the fixed-field pair calculation follows SourceNormalizer.FourShortOrbit,
with the actual U₅ nonabelian plane radical retained.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPlaneRadical UnitaryFourShortRoot
open scoped commutatorElement
namespace Theory.SpecificGroups.UnitaryFive.ShortSpace
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1)
local notation "σ" => J.conj
local notation "hσ" => J.conj_involutive
local notation "K" => FixedBy.subfield F σ
local notation "C" => centralizer J

private instance parameters_finite : Finite (PlaneCore.Parameters J) :=
  Finite.of_injective (fun x : PlaneCore.Parameters J => (x.x,x.z))
    (fun _ _ h => PlaneCore.Parameters.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
private instance semidirect_finite : Finite (PlaneCore.PlaneSemidirect J) :=
  Finite.of_injective (fun x : PlaneCore.PlaneSemidirect J => (x.left,x.right))
    (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

omit [Finite F] in
/-- The literal centralizer acts on central parameters through its fixed Levi. -/
theorem conjugation (a : C) (X : Multiplicative (hermitianMatrices F σ)) :
    a * intoCentralizer J c hc X * a⁻¹ = intoCentralizer J c hc
      (Multiplicative.ofAdd (hermitianCongruence F σ hσ (projection J c hc a.val) X.toAdd)) :=
  Subtype.ext (radical_conjugation J c hc a.val X)

private def rootPair (v : K × K) : C :=
  intoCentralizer J c hc (Multiplicative.ofAdd
    (SourceNormalizer.FourShortRoot.symmetric F σ (v.1^2) (v.1*v.2) (v.2^2)))

private theorem rootPair_injective : Function.Injective (rootPair J c hc) := by
  intro v w he
  have hh : SourceNormalizer.FourShortRoot.symmetric F σ (v.1^2) (v.1*v.2) (v.2^2) =
      SourceNormalizer.FourShortRoot.symmetric F σ (w.1^2) (w.1*w.2) (w.2^2) := by
    apply Multiplicative.ofAdd.injective
    exact intoCentralizer_injective J c hc he
  apply Prod.ext
  · apply (frobeniusEquiv K 2).injective
    apply Subtype.ext
    exact congrArg (fun X : hermitianMatrices F σ => X.val 0 0) hh
  · apply (frobeniusEquiv K 2).injective
    apply Subtype.ext
    exact congrArg (fun X : hermitianMatrices F σ => X.val 1 1) hh

omit [Finite F] in
private theorem conjugate_long (a : C) :
    ∃ v : K × K, v ≠ 0 ∧ a * longMark J c hc * a⁻¹ = rootPair J c hc v := by
  let A := projection J c hc a.val
  have hA := (mem_fixedSL F σ A).mp ((mem_centralizer J c hc a.val).mp a.property)
  let v : K × K := (⟨A.val 0 0,hA 0 0⟩,⟨A.val 1 0,hA 1 0⟩)
  have hv : v ≠ 0 := by
    intro he
    have h0 : A.val 0 0 = 0 := congrArg (fun p : K × K => (p.1 : F)) he
    have h1 : A.val 1 0 = 0 := congrArg (fun p : K × K => (p.2 : F)) he
    have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
      simpa only [det_fin_two] using A.property
    simp only [h0,h1,zero_mul,mul_zero,sub_self] at hd
    exact zero_ne_one hd
  refine ⟨v,hv,?_⟩
  change a * intoCentralizer J c hc (Multiplicative.ofAdd (longParameter F σ)) * a⁻¹ = _
  rw [conjugation]
  apply congrArg (intoCentralizer J c hc)
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  change A.val * !![1,0;0,0] * adjoint σ A.val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SourceNormalizer.FourShortRoot.symmetric,fixedHermitianEquiv,v,adjoint,mul_apply,Fin.sum_univ_two,hA,pow_two,mul_comm]

omit [Finite F] in
private theorem rootPair_conjugate (v : K × K) (hv : v ≠ 0) :
    IsConj (longMark J c hc) (rootPair J c hc v) := by
  have hv' : (![v.1,v.2] : Fin 2 → K) ≠ 0 := by
    intro he
    exact hv (Prod.ext (congrFun he 0) (congrFun he 1))
  obtain ⟨B,hB⟩ := Matrix.SL2.exists_mulVec_eq K ![1,0] ![v.1,v.2]
    (by intro he; exact one_ne_zero (congrFun he 0)) hv'
  have hb0 : B.val 0 0 = v.1 := by
    simpa [mulVec,dotProduct,Fin.sum_univ_two] using congrFun hB 0
  have hb1 : B.val 1 0 = v.2 := by
    simpa [mulVec,dotProduct,Fin.sum_univ_two] using congrFun hB 1
  let A := SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B
  let a := levi J c hc ⟨A,⟨B,rfl⟩⟩
  refine isConj_iff.mpr ⟨a,?_⟩
  change a * intoCentralizer J c hc (Multiplicative.ofAdd (longParameter F σ)) * a⁻¹ = _
  rw [conjugation]
  rw [show projection J c hc a.val = A from projection_levi J c hc ⟨A,⟨B,rfl⟩⟩]
  apply congrArg (intoCentralizer J c hc)
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  have ha0 : A.val 0 0 = (v.1 : F) := congrArg Subtype.val hb0
  have ha1 : A.val 1 0 = (v.2 : F) := congrArg Subtype.val hb1
  have hσr : σ (v.1 : F) = v.1 := v.1.property
  have hσs : σ (v.2 : F) = v.2 := v.2.property
  change A.val * !![1,0;0,0] * adjoint σ A.val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SourceNormalizer.FourShortRoot.symmetric,fixedHermitianEquiv,adjoint,mul_apply,Fin.sum_univ_two,ha0,ha1,
      hσr,hσs,pow_two,mul_comm]

/-- Nonzero fixed-field pairs parametrize the long-root class in the actual
short-root centralizer, with no quotient or central scalar ambiguity. -/
private def longClassEquiv : {v : K × K // v ≠ 0} ≃ {x : C // IsConj (longMark J c hc) x} :=
  Equiv.ofBijective (fun v => ⟨rootPair J c hc v.val,rootPair_conjugate J c hc v.val v.property⟩) (by
    constructor
    · intro v w he
      exact Subtype.ext (rootPair_injective J c hc (congrArg Subtype.val he))
    · rintro ⟨x,hx⟩
      obtain ⟨a,rfl⟩ := isConj_iff.mp hx
      obtain ⟨v,hv,he⟩ := conjugate_long J c hc a
      exact ⟨⟨v,hv⟩,Subtype.ext he.symm⟩)

/-- The exact local long-root class size is q²−1. -/
theorem longClass_card :
    Nat.card {x : C // IsConj (longMark J c hc) x} = (Nat.card K)^2 - 1 := by
  rw [←Nat.card_congr (longClassEquiv J c hc)]
  let := Fintype.ofFinite (K × K)
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [←Nat.card_eq_fintype_card,Nat.card_prod,Nat.card_unique,pow_two]

/-- The long-root centralizer has the same exact odd index. -/
theorem long_centralizer_index :
    (Subgroup.centralizer ({longMark J c hc} : Set C)).index = (Nat.card K)^2 - 1 := by
  have he := ConjClasses.nat_card_carrier_mul_card_centralizer (longMark J c hc)
  change Nat.card {x : C // IsConj (longMark J c hc) x} * _ = _ at he
  rw [longClass_card J c hc] at he
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Subgroup.centralizer ({longMark J c hc} : Set C)))
  rw [mul_comm,Subgroup.card_mul_index]
  exact he.symm

/-- A Sylow of the genuine residual short-root centralizer centralizes the
same marked long root. This is local Sylow placement, not ambient transfer. -/
theorem exists_long_centralizing_sylow :
    ∃ P : Sylow 2 C, (P : Subgroup C) ≤ Subgroup.centralizer ({longMark J c hc} : Set C) := by
  let Z := Subgroup.centralizer ({longMark J c hc} : Set C)
  have hindex : ¬ 2 ∣ Z.index := by
    rw [long_centralizer_index J c hc]
    let := Fintype.ofFinite K
    obtain ⟨n,_,hn⟩ := FiniteField.card K 2
    have hn' : Nat.card K = 2^(n : ℕ) := by rwa [Nat.card_eq_fintype_card]
    have hpow : 2 ∣ (Nat.card K)^2 := dvd_pow (by rw [hn']; exact dvd_pow_self 2 n.ne_zero) (by decide)
    have hpos : 0 < (Nat.card K)^2 := pow_pos Nat.card_pos 2
    omega
  let P : Sylow 2 Z := default
  have hi : ¬ 2 ∣ ((P : Subgroup Z).map Z.subtype).index := by
    rw [index_map_of_injective _ Z.subtype_injective,range_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hindex
  exact ⟨(P.isPGroup'.map Z.subtype).toSylow hi,map_subtype_le _⟩



/-- The whole orthogonal three-space belongs to the perfect local residual. -/
theorem space_le_solvableResidual (hK : 3 < Nat.card K) :
    space J c hc ≤ solvableResidual C := by
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three _ hK
  let : Group.IsPerfect (fixedSL F σ) := Group.IsPerfect.ofSurjective
    (f := (fixedSLEquiv F σ).symm.toMonoidHom) (fixedSLEquiv F σ).symm.surjective
  let : Group.IsPerfect (levi J c hc).range := Group.IsPerfect.range _
  rw [←centralizer_commutator_eq_space J c hc (by omega)]
  apply commutator_le.mpr
  intro a _ b hb
  obtain ⟨X,rfl⟩ := hb
  let A : fixedSL F σ := ⟨projection J c hc a.val,(mem_centralizer J c hc a.val).mp a.property⟩
  have hlevi : levi J c hc A ∈ solvableResidual C :=
    le_solvableResidual_of_isPerfect (levi J c hc).range ⟨A,rfl⟩
  have he : ⁅a,intoCentralizer J c hc X⁆ = ⁅levi J c hc A,intoCentralizer J c hc X⁆ := by
    rw [commutatorElement_def,commutatorElement_def,conjugation,levi_conjugation]
  exact he ▸ (commutator_le_left (solvableResidual C) ⊤
    (commutator_mem_commutator hlevi (mem_top _)))

end Theory.SpecificGroups.UnitaryFive.ShortSpace
