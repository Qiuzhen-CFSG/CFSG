module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortAction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.HermitianAction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortCentralizer

/-!
# The orthogonal three-space at the marked U₅ short root

The trace-one basis changes the off-diagonal Hermitian block to the existing
identity-block short involution. Central Hermitian parameters embed faithfully
in the nonabelian plane radical, and the adapted Levi projection gives their
literal conjugation action. The marked long root normally generates a
three-dimensional fixed-field symmetric space. Its fixed subgroup under the
prime-to-two residual is exactly the full one-dimensional short-root line.
After killing that entire line, one perfect fixed-field SL₂ image is transitive
on the nonzero vectors.

The Hermitian-coordinate calculations reuse the unitary-four results; all
embeddings and actions here are in the unitary-five plane semidirect product.
Source: Aschbacher–Smith F.4.42, printed pp.295–296 of refs/quasithin.pdf.
The ambient line-normalizer and maximal-subgroup quotient arguments are not
conclusions of this local calculation.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPlaneRadical UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.UnitaryFive.ShortSpace
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)
local notation "σ" => J.conj
local notation "hσ" => J.conj_involutive
local notation "K" => FixedBy.subfield F σ
local notation "P" => PlaneCore.PlaneSemidirect J
local notation "H" => hermitianMatrices F σ

/-- Hermitian matrices embed in the center of the nonabelian plane radical. -/
def parameter : Multiplicative H →* PlaneCore.Parameters J where
  toFun X := ⟨0,X.toAdd.val,by
    intro i j
    have h := congrFun (congrFun X.toAdd.property i) j
    change σ (X.toAdd.val j i) = X.toAdd.val i j at h
    simp only [Pi.zero_apply,zero_mul,h]
    exact CharTwo.add_self_eq_zero _⟩
  map_one' := rfl
  map_mul' X Y := by
    apply PlaneCore.Parameters.ext
    · simp
    · ext i j
      simp

theorem parameter_injective : Function.Injective (parameter J) := by
  intro X Y he
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg PlaneCore.Parameters.z he

theorem parameter_central (X : Multiplicative H) : parameter J X ∈ center (PlaneCore.Parameters J) :=
  PlaneCore.Parameters.mem_center_of_x_eq_zero J _ rfl

theorem parameter_action (A : SpecialLinearGroup (Fin 2) F) (X : Multiplicative H) :
    PlaneCore.Parameters.planeAction A (parameter J X) =
      parameter J (Multiplicative.ofAdd (hermitianCongruence F σ hσ A X.toAdd)) := by
  apply PlaneCore.Parameters.ext
  · simp [parameter]
  · rfl

variable (c : F) (hc : c + J.conj c = 1)

/-- This basis takes the off-diagonal short parameter to the existing identity mark. -/
def basis (c : F) (hc : c + J.conj c = 1) : SpecialLinearGroup (Fin 2) F :=
  ⟨(!![1,c;1,J.conj c] : Matrix (Fin 2) (Fin 2) F),by
    rw [Matrix.det_fin_two]
    change 1 * J.conj c - c * 1 = 1
    simpa only [one_mul,mul_one,CharTwo.sub_eq_add,add_comm] using hc⟩

def adaptedParameter : Multiplicative H →* PlaneCore.Parameters J :=
  (PlaneCore.Parameters.planeAction (basis J c hc)).toMonoidHom.comp (parameter J)

theorem adaptedParameter_injective : Function.Injective (adaptedParameter J c hc) :=
  (PlaneCore.Parameters.planeAction (basis J c hc)).injective.comp (parameter_injective J)

theorem adaptedParameter_central (X : Multiplicative H) :
    adaptedParameter J c hc X ∈ center (PlaneCore.Parameters J) :=
  MulEquivClass.apply_mem_center (PlaneCore.Parameters.planeAction (basis J c hc))
    (parameter_central J X)

theorem adapted_short :
    adaptedParameter J c hc (Multiplicative.ofAdd (UnitaryFourShortRoot.shortParameter F σ)) =
      InvolutionGeometry.shortParameter J := by
  apply PlaneCore.Parameters.ext
  · simp [adaptedParameter,parameter,InvolutionGeometry.shortParameter]
  · change (basis J c hc).val * (UnitaryFourShortRoot.shortParameter F σ).val *
      PlaneCore.planeAdjoint J (basis J c hc).val = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [basis,PlaneCore.planeAdjoint,
        UnitaryFourShortRoot.shortParameter,
        Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
    · exact hc
    · simpa only [add_comm] using hc

/-- The literal marked centralizer in the geometric plane residual. -/
def centralizer : Subgroup P :=
  Subgroup.centralizer ({SemidirectProduct.inl (InvolutionGeometry.shortParameter J)} : Set P)

/-- Center coordinates in the original semidirect product. -/
def radical : Multiplicative H →* P :=
  SemidirectProduct.inl.comp (adaptedParameter J c hc)

theorem radical_injective : Function.Injective (radical J c hc) :=
  SemidirectProduct.inl_injective.comp (adaptedParameter_injective J c hc)

/-- The actual Levi projection, in the basis of the marked short involution. -/
def projection : P →* SpecialLinearGroup (Fin 2) F :=
  (MulAut.conj (basis J c hc)⁻¹).toMonoidHom.comp SemidirectProduct.rightHom

private theorem adapted_action (A : SpecialLinearGroup (Fin 2) F) (X : Multiplicative H) :
    PlaneCore.Parameters.planeAction A (adaptedParameter J c hc X) =
      adaptedParameter J c hc (Multiplicative.ofAdd (hermitianCongruence F σ hσ
        ((basis J c hc)⁻¹ * A * basis J c hc) X.toAdd)) := by
  simp only [adaptedParameter,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
  rw [←parameter_action]
  change PlaneCore.Parameters.planeAction A (PlaneCore.Parameters.planeAction (basis J c hc) _) =
    PlaneCore.Parameters.planeAction (basis J c hc)
      (PlaneCore.Parameters.planeAction ((basis J c hc)⁻¹ * A * basis J c hc) _)
  simp only [map_mul,MulAut.mul_apply,map_inv]
  simp

theorem radical_conjugation (p : P) (X : Multiplicative H) :
    p * radical J c hc X * p⁻¹ = radical J c hc (Multiplicative.ofAdd
      (hermitianCongruence F σ hσ (projection J c hc p) X.toAdd)) := by
  have hh := PlaneCore.inl_center_conjugation J p
    ⟨adaptedParameter J c hc X,adaptedParameter_central J c hc X⟩
  change SemidirectProduct.inl (PlaneCore.Parameters.planeAction p.right (adaptedParameter J c hc X)) =
    p * SemidirectProduct.inl (adaptedParameter J c hc X) * p⁻¹ at hh
  apply hh.symm.trans
  apply congrArg SemidirectProduct.inl
  simpa only [projection,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply,inv_inv,SemidirectProduct.rightHom_eq_right] using adapted_action J c hc p.right X

theorem mem_centralizer (p : P) : p ∈ centralizer J ↔ projection J c hc p ∈ fixedSL F σ := by
  rw [centralizer,mem_centralizer_singleton_iff,←mul_inv_eq_iff_eq_mul,
    ←adapted_short J c hc]
  change p * radical J c hc _ * p⁻¹ = radical J c hc _ ↔ _
  rw [radical_conjugation,(radical_injective J c hc).eq_iff,
    Multiplicative.ofAdd.injective.eq_iff,mem_fixedSL,←short_fixed_iff F σ hσ]
  rfl

/-- All central plane parameters lie in the chosen centralizer. -/
def intoCentralizer : Multiplicative H →* centralizer J :=
  (radical J c hc).codRestrict _ (by
    intro X
    rw [mem_centralizer J c hc]
    simp [projection,radical])

theorem intoCentralizer_injective : Function.Injective (intoCentralizer J c hc) := by
  intro X Y h
  exact radical_injective J c hc (congrArg Subtype.val h)

/-- The orthogonal three-space, in the actual short centralizer. -/
def space : Subgroup (centralizer J) :=
  (fixedHermitian F σ).toSubgroup.map (intoCentralizer J c hc)

/-- The full short-root line, with all parameters from the fixed field. -/
def lineHom : Multiplicative K →* centralizer J :=
  (intoCentralizer J c hc).comp (SourceNormalizer.FourShortRoot.lineParameter F σ).toMultiplicative

def line : Subgroup (centralizer J) := (lineHom J c hc).range

theorem line_le_space : line J c hc ≤ space J c hc := by
  rintro _ ⟨b,rfl⟩
  refine ⟨(SourceNormalizer.FourShortRoot.lineParameter F σ).toMultiplicative b,?_,rfl⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [SourceNormalizer.FourShortRoot.lineParameter,SourceNormalizer.FourShortRoot.symmetric,
      fixedHermitianEquiv]
  all_goals exact b.toAdd.property

theorem space_card : Nat.card (space J c hc) = Nat.card K ^ 3 :=
  (Subgroup.card_map_of_injective (intoCentralizer_injective J c hc)).trans
    (fixedHermitian_card F σ)

theorem lineHom_injective : Function.Injective (lineHom J c hc) := by
  intro a b he
  have hh := intoCentralizer_injective J c hc he
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg (fun X : Multiplicative H => X.toAdd.val 0 1) hh

theorem line_card : Nat.card (line J c hc) = Nat.card K := by
  rw [line,←Nat.card_congr (MonoidHom.ofInjective (lineHom_injective J c hc)).toEquiv]
  exact Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)

private theorem lineParameter_fixed (A : fixedSL F σ) (b : K) :
    hermitianCongruence F σ hσ A.val (SourceNormalizer.FourShortRoot.lineParameter F σ b) =
      SourceNormalizer.FourShortRoot.lineParameter F σ b := by
  apply (SourceNormalizer.FourShortRoot.fixed_iff_line F σ hσ _ ?_).mpr ⟨b,rfl⟩ A A.property
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [SourceNormalizer.FourShortRoot.lineParameter,SourceNormalizer.FourShortRoot.symmetric,
      fixedHermitianEquiv]
  all_goals exact b.property

theorem line_le_center : line J c hc ≤ center (centralizer J) := by
  rintro x ⟨b,rfl⟩
  apply mem_center_iff.mpr
  intro a
  apply Subtype.ext
  apply mul_inv_eq_iff_eq_mul.mp
  change a.val * radical J c hc _ * a.val⁻¹ = radical J c hc _
  rw [radical_conjugation]
  apply congrArg (radical J c hc)
  apply congrArg Multiplicative.ofAdd
  exact lineParameter_fixed J ⟨projection J c hc a.val,
    (mem_centralizer J c hc a.val).mp a.property⟩ b.toAdd

theorem space_normal : (space J c hc).Normal := by
  constructor
  rintro x ⟨X,hX,he⟩ a
  refine ⟨Multiplicative.ofAdd (hermitianCongruence F σ hσ
    (projection J c hc a.val) X.toAdd),
    fixedHermitian_congruence F σ hσ _ ((mem_centralizer J c hc a.val).mp a.property) _ hX,?_⟩
  apply Subtype.ext
  change radical J c hc _ = a.val * x.val * a.val⁻¹
  rw [←he]
  exact (radical_conjugation J c hc a.val X).symm

/-- Fixed-field Levi matrices in the original short centralizer. -/
def levi : fixedSL F σ →* centralizer J :=
  (SemidirectProduct.inr.comp ((MulAut.conj (basis J c hc)).toMonoidHom.comp
    (fixedSL F σ).subtype)).codRestrict _ (by
      intro A
      rw [mem_centralizer J c hc]
      simp [projection,MulAut.conj_apply,mul_assoc,A.property])

theorem projection_levi (A : fixedSL F σ) : projection J c hc (levi J c hc A).val = A.val := by
  simp [projection,levi,MulAut.conj_apply,mul_assoc]

/-- Conjugation on all coordinates uses the literal fixed-field Levi. -/
theorem levi_conjugation (A : fixedSL F σ) (X : Multiplicative H) :
    levi J c hc A * intoCentralizer J c hc X * (levi J c hc A)⁻¹ =
      intoCentralizer J c hc (Multiplicative.ofAdd
        (hermitianCongruence F σ hσ A.val X.toAdd)) := by
  apply Subtype.ext
  exact (radical_conjugation J c hc (levi J c hc A).val X).trans
    (congrArg (fun B => radical J c hc (Multiplicative.ofAdd
      (hermitianCongruence F σ hσ B X.toAdd))) (projection_levi J c hc A))

/-- Every fixed-field Levi element lies in the actual prime-to-two residual. -/
theorem levi_mem_primeTo (A : fixedSL F σ) :
    levi J c hc A ∈ primeToResidual 2 (centralizer J) := by
  let f := (levi J c hc).comp (fixedSLEquiv F σ).symm.toMonoidHom
  have he : f ((fixedSLEquiv F σ) A) = levi J c hc A := by
    simp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply]
  rw [←he]
  exact Matrix.SL2.map_mem_primeToResidual 2 f _

/-- The whole fixed subgroup is the entire short-root line. -/
theorem fixed_primeTo :
    space J c hc ⊓ Subgroup.centralizer (primeToResidual 2 (centralizer J) : Set (centralizer J)) =
      line J c hc := by
  apply le_antisymm
  · rintro x ⟨⟨X,hX,rfl⟩,hx⟩
    have hfixed : ∀ A ∈ fixedSL F σ, hermitianCongruence F σ hσ A X.toAdd = X.toAdd := by
      intro A hA
      have hh := hx (levi J c hc ⟨A,hA⟩) (levi_mem_primeTo J c hc ⟨A,hA⟩)
      have he : levi J c hc ⟨A,hA⟩ * intoCentralizer J c hc X * (levi J c hc ⟨A,hA⟩)⁻¹ =
          intoCentralizer J c hc X := by rw [hh,mul_inv_cancel_right]
      rw [levi_conjugation] at he
      exact congrArg Multiplicative.toAdd (intoCentralizer_injective J c hc he)
    obtain ⟨b,hb⟩ := (SourceNormalizer.FourShortRoot.fixed_iff_line F σ hσ X.toAdd hX).mp hfixed
    exact ⟨Multiplicative.ofAdd b,congrArg (intoCentralizer J c hc) (congrArg Multiplicative.ofAdd hb.symm)⟩
  · intro x hx
    exact ⟨line_le_space J c hc hx,center_le_centralizer _ (line_le_center J c hc hx)⟩

/-- The existing identity-block short mark belongs to this full line. -/
def shortMark : centralizer J :=
  ⟨SemidirectProduct.inl (InvolutionGeometry.shortParameter J),mem_centralizer_singleton_iff.mpr rfl⟩

theorem shortMark_mem_line : shortMark J ∈ line J c hc := by
  refine ⟨Multiplicative.ofAdd (1 : K),?_⟩
  apply Subtype.ext
  exact congrArg SemidirectProduct.inl (adapted_short J c hc)

/-- The marked long root in the same coordinate plane. -/
def longMark : centralizer J :=
  intoCentralizer J c hc (Multiplicative.ofAdd (longParameter F σ))

theorem space_elementary : IsElementaryAbelian 2 (space J c hc) := by
  have hi : IsElementaryAbelian 2 (Multiplicative H) := by
    refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
    intro X
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change X.toAdd.val + X.toAdd.val = 0
    ext i j
    exact CharTwo.add_self_eq_zero _
  let := hi
  let : IsElementaryAbelian 2 ((fixedHermitian F σ).toSubgroup) :=
    IsElementaryAbelian.of_injective _ ((fixedHermitian F σ).toSubgroup).subtype_injective
  exact IsElementaryAbelian.map _

variable [Finite F]

private theorem normal_contains_diagonal (N : Subgroup (centralizer J)) [N.Normal]
    (hz : longMark J c hc ∈ N) (a : K) :
    intoCentralizer J c hc (Multiplicative.ofAdd (SourceNormalizer.FourShortRoot.symmetric F σ a 0 0)) ∈ N := by
  by_cases ha : a = 0
  · have he : SourceNormalizer.FourShortRoot.symmetric F σ a 0 0 = 0 := by
      subst a
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    simpa only [he, ofAdd_zero, map_one] using N.one_mem
  obtain ⟨r,hr⟩ := (frobeniusEquiv K 2).surjective a
  have hr2 : r^2 = a := hr
  have hr0 : r ≠ 0 := by intro he; apply ha; rw [←hr2,he,zero_pow (by decide)]
  have hrf : σ (r:F) = r := r.property
  have hrF : (r:F) ≠ 0 := fun he => hr0 (Subtype.ext he)
  let A : SpecialLinearGroup (Fin 2) F :=
    ⟨!![(r:F),0;0,(r:F)⁻¹],by simp [det_fin_two,hrF]⟩
  have hA : A ∈ fixedSL F σ := by
    rw [mem_fixedSL]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [A,hrf]
  have he : hermitianCongruence F σ hσ A (longParameter F σ) = SourceNormalizer.FourShortRoot.symmetric F σ a 0 0 := by
    apply Subtype.ext
    have hh := congrArg Subtype.val hr2
    change (r:F)^2 = (a:F) at hh
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianCongruence,A,longParameter,SourceNormalizer.FourShortRoot.symmetric,fixedHermitianEquiv,
        adjoint,Fin.sum_univ_two,Matrix.vecMul,dotProduct,hrf,←pow_two,hh]
  have hn := (show N.Normal from inferInstance).conj_mem (longMark J c hc) hz (levi J c hc ⟨A,hA⟩)
  change levi J c hc ⟨A,hA⟩ * intoCentralizer J c hc
    (Multiplicative.ofAdd (longParameter F σ)) * (levi J c hc ⟨A,hA⟩)⁻¹ ∈ N at hn
  rw [levi_conjugation] at hn
  simpa only [toAdd_ofAdd,he] using hn

/-- The long root normally generates the entire orthogonal three-space
inside the literal short-root centralizer. -/
theorem long_normalClosure :
    normalClosure ({longMark J c hc} : Set (centralizer J)) =
      space J c hc := by
  let := space_normal J c hc
  let N := normalClosure ({longMark J c hc} : Set (centralizer J))
  have hz : longMark J c hc ∈ N := subset_normalClosure (Set.mem_singleton _)
  apply le_antisymm
  · apply normalClosure_le_normal
    rintro x rfl
    refine ⟨Multiplicative.ofAdd (longParameter F σ),?_,rfl⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [longParameter]
  · rintro x ⟨X,hX,he⟩
    have hx : intoCentralizer J c hc X = x := he
    rw [←hx]
    let p := fixedHermitianEquiv F σ ⟨X.toAdd,hX⟩
    have hcoord : X.toAdd = SourceNormalizer.FourShortRoot.symmetric F σ p.1 p.2.1 p.2.2 :=
      (congrArg Subtype.val ((fixedHermitianEquiv F σ).symm_apply_apply ⟨X.toAdd,hX⟩)).symm
    have hd := normal_contains_diagonal J c hc N hz
    have hs (a : K) : intoCentralizer J c hc
        (Multiplicative.ofAdd (SourceNormalizer.FourShortRoot.symmetric F σ 0 0 a)) ∈ N := by
      have hn := (show N.Normal from inferInstance).conj_mem _ (hd a) (levi J c hc ⟨cubic F,cubic_mem_fixedSL F σ⟩)
      rw [levi_conjugation] at hn
      have he : hermitianCongruence F σ hσ (cubic F) (SourceNormalizer.FourShortRoot.symmetric F σ a 0 0) = SourceNormalizer.FourShortRoot.symmetric F σ 0 0 a := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hermitianCongruence,cubic,SourceNormalizer.FourShortRoot.symmetric,fixedHermitianEquiv,
            adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
      simpa only [toAdd_ofAdd,he] using hn
    have ho (b : K) : intoCentralizer J c hc
        (Multiplicative.ofAdd (SourceNormalizer.FourShortRoot.symmetric F σ 0 b 0)) ∈ N := by
      have hn := (show N.Normal from inferInstance).conj_mem _ (hs b) (levi J c hc ⟨cubic F,cubic_mem_fixedSL F σ⟩)
      rw [levi_conjugation] at hn
      have he : hermitianCongruence F σ hσ (cubic F) (SourceNormalizer.FourShortRoot.symmetric F σ 0 0 b) = SourceNormalizer.FourShortRoot.symmetric F σ b b b := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hermitianCongruence,cubic,SourceNormalizer.FourShortRoot.symmetric,fixedHermitianEquiv,
            adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
      have hn' : intoCentralizer J c hc (Multiplicative.ofAdd (SourceNormalizer.FourShortRoot.symmetric F σ b b b)) ∈ N := by
        simpa only [toAdd_ofAdd,he] using hn
      have hsum : SourceNormalizer.FourShortRoot.symmetric F σ b b b + SourceNormalizer.FourShortRoot.symmetric F σ b 0 0 + SourceNormalizer.FourShortRoot.symmetric F σ 0 0 b = SourceNormalizer.FourShortRoot.symmetric F σ 0 b 0 := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [SourceNormalizer.FourShortRoot.symmetric,fixedHermitianEquiv,CharTwo.add_self_eq_zero]
      have hh := N.mul_mem (N.mul_mem hn' (hd b)) (hs b)
      rw [←map_mul,←map_mul] at hh
      change intoCentralizer J c hc (Multiplicative.ofAdd
        (SourceNormalizer.FourShortRoot.symmetric F σ b b b + SourceNormalizer.FourShortRoot.symmetric F σ b 0 0 + SourceNormalizer.FourShortRoot.symmetric F σ 0 0 b)) ∈ N at hh
      rwa [hsum] at hh
    have hsum : SourceNormalizer.FourShortRoot.symmetric F σ p.1 0 0 + SourceNormalizer.FourShortRoot.symmetric F σ 0 p.2.1 0 + SourceNormalizer.FourShortRoot.symmetric F σ 0 0 p.2.2 = X.toAdd := by
      rw [hcoord]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [SourceNormalizer.FourShortRoot.symmetric,fixedHermitianEquiv]
    have hh := N.mul_mem (N.mul_mem (hd p.1) (ho p.2.1)) (hs p.2.2)
    rw [←map_mul,←map_mul] at hh
    change intoCentralizer J c hc (Multiplicative.ofAdd
      (SourceNormalizer.FourShortRoot.symmetric F σ p.1 0 0 + SourceNormalizer.FourShortRoot.symmetric F σ 0 p.2.1 0 + SourceNormalizer.FourShortRoot.symmetric F σ 0 0 p.2.2)) ∈ N at hh
    simpa only [hsum,ofAdd_toAdd] using hh


/-- After killing the full line, every nonzero orthogonal vector lies in
one orbit of the literal fixed-field Levi subgroup. -/
theorem quotient_orbit {B : Type*} [Group B] (f : centralizer J →* B)
    (hline : line J c hc ≤ f.ker) {v : B}
    (hv : v ∈ (space J c hc).map f) (hv1 : v ≠ 1) :
    ∃ A : fixedSL F σ, f (levi J c hc A) * f (longMark J c hc) *
      (f (levi J c hc A))⁻¹ = v := by
  rw [space,Subgroup.map_map] at hv
  obtain ⟨X,hX,rfl⟩ := hv
  obtain ⟨b,hb⟩ | ⟨A,b,hb⟩ := SourceNormalizer.FourShortRoot.orthogonal_cases F σ hσ X.toAdd hX
  · exfalso
    apply hv1
    change f (intoCentralizer J c hc X) = 1
    apply hline
    exact ⟨Multiplicative.ofAdd b,congrArg (intoCentralizer J c hc) (congrArg Multiplicative.ofAdd hb.symm)⟩
  · refine ⟨A,?_⟩
    rw [←map_inv,←map_mul,←map_mul,show longMark J c hc = intoCentralizer J c hc
      (Multiplicative.ofAdd (longParameter F σ)) from rfl,levi_conjugation]
    have hkill : f (lineHom J c hc (Multiplicative.ofAdd b)) = 1 := hline ⟨Multiplicative.ofAdd b,rfl⟩
    have he : X = Multiplicative.ofAdd (hermitianCongruence F σ hσ A.val (longParameter F σ)) *
      (SourceNormalizer.FourShortRoot.lineParameter F σ).toMultiplicative (Multiplicative.ofAdd b) :=
      congrArg Multiplicative.ofAdd hb
    change _ = f (intoCentralizer J c hc X)
    rw [he,map_mul,map_mul,show f (intoCentralizer J c hc
      ((SourceNormalizer.FourShortRoot.lineParameter F σ).toMultiplicative (Multiplicative.ofAdd b))) = 1 from hkill,mul_one]
    rfl

/-- The quotient orbit is induced by a single perfect subgroup. -/
theorem quotient_perfect_orbit (hK : 3 < Nat.card K)
    {B : Type*} [Group B] (f : centralizer J →* B)
    (hline : line J c hc ≤ f.ker) :
    ∃ D : Subgroup B, Group.IsPerfect D ∧ D ≤ f.range ∧
      ∀ v ∈ (space J c hc).map f, v ≠ 1 →
        ∃ a ∈ D, a * f (longMark J c hc) * a⁻¹ = v := by
  let k := (f.comp (levi J c hc)).comp (fixedSLEquiv F σ).symm.toMonoidHom
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three _ hK
  refine ⟨k.range,Group.IsPerfect.range k,?_,?_⟩
  · rintro _ ⟨a,rfl⟩
    exact ⟨levi J c hc ((fixedSLEquiv F σ).symm a),rfl⟩
  · intro v hv hv1
    obtain ⟨A,he⟩ := quotient_orbit J c hc f hline hv hv1
    refine ⟨f (levi J c hc A),⟨(fixedSLEquiv F σ) A,?_⟩,he⟩
    simp only [k,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply]

end Theory.SpecificGroups.UnitaryFive.ShortSpace
