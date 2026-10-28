module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.OrthogonalQuotient
public import Theory.SpecificGroups.SL2.PrimeToResidual

/-!
# The orthogonal three-space and its full short-root fixed line

In the literal unitary-four plane residual, the normal closure of the marked
long root in the short-root centralizer is the symmetric fixed-field
three-space. Fixed-field square roots and cubic Levi conjugation produce
its three coordinates. Its fixed subgroup under the actual prime-to-two
residual is exactly the q-element off-diagonal line: all fixed-field SL₂
matrices lie in that residual, and the line is central in the whole local
centralizer. For q>2 the line strictly contains the marked cyclic subgroup.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of
`refs/quasithin.pdf`. These are intrinsic local calculations. Applying I.8.5
still requires the ambient unique-fixed-coset and normalizer arguments.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "L" => localFactor F (form F σ hσ)
local notation "C" => shortCentralizer F σ hσ

/-- Fixed-field symmetric coordinates on the orthogonal three-space. -/
def symmetric (a b c : K) : hermitianMatrices F σ :=
  ((fixedHermitianEquiv F σ).symm (a,b,c)).val

omit [Finite F] [CharP F 2] in
private theorem symmetric_mem (a b c : K) :
    symmetric F σ a b c ∈ fixedHermitian F σ :=
  ((fixedHermitianEquiv F σ).symm (a,b,c)).property

/-- The entire fixed-field short-root line, including every field parameter. -/
def lineParameter : K →+ hermitianMatrices F σ where
  toFun b := symmetric F σ 0 b 0
  map_zero' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' b c := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [symmetric, fixedHermitianEquiv]

/-- Literal inclusion of the Hermitian radical in the plane residual. -/
def radicalHom : Multiplicative (hermitianMatrices F σ) →* L :=
  (radical F σ hσ).subtype.comp (radicalEquiv F σ hσ).toMonoidHom

theorem radicalHom_injective : Function.Injective (radicalHom F σ hσ) :=
  (radical F σ hσ).subtype_injective.comp (radicalEquiv F σ hσ).injective

/-- The short-root line as a subgroup of the original matrix residual. -/
def lineHom : Multiplicative K →* L :=
  (radicalHom F σ hσ).comp (lineParameter F σ).toMultiplicative

def shortLine : Subgroup L := (lineHom F σ hσ).range

theorem lineHom_injective : Function.Injective (lineHom F σ hσ) := by
  intro a b he
  have h := congrArg (fun X : Multiplicative (hermitianMatrices F σ) => X.toAdd.val 0 1)
    (radicalHom_injective F σ hσ he)
  exact Multiplicative.toAdd.injective (Subtype.ext h)

theorem shortLine_card : Nat.card (shortLine F σ hσ) = Nat.card K := by
  rw [shortLine, ←Nat.card_congr (MonoidHom.ofInjective (lineHom_injective F σ hσ)).toEquiv]
  exact Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)

omit [Finite F] in
private theorem line_fixed (A : SpecialLinearGroup (Fin 2) F) (hA : A ∈ fixedSL F σ) (b : K) :
    hermitianCongruence F σ hσ A (lineParameter F σ b) = lineParameter F σ b := by
  have ha := (mem_fixedSL F σ A).mp hA
  have hd : A.val 0 0 * A.val 1 1 + A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [det_fin_two, CharTwo.sub_eq_add] using A.property
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianCongruence, lineParameter, symmetric, fixedHermitianEquiv,
      adjoint, Matrix.mul_apply, Fin.sum_univ_two, ha]
  · ring_nf; simp [CharTwo.two_eq_zero]
  · linear_combination (b:F) * hd
  · linear_combination (b:F) * hd
  · ring_nf; simp [CharTwo.two_eq_zero]

omit [Finite F] in
/-- A symmetric Hermitian matrix is fixed by SL₂(K) exactly on the short-root line. -/
theorem fixed_iff_line (X : hermitianMatrices F σ) (hX : X ∈ fixedHermitian F σ) :
    (∀ A ∈ fixedSL F σ, hermitianCongruence F σ hσ A X = X) ↔
      ∃ b : K, X = lineParameter F σ b := by
  constructor
  · intro h
    have hc := h (cubic F) (cubic_mem_fixedSL F σ)
    have hx := (cubic_fixed_iff F σ hσ X).mp hc
    have hb : σ (X.val 0 1) = X.val 0 1 := hX 0 1
    refine ⟨⟨X.val 0 1,hb⟩,?_⟩
    apply hx.trans
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fixedParameter, lineParameter, symmetric, fixedHermitianEquiv, hb,
        CharTwo.add_self_eq_zero]
  · rintro ⟨b,rfl⟩ A hA
    exact line_fixed F σ hσ A hA b

/-- The fixed-field Levi subgroup inside the actual plane residual. -/
def fixedLeviGroup : Subgroup L :=
  ((levi F σ hσ).comp (fixedSL F σ).subtype).range

theorem fixedLeviGroup_le_centralizer : fixedLeviGroup F σ hσ ≤ C := by
  rintro _ ⟨a,rfl⟩
  apply (mem_shortCentralizer F σ hσ _).mpr
  change factorRestriction F (form F σ hσ) (levi F σ hσ a.val) ∈ fixedSL F σ
  rw [factorRestriction_levi]
  exact a.property

private theorem radicalHom_conj (a : L) (X : Multiplicative (hermitianMatrices F σ)) :
    a * radicalHom F σ hσ X * a⁻¹ = radicalHom F σ hσ (Multiplicative.ofAdd
      (hermitianCongruence F σ hσ (factorRestriction F (form F σ hσ) a) X.toAdd)) :=
  congrArg Subtype.val (radicalEquiv_conj F σ hσ a X)

theorem shortLine_le_orthogonal : shortLine F σ hσ ≤ orthogonalRadical F σ hσ := by
  rintro _ ⟨b,rfl⟩
  exact ⟨(lineParameter F σ).toMultiplicative b, symmetric_mem F σ 0 b.toAdd 0,rfl⟩

/-- The fixed line is central in the complete residual short-root centralizer. -/
theorem shortLine_le_center : (shortLine F σ hσ).subgroupOf C ≤ center C := by
  intro x hx
  obtain ⟨b,hb⟩ := hx
  apply mem_center_iff.mpr
  intro a
  apply Subtype.ext
  change a.val * x.val = x.val * a.val
  apply mul_inv_eq_iff_eq_mul.mp
  change lineHom F σ hσ b = x.val at hb
  rw [←hb]
  change a.val * radicalHom F σ hσ (Multiplicative.ofAdd (lineParameter F σ b.toAdd)) * a.val⁻¹ = _
  rw [radicalHom_conj, toAdd_ofAdd, line_fixed F σ hσ _ ((mem_shortCentralizer F σ hσ _).mp a.property)]
  rfl

/-- The orthogonal three-space has exactly this q-element fixed subgroup. -/
theorem orthogonal_centralizer :
    orthogonalRadical F σ hσ ⊓ centralizer (fixedLeviGroup F σ hσ : Set L) = shortLine F σ hσ := by
  apply le_antisymm
  · rintro x ⟨⟨X,hX,rfl⟩,hc⟩
    have hx : ∀ A ∈ fixedSL F σ, hermitianCongruence F σ hσ A X.toAdd = X.toAdd := by
      intro A hA
      have h := hc (levi F σ hσ A) ⟨⟨A,hA⟩,rfl⟩
      change levi F σ hσ A * radicalHom F σ hσ X = radicalHom F σ hσ X * levi F σ hσ A at h
      have hh : (levi F σ hσ A) * radicalHom F σ hσ X * (levi F σ hσ A)⁻¹ = radicalHom F σ hσ X := by
        rw [h,mul_inv_cancel_right]
      rw [radicalHom_conj, factorRestriction_levi] at hh
      exact congrArg Multiplicative.toAdd (radicalHom_injective F σ hσ hh)
    obtain ⟨b,hb⟩ := (fixed_iff_line F σ hσ X.toAdd hX).mp hx
    exact ⟨Multiplicative.ofAdd b, congrArg (fun Y => radicalHom F σ hσ (Multiplicative.ofAdd Y)) hb.symm⟩
  · intro x hx
    refine ⟨shortLine_le_orthogonal F σ hσ hx,?_⟩
    let a : C := ⟨x,(orthogonalRadical_le_shortCentralizer F σ hσ) (shortLine_le_orthogonal F σ hσ hx)⟩
    have ha : a ∈ center C := shortLine_le_center F σ hσ hx
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨y,fixedLeviGroup_le_centralizer F σ hσ hy⟩)

/-- The original marked long root, in the short-root centralizer. -/
def longMark : C :=
  radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (longParameter F σ))

private theorem normal_contains_diagonal (N : Subgroup C) [N.Normal]
    (hz : longMark F σ hσ ∈ N) (a : K) :
    radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (symmetric F σ a 0 0)) ∈ N := by
  by_cases ha : a = 0
  · have he : symmetric F σ a 0 0 = 0 := by
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
  have he : hermitianCongruence F σ hσ A (longParameter F σ) = symmetric F σ a 0 0 := by
    apply Subtype.ext
    have hh := congrArg Subtype.val hr2
    change (r:F)^2 = (a:F) at hh
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianCongruence,A,longParameter,symmetric,fixedHermitianEquiv,
        adjoint,Fin.sum_univ_two,Matrix.vecMul,dotProduct,hrf,←pow_two,hh]
  have hn := (show N.Normal from inferInstance).conj_mem (longMark F σ hσ) hz (fixedLevi F σ hσ ⟨A,hA⟩)
  change fixedLevi F σ hσ ⟨A,hA⟩ * radicalIntoCentralizer F σ hσ
    (Multiplicative.ofAdd (longParameter F σ)) * (fixedLevi F σ hσ ⟨A,hA⟩)⁻¹ ∈ N at hn
  rw [radicalIntoCentralizer_conj] at hn
  simpa only [fixedLevi,factorRestriction_levi,toAdd_ofAdd,he] using hn

/-- The long root normally generates the entire orthogonal three-space
inside the literal short-root centralizer. -/
theorem long_normalClosure :
    normalClosure ({longMark F σ hσ} : Set C) =
      (orthogonalRadical F σ hσ).subgroupOf C := by
  let N := normalClosure ({longMark F σ hσ} : Set C)
  have hz : longMark F σ hσ ∈ N := subset_normalClosure (Set.mem_singleton _)
  apply le_antisymm
  · apply normalClosure_le_normal
    rintro x rfl
    refine ⟨Multiplicative.ofAdd (longParameter F σ),?_,rfl⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [longParameter]
  · rintro x ⟨X,hX,he⟩
    have hx : radicalIntoCentralizer F σ hσ X = x := Subtype.ext he
    rw [←hx]
    let p := fixedHermitianEquiv F σ ⟨X.toAdd,hX⟩
    have hcoord : X.toAdd = symmetric F σ p.1 p.2.1 p.2.2 :=
      (congrArg Subtype.val ((fixedHermitianEquiv F σ).symm_apply_apply ⟨X.toAdd,hX⟩)).symm
    have hd := normal_contains_diagonal F σ hσ N hz
    have hs (a : K) : radicalIntoCentralizer F σ hσ
        (Multiplicative.ofAdd (symmetric F σ 0 0 a)) ∈ N := by
      have hn := (show N.Normal from inferInstance).conj_mem _ (hd a) (fixedLevi F σ hσ ⟨cubic F,cubic_mem_fixedSL F σ⟩)
      rw [radicalIntoCentralizer_conj] at hn
      have he : hermitianCongruence F σ hσ (cubic F) (symmetric F σ a 0 0) = symmetric F σ 0 0 a := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hermitianCongruence,cubic,symmetric,fixedHermitianEquiv,
            adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
      simpa only [fixedLevi,factorRestriction_levi,toAdd_ofAdd,he] using hn
    have ho (b : K) : radicalIntoCentralizer F σ hσ
        (Multiplicative.ofAdd (symmetric F σ 0 b 0)) ∈ N := by
      have hn := (show N.Normal from inferInstance).conj_mem _ (hs b) (fixedLevi F σ hσ ⟨cubic F,cubic_mem_fixedSL F σ⟩)
      rw [radicalIntoCentralizer_conj] at hn
      have he : hermitianCongruence F σ hσ (cubic F) (symmetric F σ 0 0 b) = symmetric F σ b b b := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hermitianCongruence,cubic,symmetric,fixedHermitianEquiv,
            adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
      have hn' : radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (symmetric F σ b b b)) ∈ N := by
        simpa only [fixedLevi,factorRestriction_levi,toAdd_ofAdd,he] using hn
      have hsum : symmetric F σ b b b + symmetric F σ b 0 0 + symmetric F σ 0 0 b = symmetric F σ 0 b 0 := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [symmetric,fixedHermitianEquiv,CharTwo.add_self_eq_zero]
      have hh := N.mul_mem (N.mul_mem hn' (hd b)) (hs b)
      rw [←map_mul,←map_mul] at hh
      change radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd
        (symmetric F σ b b b + symmetric F σ b 0 0 + symmetric F σ 0 0 b)) ∈ N at hh
      rwa [hsum] at hh
    have hsum : symmetric F σ p.1 0 0 + symmetric F σ 0 p.2.1 0 + symmetric F σ 0 0 p.2.2 = X.toAdd := by
      rw [hcoord]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [symmetric,fixedHermitianEquiv]
    have hh := N.mul_mem (N.mul_mem (hd p.1) (ho p.2.1)) (hs p.2.2)
    rw [←map_mul,←map_mul] at hh
    change radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd
      (symmetric F σ p.1 0 0 + symmetric F σ 0 p.2.1 0 + symmetric F σ 0 0 p.2.2)) ∈ N at hh
    simpa only [hsum,ofAdd_toAdd] using hh

/-- The fixed-field SL₂ acts inside the literal short-root centralizer. -/
def fixedLeviHom : SpecialLinearGroup (Fin 2) K →* C :=
  ((levi F σ hσ).comp (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype)).codRestrict C (by
    intro A
    apply (mem_shortCentralizer F σ hσ _).mpr
    change factorRestriction F (form F σ hσ) (levi F σ hσ _) ∈ fixedSL F σ
    rw [factorRestriction_levi]
    exact ⟨A,rfl⟩)

private theorem fixedLevi_mem_primeTo (A : fixedSL F σ) :
    fixedLevi F σ hσ A ∈ primeToResidual 2 C := by
  obtain ⟨B,hB⟩ := A.property
  have he : fixedLeviHom F σ hσ B = fixedLevi F σ hσ A := by
    apply Subtype.ext
    change levi F σ hσ (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B) = levi F σ hσ A.val
    rw [hB]
  rw [←he]
  exact Matrix.SL2.map_mem_primeToResidual 2 (fixedLeviHom F σ hσ) B

/-- F.4.42's fixed line uses the genuine O^{2′} of the local centralizer. -/
theorem orthogonal_primeTo_fixed :
    (orthogonalRadical F σ hσ).subgroupOf C ⊓ centralizer (primeToResidual 2 C : Set C) =
      (shortLine F σ hσ).subgroupOf C := by
  apply le_antisymm
  · intro x hx
    apply (orthogonal_centralizer F σ hσ).le
    refine ⟨hx.1,?_⟩
    rintro y ⟨A,rfl⟩
    exact congrArg Subtype.val (hx.2 (fixedLevi F σ hσ A) (fixedLevi_mem_primeTo F σ hσ A))
  · intro x hx
    exact ⟨shortLine_le_orthogonal F σ hσ hx,
      center_le_centralizer _ (shortLine_le_center F σ hσ hx)⟩

/-- The marked short-root involution in its own centralizer. -/
def shortMark : C := ⟨shortLocal F σ hσ, mem_centralizer_singleton_iff.mpr rfl⟩

theorem shortMark_mem_line : shortMark F σ hσ ∈ (shortLine F σ hσ).subgroupOf C :=
  ⟨Multiplicative.ofAdd (1:K),rfl⟩

theorem shortMark_order : orderOf (shortMark F σ hσ) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    exact congrArg (fun q : radical F σ hσ => q.val) (radical_sq F σ hσ
      (radicalEquiv F σ hσ (Multiplicative.ofAdd (shortParameter F σ))))
  · intro he
    have hh := congrArg (fun x : C => x.val.val.val.val 0 2) he
    exact one_ne_zero hh

theorem longMark_order : orderOf (longMark F σ hσ) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    exact congrArg (fun q : radical F σ hσ => q.val) (radical_sq F σ hσ
      (radicalEquiv F σ hσ (Multiplicative.ofAdd (longParameter F σ))))
  · intro he
    have hh := congrArg (fun x : C => x.val.val.val.val 0 3) he
    exact one_ne_zero hh

/-- The entire short-root line, not just its marked involution, is needed for q>2. -/
theorem marked_cyclic_lt_line (hK : 2 < Nat.card K) :
    zpowers (shortMark F σ hσ) < (shortLine F σ hσ).subgroupOf C := by
  apply lt_of_le_of_ne (zpowers_le.mpr (shortMark_mem_line F σ hσ))
  intro he
  have hc := congrArg (fun D : Subgroup C => Nat.card D) he
  rw [Nat.card_zpowers, shortMark_order,
    Nat.card_congr (subgroupOfEquivOfLe ((shortLine_le_orthogonal F σ hσ).trans
      (orthogonalRadical_le_shortCentralizer F σ hσ))).toEquiv, shortLine_card] at hc
  omega

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
