module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PointParabolic

/-!
# Transitivity on the center of the unitary-four point residual

The center of the vector stabilizer lies in the Heisenberg radical, by
its explicit centralizer calculation. The radical's center has the fixed
field as its last coordinate. Diagonal matrices with entries s,s⁻¹,s,s⁻¹
scale this coordinate by s². Frobenius is surjective on the finite fixed
field, giving transitivity on all its nonzero elements.

This is the native center-orbit input to Aschbacher–Smith 5.3.3, printed
p.659 of `refs/quasithin.pdf`; the ambient centralizer bound uses original
uniqueness separately. The conjugators belong to the actual point
parabolic and the stored field involution is retained throughout.
-/

open Subgroup Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "P" => pointParabolicSU F (form F σ hσ)
local notation "κ" => coordinatesOfRadical F σ hσ

private def fixedTorus (s : FixedBy.subfield F σ) (hs : s ≠ 0) : P := by
  let a : F := s
  have ha : a ≠ 0 := fun h => hs (Subtype.ext h)
  have hsa : σ a = a := s.property
  let d : Fin 4 → F := ![a,a⁻¹,a,a⁻¹]
  have hd : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    simp [d, Fin.prod_univ_succ,ha]
  let g : SU F (form F σ hσ) :=
    ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (by rw [hd]; exact one_ne_zero),
      by
        change (form F σ hσ).conjTranspose (Matrix.diagonal d) * gram F *
          Matrix.diagonal d = gram F
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
            Fin.sum_univ_succ, d,ha,hsa],
      Units.ext hd⟩
  exact ⟨g,(mem_pointParabolicSU F _ g).mpr ⟨rfl,rfl,rfl⟩⟩

private theorem center_local_to_radical (x : L) (hx : x ∈ center L) :
    ∃ r : R, r.val = x ∧ r ∈ center R := by
  have hxr : x.val ∈ UnitaryFourConverse.PointParabolic.ambientRadical F σ hσ := by
    apply UnitaryFourConverse.PointParabolic.centralizer_ambientRadical_le F σ hσ
    rintro _ ⟨r,hr,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hx r)
  obtain ⟨r,hr,he⟩ := hxr
  have hrx : r = x := Subtype.ext he
  refine ⟨⟨r,hr⟩,hrx,mem_center_iff.mpr fun a => ?_⟩
  apply Subtype.ext
  change a.val * r = r * a.val
  rw [hrx]
  exact mem_center_iff.mp hx a.val

private theorem radical_center_orbit (hnt : ∃ u, σ u ≠ u)
    (x y : R) (hx : x ∈ center R) (hy : y ∈ center R)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ g ∈ P, y.val.val = g * x.val.val * g⁻¹ := by
  let e := centerEquivFixedField F σ hσ hnt
  let a := (e ⟨x,hx⟩).toAdd
  let b := (e ⟨y,hy⟩).toAdd
  have ha : a ≠ 0 := by
    intro he
    apply hx1
    have he' : e ⟨x,hx⟩ = 1 := congrArg Multiplicative.ofAdd he
    exact congrArg Subtype.val (e.injective (he'.trans e.map_one.symm))
  have hb : b ≠ 0 := by
    intro he
    apply hy1
    have he' : e ⟨y,hy⟩ = 1 := congrArg Multiplicative.ofAdd he
    exact congrArg Subtype.val (e.injective (he'.trans e.map_one.symm))
  obtain ⟨s,hs⟩ := (frobeniusEquiv (FixedBy.subfield F σ) 2).surjective (b/a)
  have hs2 : s^2 = b/a := hs
  have hs0 : s ≠ 0 := by
    intro he
    exact (div_ne_zero hb ha) (by simpa [he] using hs2.symm)
  let g := fixedTorus F σ hσ s hs0
  have hg : g.val ∈ P := g.property
  refine ⟨g.val,hg,?_⟩
  have hxmat : x.val.val.val.val = radicalMatrix F σ (κ x) :=
    congrArg (fun r : R => r.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply x).symm
  have hymat : y.val.val.val.val = radicalMatrix F σ (κ y) :=
    congrArg (fun r : R => r.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply y).symm
  obtain ⟨hx0,hx0'⟩ := (mem_center_radical_iff F σ hσ hnt x).mp hx
  obtain ⟨hy0,hy0'⟩ := (mem_center_radical_iff F σ hσ hnt y).mp hy
  have hz : (κ y).z = (s:F)^2 * (κ x).z := by
    change (b:F) = (s:F)^2 * (a:F)
    exact congrArg Subtype.val ((hs2 ▸ div_mul_cancel₀ b ha).symm)
  have hgm : g.val.val.val = Matrix.diagonal
      ![(s:F), (s:F)⁻¹, (s:F), (s:F)⁻¹] := rfl
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext
  apply Units.ext
  change y.val.val.val.val * g.val.val.val = g.val.val.val * x.val.val.val.val
  rw [hxmat,hymat,hgm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, radicalMatrix,hx0,hx0',hy0,hy0',hz]
  field_simp

/-- The point parabolic is transitive on the nonidentity center of its vector stabilizer. -/
theorem center_orbit (hnt : ∃ u, σ u ≠ u)
    (x : SU F (form F σ hσ)) (hx : x ∈ (center L).map (localSU F (form F σ hσ)).subtype) (hx1 : x ≠ 1)
    (y : SU F (form F σ hσ)) (hy : y ∈ (center L).map (localSU F (form F σ hσ)).subtype) (hy1 : y ≠ 1) :
    ∃ g ∈ P, y = g*x*g⁻¹ := by
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  obtain ⟨r,hr,hrc⟩ := center_local_to_radical F σ hσ x hx
  obtain ⟨s,hs,hsc⟩ := center_local_to_radical F σ hσ y hy
  have hr1 : r ≠ 1 := by
    intro he
    exact hx1 (by rw [←hr,he]; rfl)
  have hs1 : s ≠ 1 := by
    intro he
    exact hy1 (by rw [←hs,he]; rfl)
  obtain ⟨g,hg,he⟩ := radical_center_orbit F σ hσ hnt r s hrc hsc hr1 hs1
  refine ⟨g,hg,?_⟩
  change y.val = g*x.val*g⁻¹
  simpa only [hr,hs] using he

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter
