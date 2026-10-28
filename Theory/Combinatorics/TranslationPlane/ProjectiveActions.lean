module
public import Theory.Combinatorics.TranslationPlane.ProjectiveRecognition
public import Theory.Combinatorics.ProjectivePlaneMatrixAction

/-!
# Projective affine actions and uniqueness from affine points

Agreement on affine points determines both permutations of a finite
projective-plane collineation. The determinant-one affine matrix with
linear part A and translation b acts by t ↦ At+b on [t₀:t₁:1].
Together these statements identify an original translation/natural
action with its actual matrix collineation, not merely its affine trace.

Source application: the one-field centerfree A₂ recognition in DGS,
Groups and Graphs, 10.5 and Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
namespace Configuration.Collineation
variable {P L : Type*} [Membership P L] [Finite P] [Finite L] [ProjectivePlane P L]

/-- Agreement on all affine points determines a collineation of the whole plane. -/
theorem ext_affine (l : L) {g h : Collineation P L}
    (he : ∀ p : P, p ∉ l → pointHom P L g p = pointHom P L h p) : g = h := by
  have hl (m : L) (hm : m ≠ l) : lineHom P L g m = lineHom P L h m := by
    obtain ⟨p,q,hpm,hpl,hqm,hql,hpq⟩ := TranslationPlane.exists_two_affine_points l m hm
    have hpg := (mem_iff g p m).mpr hpm
    have hqg := (mem_iff g q m).mpr hqm
    have hph := (mem_iff h p m).mpr hpm
    have hqh := (mem_iff h q m).mpr hqm
    rw [←he p hpl] at hph
    rw [←he q hql] at hqh
    exact (Nondegenerate.eq_or_eq hpg hqg hph hqh).resolve_left
      (fun hh => hpq ((pointHom P L g).injective hh))
  have hall (m : L) : lineHom P L g m = lineHom P L h m := by
    by_cases hm : m = l
    · subst m
      obtain ⟨n,hn⟩ := (lineHom P L h).surjective (lineHom P L g l)
      by_cases hnl : n = l
      · exact (hnl ▸ hn).symm
      · have hh := (lineHom P L g).injective ((hl n hnl).trans hn)
        exact (hnl hh).elim
    · exact hl m hm
  apply ext _ hall
  intro p
  have hc : 1 < Nat.card {m : L // p ∈ m} :=
    lt_trans (by decide) (ProjectivePlane.two_lt_lineCount L p)
  let : Nontrivial {m : L // p ∈ m} := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨m,n,hmn⟩ := exists_pair_ne {m : L // p ∈ m}
  have hgm := (mem_iff g p m).mpr m.property
  have hgn := (mem_iff g p n).mpr n.property
  have hhm := (mem_iff h p m).mpr m.property
  have hhn := (mem_iff h p n).mpr n.property
  rw [←hall m] at hhm
  rw [←hall n] at hhn
  exact (Nondegenerate.eq_or_eq hgm hhm hgn hhn).resolve_right
    (fun hh => hmn (Subtype.ext ((lineHom P L g).injective hh)))

end Configuration.Collineation

namespace Configuration.TranslationPlane.FieldChart
open Matrix Projectivization
open scoped MatrixGroups
variable {F : Type*} [Field F]

/-- The determinant-one affine matrix with linear part A and translation b. -/
def affineMatrix (A : SL(2,F)) (b : Fin 2 → F) : SL(3,F) :=
  ⟨!![A.val 0 0,A.val 0 1,b 0; A.val 1 0,A.val 1 1,b 1; 0,0,1],by
    simp only [Matrix.det_fin_three]
    change A.val 0 0 * A.val 1 1 * 1 - A.val 0 0 * b 1 * 0 -
      A.val 0 1 * A.val 1 0 * 1 + A.val 0 1 * b 1 * 0 +
      b 0 * A.val 1 0 * 0 - b 0 * A.val 1 1 * 0 = 1
    simp only [mul_one,mul_zero,sub_zero,add_zero]
    exact (Matrix.det_fin_two A.val) ▸ A.property⟩

theorem affineMatrix_point (A : SL(2,F)) (b t : Fin 2 → F) :
    affineMatrix A b • point F t = point F (Matrix.mulVec A.val t + b) := by
  change affineMatrix A b • Projectivization.mk F ![t 0,t 1,1] _ = _
  rw [Projectivization.smul_mk]
  have hv : (affineMatrix A b) • ![t 0,t 1,1] =
      ![(Matrix.mulVec A.val t + b) 0,(Matrix.mulVec A.val t + b) 1,1] := by
    change (affineMatrix A b).val *ᵥ _ = _
    ext i
    fin_cases i <;> simp [affineMatrix,Matrix.mulVec, dotProduct,Fin.sum_univ_three,Fin.sum_univ_two]
  exact congrArg (fun x : {v : Fin 3 → F // v ≠ 0} => Projectivization.mk' F x)
    (Subtype.ext hv)

/-- The native affine action on both projective fibers. -/
def affineCollineation (A : SL(2,F)) (b : Fin 2 → F) : Collineation (PG F) (PG F) :=
  specialLinearCollineation (affineMatrix A b)

@[simp] theorem affineCollineation_point (A : SL(2,F)) (b t : Fin 2 → F) :
    Collineation.pointHom _ _ (affineCollineation A b) (point F t) =
      point F (Matrix.mulVec A.val t + b) :=
  affineMatrix_point A b t

/-- The native translation, including its line-covector action. -/
def translation (b : Fin 2 → F) : Collineation (PG F) (PG F) :=
  affineCollineation 1 b

@[simp] theorem translation_point (b t : Fin 2 → F) :
    Collineation.pointHom _ _ (translation b) (point F t) = point F (b + t) := by
  rw [translation,affineCollineation_point,Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mulVec,add_comm]

end Configuration.TranslationPlane.FieldChart
