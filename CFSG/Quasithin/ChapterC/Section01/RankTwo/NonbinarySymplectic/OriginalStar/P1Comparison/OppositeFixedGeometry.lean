module
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane

/-!
# Fixed vectors of cubic elementary symplectic actors

An elementary subgroup of order q cubed is conjugate to a point or plane
radical. Its natural fixed space is therefore isotropic. Symplectic duality
then puts every fixed vector in the displacement space of that same actor.

This is the natural-module input for eliminating the opposite fixed-core
intersection in MS93 (3.7), printed p.877.
-/

public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]

/-- An elementary actor of cubic field order has no fixed vectors outside its
natural displacement space. -/
theorem cubic_fixedSpace_le_displacementSpace {n : ℕ}
    (hE : Nat.card E = 2^n) (hn : 0 < n)
    (A : Subgroup (Sp E)) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = Nat.card E ^ 3) :
    TwoLocalCover.fixedSpace A ≤ displacementSpace A := by
  obtain ⟨g,hg⟩ := MaximalElementary.conjugate_radical hE hn A hA
  have hfixed (v : Vector E) (hv : v ∈ TwoLocalCover.fixedSpace A) :
      g • v ∈ TwoLocalCover.fixedSpace (A.map (MulAut.conj g).toMonoidHom) := by
    rintro x ⟨y,hy,rfl⟩
    change (g*y*g⁻¹) • (g • v) = g • v
    simp only [mul_smul,inv_smul_smul,hv y hy]
  have hiso (x : Vector E) (hx : x ∈ TwoLocalCover.fixedSpace A)
      (y : Vector E) (hy : y ∈ TwoLocalCover.fixedSpace A) : form E x y = 0 := by
    rw [←preserves_form g x y]
    rcases hg with hg | hg
    · exact point_isotropic _ _
        (NaturalScalarCubic.point_radical_fixed _ (hg ▸ hfixed x hx))
        (NaturalScalarCubic.point_radical_fixed _ (hg ▸ hfixed y hy))
    · exact plane_isotropic _ _
        (NaturalScalarCubic.plane_radical_fixed _ (hg ▸ hfixed x hx))
        (NaturalScalarCubic.plane_radical_fixed _ (hg ▸ hfixed y hy))
  intro v hv
  have hp : v ∈ (form E).orthogonal (TwoLocalCover.fixedSpace A) :=
    fun w hw => hiso w hw v hv
  rwa [←orthogonal_displacementSpace,LinearMap.BilinForm.orthogonal_orthogonal
    TwoLocalCover.form_nondegenerate TwoLocalCover.form_alternating.isRefl] at hp

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
