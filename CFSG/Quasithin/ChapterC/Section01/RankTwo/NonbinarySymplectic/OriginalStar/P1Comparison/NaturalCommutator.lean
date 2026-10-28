module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.IntersectionCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.RadicalCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.SpanAction

/-!
# Natural rows of the original commutator pairing

On the whole natural kernel, the commutator pairing with the point radical
is scalar multiplication by the original natural-line coordinate. The
calculation uses the same group quotient and natural marking throughout.
This identifies the restriction of the relative-centralizer scalar map in
Meierfrankenfeld--Stellmacher (1993), (3.7), printed p.877.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement CharTwo
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
variable {F G : Type*} [Field F] [Group G] [CharP F 2]
variable {κ : G →* Sp F} {A B : Subgroup G} (s : MarkedPair κ A B)

private theorem middleProjection_radical_difference
    (g : Sp F) (hg : g ∈ pointRadicalAmbient) (v : Vector F) :
    middleProjection (v - g • v) = coordinate v •
      ![g.val (.inl 1) (.inr 0), g.val (.inr 1) (.inr 0)] := by
  obtain ⟨r, hr, rfl⟩ := hg
  rw [pointRadical_eq_element r hr]
  ext i
  fin_cases i <;>
    simp [middleProjection, middleIndex, coordinate, pointRadicalElement,
      pointRadicalMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, CharTwo.sub_eq_add, mul_comm]
  rw [add_comm (v (.inr 0) * _), CharTwo.add_cancel_left]

/-- The natural kernel contributes its natural-line scalar to every radical row. -/
theorem natural_commutator_middle [Finite G]
    (a : A) (q : pointRadicalAmbient.comap κ) :
    intersectionMiddle s
      ⟨⁅(a : G), (q : G)⁆, pointCore_span_commutator_le_intersection s
        (commutator_mem_commutator ((show A ≤ A ⊔ B from le_sup_left) a.property) q.property)⟩ =
      Multiplicative.ofAdd ((s.naturalLine a).toAdd • (radicalCoordinates κ q).toAdd) := by
  let : A.Normal := s.kernel ▸ inferInstance
  let y : A := ⟨(q : G) * a * (q : G)⁻¹,
    (inferInstance : A.Normal).conj_mem _ a.property q⟩
  let c : A := ⟨⁅(a : G), (q : G)⁆,
    (pointCore_span_commutator_le_intersection s
      (commutator_mem_commutator ((show A ≤ A ⊔ B from le_sup_left) a.property) q.property)).1⟩
  have hc : c = a * y⁻¹ := by
    apply Subtype.ext
    simp [c, y, commutatorElement_def, mul_assoc]
  have hn : (s.natural c).toAdd = (s.natural a).toAdd - κ q • (s.natural a).toAdd := by
    rw [hc, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [s.natural_conjugation q a y rfl]
    exact (sub_eq_add_neg _ _).symm
  apply Multiplicative.toAdd.injective
  change middleProjection (s.natural c).toAdd =
    coordinate (s.natural a).toAdd •
      ![(κ q).val (.inl 1) (.inr 0), (κ q).val (.inr 1) (.inr 0)]
  rw [hn]
  exact middleProjection_radical_difference (κ q) q.property (s.natural a).toAdd

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
