module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.StarCoordinates
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeAutomizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.QuadraticInnerField
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The complete odd linear-two rows on the original star component

The quotient by the unique maximal subgroup's normal core retains the
original prescribed Sylow and simple normal component. Apply the prime
and quadratic concrete source geometry there, then identify the overlap
and induced automizer with the literal marked source definitions. The
quadratic row retains the same model equivalence for its non-inner-field
witness. No automizer, centralizer, or actor conclusion is assumed.

Source: Aschbacher–Smith E.2.2(2c), printed pp.215–216. The small parameters
five, seven and nine belong to the separate binary model rows. These
geometric conclusions do not assert a generation-parameter equality.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]
omit [Finite H] in
/-- For a normal star component the source automizer is the ordinary conjugation image. -/
theorem sourceAutomizer_eq_map_conjNormal (M K T : Subgroup H) [(sourceImage M K).Normal] :
    sourceAutomizer M K T = (sourceImage M T).map
      (MulAut.conjNormal (H := sourceImage M K)) := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.val,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨x,?_⟩,hx,rfl⟩
    rw [normalizer_eq_top]
    trivial

/-- The full original prime-field geometric row, with every local clause proved. -/
theorem source_odd_prime_linear_model (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 9 < p)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 p) :
    SingleOddLinearModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := sourceImage M K
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : D.Normal := hi.2.2.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hcore : pCore 2 (H ⧸ J) = ⊥ := by
    exact bot_unique ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans
      (Structure.source_star_minimal_core_free T hP).2.le)
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk']; exact le_rfl)).symm
  rcases hm with ⟨F,hF,hfin,hcard,⟨e⟩⟩
  let : Field F := hF
  let : Finite F := hfin
  let : Fact p.Prime := ⟨hp⟩
  have hc := Structure.prime_linear_source_row S hmin D hi.2.2.2 hcore ho hcard hlarge e
  refine ⟨p,1,hp,by omega,by decide,by decide,?_,F,hF,hfin,by simpa using hcard,e,?_,?_,by omega⟩
  · simpa only [pow_one] using hc.1
  · apply (centralizerOverlap_iff_star M K T hK.subnormal).mpr
    change (M.map q).subgroupOf D = _
    rw [←hmax]
    exact hc.2.1
  · rw [sourceAutomizer_eq_map_conjNormal]
    exact hc.2.2

/-- The full quadratic row includes an actual Sylow actor outside the inner-field subgroup. -/
theorem source_odd_quadratic_linear_model (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (p^2)) :
    SingleOddLinearModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := sourceImage M K
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : D.Normal := hi.2.2.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hcore : pCore 2 (H ⧸ J) = ⊥ := by
    exact bot_unique ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans
      (Structure.source_star_minimal_core_free T hP).2.le)
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk']; exact le_rfl)).symm
  rcases hm with ⟨F,hF,hfin,hcard,⟨e⟩⟩
  let : Field F := hF
  let : Finite F := hfin
  let : Fact p.Prime := ⟨hp⟩
  have hc := Structure.quadratic_linear_source_row S hmin D hi.2.2.2 hcore ho hcard hlarge e
  refine ⟨p,2,hp,hlarge,by decide,by decide,hc.1,F,hF,hfin,hcard,e,?_,?_,?_⟩
  · apply (centralizerOverlap_iff_star M K T hK.subnormal).mpr
    change (M.map q).subgroupOf D = _
    rw [←hmax]
    exact hc.2.1
  · rw [sourceAutomizer_eq_map_conjNormal]
    exact hc.2.2
  · intro _
    obtain ⟨a,ha,hnot⟩ := Structure.quadratic_linear_source_matrix_not_inner_field
      S hmin D hi.2.2.2 hcore ho hcard hlarge e
    refine ⟨a,?_,hnot⟩
    rw [sourceAutomizer_eq_map_conjNormal]
    exact ha

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
