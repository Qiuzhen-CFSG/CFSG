module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.StarCoordinates
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.Unitary
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.Linear
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Odd degree-three source geometry on the original component

Apply the proved normal odd linear and unitary families to the literal
simple image of the original C-component in H/J. The quotient preserves
the prescribed Sylow and unique maximal subgroup. The overlap and Sylow
coordinate identities then return the exact centralizer clause to the
original marked source interface. In the unitary case this constructs the
full odd-rank-three model row. No generation-parameter equality is asserted.

Source: Aschbacher–Smith E.2.2(2d), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

/-- The entire odd-unitary model row, with the original quotient and maximal overlap. -/
theorem source_odd_unitary_model (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p) :
    SingleOddRankThreeModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup (K.map q) := hi.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hc := Structure.OddDegreeThree.unitary S hmin (K.map q) hi.2.2.2 hp ho hm
  refine ⟨p,hp,ho,?_,Or.inl ⟨hc.1,hm⟩⟩
  apply (centralizerOverlap_iff_star M K T hK.subnormal).mpr
  change (M.map q).subgroupOf (K.map q) = _
  rw [←hmax]
  exact hc.2

/-- The original odd-linear congruence and centralizer clause, retaining the actual component. -/
theorem source_odd_linear_centralizer (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p) :
    p%4=3 ∧ CentralizerOverlap (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup (K.map q) := hi.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hcore : pCore 2 (H ⧸ J) = ⊥ :=
    bot_unique ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans
      (Structure.source_star_minimal_core_free T hP).2.le)
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hc := Structure.OddDegreeThree.linear S hmin (K.map q) hi.2.2.2 hcore hp ho hm
  refine ⟨hc.1,?_⟩
  apply (centralizerOverlap_iff_star M K T hK.subnormal).mpr
  change (M.map q).subgroupOf (K.map q) = _
  rw [←hmax]
  exact hc.2
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
