module
public import CFSG.Quasithin.ChapterE.Section02.Structure.StarSQTK
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.CComponent.QuotientLifting
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original normal component in the actual star quotient

The normal core of a nonsolvable minimal parabolic equals its solvable
radical. A C-component therefore has nonabelian simple image in H/J.
The actual image is normal, supplements the prescribed image Sylow, and
inherits the original minimal-parabolic structure and maximal subgroup.
Theorems A and C now apply to this precise simple image, rather than to an
abstract carrier. This is the input to the model-by-model E.2.2 proof.

Source: Aschbacher–Smith E.2.2, second paragraph on printed p.216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The actual normal C-component becomes nonabelian simple in H/J. -/
theorem source_normal_simple_image (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
    IsSimpleGroup (K.map q) ∧ ¬ IsMulCommutative (K.map q) ∧
      (K.map q).Normal ∧
      K.map q ⊔ ((T : Subgroup H).map q) = ⊤ := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hJ := ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs
  have hrad : solvableRadical (H ⧸ J) = ⊥ := by
    let e : (H ⧸ J) ≃* (H ⧸ solvableRadical H) := QuotientGroup.quotientMulEquivOfEq hJ
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_solvableRadical_equiv,solvableRadical_quotient_solvableRadical,Subgroup.map_bot]
  have him := hK.map_quotient J
  refine ⟨him.isSimpleGroup_of_solvableRadical_eq_bot hrad,
    him.not_isMulCommutative_of_solvableRadical_eq_bot hrad,inferInstance,?_⟩
  rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective J)]

/-- The exact normal simple image receives Theorem C's genuine complete list. -/
theorem source_normal_simple_catalogue
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremC κ D)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ChapterA.Section02.IsTheoremCModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) := by
  have h := source_normal_simple_image T hP hs K hK hgen
  have hsq := (source_star_sqtk hA hH T hP hs).subgroup
    (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
  exact hC _ h.1 h.2.1 hsq.stronglyQuasithin hsq.isKGroup

/-- The star quotient is itself the original minimal parabolic with trivial core. -/
theorem source_star_minimal_core_free (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) :
    let J := ChapterB.minimalParabolicCore T hP
    let q := QuotientGroup.mk' J
    let hq := QuotientGroup.mk'_surjective J
    let hk : q.ker ≤ J := by rw [QuotientGroup.ker_mk']
    ChapterB.IsMinimalParabolicOver (T.mapSurjective hq) ⊤ ∧
      ChapterB.minimalParabolicCore (T.mapSurjective hq)
        (ChapterB.minimalParabolic_surjective_core T hP q hq hk) = ⊥ := by
  dsimp only
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hq := QuotientGroup.mk'_surjective J
  have hk : q.ker ≤ J := by rw [QuotientGroup.ker_mk']
  refine ⟨ChapterB.minimalParabolic_surjective_core T hP q hq hk,?_⟩
  rw [← ChapterB.minimalParabolicCore_map_core T hP q hq hk]
  exact QuotientGroup.map_mk'_self J
end CFSG.Quasithin.ChapterE.Structure
