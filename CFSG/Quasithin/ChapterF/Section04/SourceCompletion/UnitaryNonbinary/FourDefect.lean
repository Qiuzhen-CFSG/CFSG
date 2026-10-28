module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourApartment
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.CartanTransport
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourDiagonal

/-!
# The full Cartan constraints on the PSU₄ completion defect

The order-bound apartment theorem places the fourth rotation power in the
whole extension overlap. Native centralizer control makes it involutory.
Transport along the actual endpoint maps then shows that this automorphism
preserves both native parabolics and fixes both reflections and every native
diagonal Cartan element, without restricting the entries to the fixed field.
This includes q = 4 and the genuine even outer factors.

Triviality still requires native automorphism rigidity. No recognition
conclusion is assumed or asserted here. Source: Aschbacher–Smith
F.4.10,16–17,24, printed pp.279,282–283,287 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourGeneration
variable (m : ℕ) (hm : 1 ≤ m)
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "J" => UnitaryFourFlag.form F σ hσ
local notation "π" => project F J

/-- The projective image of all diagonal native special unitary matrices. -/
def diagonalCartan : Set (ProjectiveGroup m hm) :=
  {b | ∃ g : MatrixGroup m hm, SmallCompletion.FourDiagonal.IsDiagonal F σ hσ g ∧ π g=b}

private theorem diagonalCartan_flag (b : ProjectiveGroup m hm)
    (hb : b∈diagonalCartan m hm) : b∈pointParabolic m hm ⊓ planeParabolic m hm := by
  obtain ⟨g,hg,rfl⟩ := hb
  have hh := SmallCompletion.FourDiagonal.mem_borel F σ hσ g hg
  exact ⟨⟨g,hh.1,rfl⟩,⟨g,hh.2,rfl⟩⟩

private theorem point_diagonalCartan (b : ProjectiveGroup m hm)
    (hb : b∈diagonalCartan m hm) :
    (point m hm).val*b*(point m hm).val⁻¹∈diagonalCartan m hm := by
  obtain ⟨g,hg,rfl⟩ := hb
  refine ⟨_,SmallCompletion.FourDiagonal.point_conj F σ hσ g hg,?_⟩
  simp only [map_mul,map_inv]
  rfl

private theorem plane_diagonalCartan (b : ProjectiveGroup m hm)
    (hb : b∈diagonalCartan m hm) :
    (plane m hm).val*b*(plane m hm).val⁻¹∈diagonalCartan m hm := by
  obtain ⟨g,hg,rfl⟩ := hb
  refine ⟨_,SmallCompletion.FourDiagonal.plane_conj F σ hσ g hg,?_⟩
  simp only [map_mul,map_inv]
  rfl

private theorem native_fourth : ((plane m hm).val*(point m hm).val)^4=1 := by
  let s : MatrixGroup m hm := middleSwap F σ hσ
  let t : MatrixGroup m hm := pairSwap F σ hσ
  have hr : (t*s)^4=1 := SmallCompletion.FourDiagonal.rotation_fourth F σ hσ
  have hh := (map_pow (projection m hm) (t*s) 4).symm.trans
    ((congrArg (projection m hm) hr).trans (map_one _))
  have he : projection m hm (t*s)=(plane m hm).val*(point m hm).val :=
    map_mul (projection m hm) t s
  exact (congrArg (fun b : ProjectiveGroup m hm => b^4) he).symm.trans hh

/-- For a full extension, the actual fourth-power defect fixes the entire
native Cartan and both reflections, and preserves the two native parabolics.
No identity or native-subgroup membership of the defect is assumed. -/
theorem fourth_defect (hmgt : 1 < m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) :
    ∃ a : E.middle, c.middle a=rotation m hm E c ^ 4 ∧
      SourceExtension.CartanFixedInvolution (point m hm) (plane m hm)
        (diagonalCartan m hm) a.val := by
  obtain ⟨a,ha⟩ := fourth_mem_middle m hm hmgt E c ho hcard
  have ha2 : a^2=1 := c.middle_injective (by
    rw [map_pow,ha,map_one]
    exact power_sq_eq_one_of_middle m hm E c 4 ⟨a,ha⟩)
  exact ⟨a,ha,E.rotation_defect_constraints c (four_conj_injective m hm)
    (point m hm) (plane m hm) (point_sq m hm) (plane_sq m hm)
    (diagonalCartan m hm) (diagonalCartan_flag m hm)
    (point_diagonalCartan m hm) (plane_diagonalCartan m hm)
    4 (native_fourth m hm) a ha ha2⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
