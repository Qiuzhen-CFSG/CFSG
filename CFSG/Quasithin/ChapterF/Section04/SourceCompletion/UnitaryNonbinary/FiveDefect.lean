module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveApartment
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.CartanTransport
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveDiagonal

/-!
# The full Cartan constraints on the PSU₅(4) completion defect

The actual fourth rotation power is represented by an involutory full-middle
automorphism. Faithful endpoint transport proves that it preserves both
native parabolics and fixes both reflections and the whole native projective
diagonal Cartan. The matrix field has order sixteen and the scalar kernel
of order five is retained throughout; no injective SU₅ projection is used.

Native rigidity remains necessary to eliminate the defect. This is not
F.4.24 recognition. Source: Aschbacher–Smith F.4.10,16–17,24,
printed pp.279,282–283,287 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.UnitaryFive
open SmallCompletion.FivePaths
variable (U : GreenBook.UnitaryFive.Model 4)
variable (t : U.F) (ht : t + U.form.conj t = 1)

/-- The image of the full native SU Cartan in the actual projective group.
The SU₅ scalar kernel is retained. -/
def diagonalCartan : Set U.Carrier :=
  {b | ∃ g : U.form.specialSubgroup, SmallCompletion.FiveDiagonal.IsDiagonal U.form t g ∧
    project U.form g=b}

private theorem diagonalCartan_flag (b : U.Carrier)
    (hb : b∈diagonalCartan U t) : b∈U.leftParabolic ⊓ U.rightParabolic := by
  obtain ⟨g,hg,rfl⟩ := hb
  have hh := SmallCompletion.FiveDiagonal.mem_flag U.form t g hg
  exact ⟨⟨g,hh.1,rfl⟩,⟨g,hh.2,rfl⟩⟩

private theorem point_diagonalCartan (b : U.Carrier)
    (hb : b∈diagonalCartan U t) :
    (point U t ht).val*b*(point U t ht).val⁻¹∈diagonalCartan U t := by
  obtain ⟨g,hg,rfl⟩ := hb
  refine ⟨_,SmallCompletion.FiveDiagonal.point_conj U.form t ht U.matrix g hg,?_⟩
  simp only [map_mul,map_inv]
  rfl

private theorem plane_diagonalCartan (b : U.Carrier)
    (hb : b∈diagonalCartan U t) :
    (plane U t ht).val*b*(plane U t ht).val⁻¹∈diagonalCartan U t := by
  obtain ⟨g,hg,rfl⟩ := hb
  refine ⟨_,SmallCompletion.FiveDiagonal.plane_conj U.form t ht U.matrix g hg,?_⟩
  simp only [map_mul,map_inv]
  rfl

private theorem native_fourth : ((plane U t ht).val*(point U t ht).val)^4=1 := by
  change (project U.form (pairSwap U.form t ht U.matrix)*
    project U.form (middleSwap U.form t ht U.matrix))^4=1
  rw [←map_mul,←map_pow]
  change project U.form (SmallCompletion.FivePaths.rotation U.form t ht U.matrix ^ 4)=1
  rw [rotation_fourth,map_one]

/-- The actual PSU₅(4) fourth-power defect preserves both native parabolics,
fixes both reflections and fixes the entire projective native Cartan.
The full extension and its possible outer involution are retained. -/
theorem fourth_defect (E : FiveExtension U)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) :
    ∃ a : E.middle, c.middle a=rotation U t ht E c ^ 4 ∧
      SourceExtension.CartanFixedInvolution (point U t ht) (plane U t ht)
        (diagonalCartan U t) a.val := by
  obtain ⟨a,ha⟩ := fourth_mem_middle U t ht E c ho hcard
  have ha2 : a^2=1 := c.middle_injective (by
    rw [map_pow,ha,map_one]
    exact power_sq_eq_one_of_middle U t ht E c 4 ⟨a,ha⟩)
  exact ⟨a,ha,E.rotation_defect_constraints c (five_conj_injective U)
    (point U t ht) (plane U t ht) (point_sq U t ht) (plane_sq U t ht)
    (diagonalCartan U t) (diagonalCartan_flag U t)
    (point_diagonalCartan U t ht) (plane_diagonalCartan U t ht)
    4 (native_fourth U t ht) a ha ha2⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
