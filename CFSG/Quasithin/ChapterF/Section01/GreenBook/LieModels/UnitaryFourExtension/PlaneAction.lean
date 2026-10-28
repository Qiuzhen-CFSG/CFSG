module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.PlaneOuter
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneShort.Structure

/-!
# Faithful conjugation on the ordinary unitary plane

The literal ordinary plane embeds into its doubled endpoint by the semidirect
product inclusion. Its image is the kernel of the second-coordinate map, so
conjugation on this image transports to an action on the original plane.

The two-core of the local factor is self-centralizing and has trivial
intersection with the center, giving centerlessness of the ordinary plane.
An element in the kernel of the extended action has either trivial second
coordinate, when centerlessness kills its first coordinate, or the Frobenius
coordinate, when it would make Frobenius inner. The latter contradicts the
proved quotient field action. Hence the extended action is faithful.

The inclusion and conjugation formulas retain the original matrix/projective
coordinates. They supply the concrete faithful-action input for the doubled
plane comparison in the normal A5 branch of Aschbacher--Smith 13.1.7, using
the plane local structure of C.1.7 and F.1.12.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
open Theory.SpecificGroups.ClassicalUnitary
local notation "h1" => (Nat.le_refl 1)
local notation "P" => planeParabolic 1 h1
local notation "E" => plane 1 h1

/-- The plane local factor has trivial center. -/
theorem L2_center_eq_bot (n : ℕ) (hn : 1 ≤ n) : Subgroup.center (L2 n hn) = ⊥ := by
  have hle : Subgroup.center (L2 n hn) ≤ pCore 2 (L2 n hn) := by
    rw [← L2TwoCore_centralizer]
    exact Subgroup.center_le_centralizer _
  rw [← inf_eq_right.mpr hle, L2TwoCore_inf_center]

/-- At q = 2 the whole ordinary plane is centerless. -/
theorem binaryPlane_center_eq_bot : Subgroup.center P = ⊥ := by
  rw [BinaryCompletion.plane_eq_local]
  exact L2_center_eq_bot 1 h1

/-- The literal inclusion of the ordinary plane into its doubled endpoint. -/
def binaryPlaneInclusion : P →* E :=
  (((SemidirectProduct.inl : ProjectiveGroup 1 h1 →* ProjectiveExtension 1 h1).comp
    (P).subtype).codRestrict E (fun g => (mem_plane 1 h1 _).mpr g.property))

theorem binaryPlaneInclusion_val (g : P) :
    (binaryPlaneInclusion g).val = SemidirectProduct.inl g.val := rfl

theorem binaryPlaneInclusion_injective : Function.Injective binaryPlaneInclusion := by
  intro x y h
  apply Subtype.ext
  exact SemidirectProduct.inl_injective (congrArg Subtype.val h)

/-- The second coordinate on the literal extended plane. -/
def binaryPlaneParity : E →* UnitaryFourOuter.C2 :=
  SemidirectProduct.rightHom.comp (E).subtype

/-- The ordinary plane is exactly the second-coordinate kernel. -/
theorem binaryPlaneInclusion_range_eq_ker :
    binaryPlaneInclusion.range = binaryPlaneParity.ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    refine ⟨⟨x.val.left, (mem_plane 1 h1 _).mp x.property⟩, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact (show x.val.right = 1 from hx).symm

theorem binaryPlaneInclusion_range_normal : binaryPlaneInclusion.range.Normal := by
  rw [binaryPlaneInclusion_range_eq_ker]
  infer_instance

local instance : binaryPlaneInclusion.range.Normal := binaryPlaneInclusion_range_normal

/-- Conjugation on the original ordinary plane, through its literal inclusion. -/
def binaryPlaneConjugation : E →* MulAut P :=
  (MulAut.congr (MonoidHom.ofInjective binaryPlaneInclusion_injective).symm).toMonoidHom.comp
    MulAut.conjNormal

/-- The transported action is actual conjugation in the extended plane. -/
theorem binaryPlaneConjugation_conj (x : E) (y : P) :
    binaryPlaneInclusion (binaryPlaneConjugation x y) =
      x * binaryPlaneInclusion y * x⁻¹ := by
  exact MonoidHom.apply_ofInjective_symm binaryPlaneInclusion_injective _

/-- Ordinary plane elements act by their original inner automorphisms. -/
theorem binaryPlaneConjugation_inclusion (g : P) :
    binaryPlaneConjugation (binaryPlaneInclusion g) = MulAut.conj g := by
  apply MulEquiv.ext
  intro y
  apply binaryPlaneInclusion_injective
  rw [binaryPlaneConjugation_conj]
  simp only [MulAut.conj_apply, map_mul, map_inv]

/-- The ambient coordinate formula for the action retains the literal field actor. -/
theorem binaryPlaneConjugation_apply_val (x : E) (y : P) :
    (binaryPlaneConjugation x y).val =
      x.val.left * projectiveAction 1 h1 x.val.right y.val * x.val.left⁻¹ := by
  have h := congrArg (fun z : E => z.val.left) (binaryPlaneConjugation_conj x y)
  change (binaryPlaneConjugation x y).val = _ at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, binaryPlaneInclusion_val,
    SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    SemidirectProduct.inv_left, mul_one, map_mul, map_inv, ← MulAut.mul_apply,
    ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] using h

/-- The whole doubled plane acts faithfully on its ordinary plane subgroup. -/
theorem binaryPlaneConjugation_injective : Function.Injective binaryPlaneConjugation := by
  apply binaryPlaneConjugation.ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  have he : binaryPlaneConjugation x = 1 := hx
  have hf (y : P) :
      x.val.left * projectiveAction 1 h1 x.val.right y.val * x.val.left⁻¹ = y.val := by
    rw [← binaryPlaneConjugation_apply_val, he]
    rfl
  let a : P := ⟨x.val.left, (mem_plane 1 h1 _).mp x.property⟩
  rcases UnitaryFourOuter.c2_cases x.val.right with hc | hc
  · have ha : a ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hy := hf y
      simp only [hc, map_one, MulAut.one_apply] at hy
      change y.val * x.val.left = x.val.left * y.val
      calc
        y.val * x.val.left =
          (x.val.left * y.val * x.val.left⁻¹) * x.val.left := by rw [hy]
        _ = x.val.left * y.val := by group
    have ha1 : a = 1 := by simpa only [binaryPlane_center_eq_bot, Subgroup.mem_bot] using ha
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact SemidirectProduct.ext (congrArg Subtype.val ha1) hc
  · exfalso
    apply binary_projectiveAut_not_plane_inner a⁻¹
    intro y
    have hy := hf y
    rw [hc, projectiveAction_generator] at hy
    change projectiveAut 1 h1 y.val = x.val.left⁻¹ * y.val * (x.val.left⁻¹)⁻¹
    calc
      projectiveAut 1 h1 y.val =
        x.val.left⁻¹ * (x.val.left * projectiveAut 1 h1 y.val * x.val.left⁻¹) *
          x.val.left := by group
      _ = x.val.left⁻¹ * y.val * (x.val.left⁻¹)⁻¹ := by rw [hy]; simp

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
