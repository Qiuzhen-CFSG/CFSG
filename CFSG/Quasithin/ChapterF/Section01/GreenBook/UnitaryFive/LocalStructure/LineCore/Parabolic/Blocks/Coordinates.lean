module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parabolic.Model
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Blocks.Flag

/-!
# Concrete full block coordinates for the unitary-five model

These definitions specialize the verified radical, SU₃ and cubic-torus matrix
map. The map is injective. The exact flag preimage is proved; surjectivity remains
a separate matrix obligation; no residual or exhaustion hypothesis
is stored in the model.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive.LineCore
open Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
open Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
variable (M : Model 4)

abbrev LineCubic := Cubic (F := M.F)

abbrev LineFullProduct := FullProduct M.form M.conjugation

abbrev lineFullMap (c : M.F) (hc : c + M.form.conj c = 1) :
    M.LineFullProduct →* M.leftParabolic := fullMap M.form M.conjugation c hc M.matrix

abbrev lineCubicEmbedding (c : M.F) (hc : c + M.form.conj c = 1) :
    M.LineCubic →* M.leftParabolic := cubicParabolic M.form M.conjugation c hc M.matrix

abbrev lineRadicalLeviInclusion : M.LineRadicalLevi →* M.LineFullProduct :=
  radicalLeviInclusion M.form M.conjugation

abbrev lineProductProjection : M.LineFullProduct →* M.LocalUnitaryGroup :=
  productProjection M.form M.conjugation

abbrev lineProductCharacter : M.LineFullProduct →* M.LineCubic :=
  productCharacter M.form M.conjugation

theorem lineCubic_card : Nat.card M.LineCubic = 3 := cubic_card M.local_field_card

instance lineCubic_solvable : Group.IsSolvable M.LineCubic := inferInstance

theorem lineFullMap_injective (c : M.F) (hc : c + M.form.conj c = 1) :
    Function.Injective (M.lineFullMap c hc) :=
  fullMap_injective M.form M.conjugation c hc M.matrix

theorem lineFullMap_comp_radicalLeviInclusion (c : M.F) (hc : c + M.form.conj c = 1) :
    (M.lineFullMap c hc).comp M.lineRadicalLeviInclusion = M.lineRadicalLeviMap :=
  fullMap_comp_radicalLeviInclusion M.form M.conjugation c hc M.matrix

theorem lineProductCharacter_ker : M.lineProductCharacter.ker = M.lineRadicalLeviInclusion.range :=
  productCharacter_ker M.form M.conjugation

theorem lineProduct_common_kernel :
    M.lineProductProjection.ker ⊓ M.lineProductCharacter.ker =
      (SemidirectProduct.inl : M.LineRadicalCoordinates →* M.LineFullProduct).range :=
  product_common_kernel M.form M.conjugation

theorem lineCubicEmbedding_mem_overlap (c : M.F) (hc : c + M.form.conj c = 1)
    (b : M.LineCubic) : M.lineCubicEmbedding c hc b ∈ M.overlap.subgroupOf M.leftParabolic :=
  cubicParabolic_mem_overlap M.form M.conjugation c hc M.matrix b

theorem lineCubicEmbedding_commute_levi (c : M.F) (hc : c + M.form.conj c = 1)
    (b : M.LineCubic) (A : M.LocalUnitaryGroup) :
    Commute (M.lineCubicEmbedding c hc b) (M.lineLeviEmbedding A) :=
  cubicParabolic_commute_levi M.form M.conjugation c hc M.matrix b A

theorem lineRadicalEmbedding_cubicAction (c : M.F) (hc : c + M.form.conj c = 1)
    (b : M.LineCubic) (u : M.LineRadicalCoordinates) :
    M.lineRadicalEmbedding (cubicAction M.form M.conjugation b u) =
      M.lineCubicEmbedding c hc b * M.lineRadicalEmbedding u * (M.lineCubicEmbedding c hc b)⁻¹ :=
  toParabolic_cubicAction M.form M.conjugation c hc M.matrix b u

/-- The plane in the original flag induces the marked isotropic middle line. -/
theorem lineFullMap_mem_overlap_iff (c : M.F) (hc : c + M.form.conj c = 1)
    (x : M.LineFullProduct) :
    M.lineFullMap c hc x ∈ M.overlap.subgroupOf M.leftParabolic ↔
      x.right.1 ∈ M.localUnitaryLineStabilizer := by
  exact (fullMap_mem_overlap_iff M.form M.conjugation c hc M.matrix x).trans
    (M.mem_localUnitaryLineStabilizer_iff x.right.1).symm

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
