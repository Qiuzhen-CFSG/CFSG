module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.IntersectionAssembly
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.CoreAssembly
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The binary branch over an arbitrary two-element source field

Entrywise transport through the unique prime-field isomorphism, after the
proved determinant-one alignment, gives an actual binary Hypothesis on the
same ambient groups. This preserves the marked point and intertwines the
original star action; it is not a change of group-family label.
The cubic terminal exclusion and V≤L₁ therefore hold for any field of order two.

The SL field isomorphism is the existing `Atlas.fieldEquivSL` from
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`, with its source attribution
and license retained there. Source application: Aschbacher–Smith,
G.2.5(8), printed pp.335–336, and 12.8.8, printed pp.851–852.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.BinaryField
open ScalarConstituents
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {g h : G}
  {d : Hypothesis D F 1 g h} (a : PointAlignment d)

noncomputable def fieldEquiv (d : Hypothesis D F 1 g h) : F ≃+* ZMod 2 := by
  let := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card,pow_one] using d.field_card)).symm

def vectorEquiv (e : F ≃+* ZMod 2) : (Fin 3 → F) ≃+ (Fin 3 → ZMod 2) :=
  AddEquiv.piCongrRight (fun _ => e.toAddEquiv)

omit [Finite G] [Finite F] in
private theorem map_natural (e : F ≃+* ZMod 2) (x : SL(3,F)) (v : Fin 3 → F) :
    vectorEquiv e (x.val *ᵥ v) =
      (Atlas.fieldEquivSL 3 e x).val *ᵥ vectorEquiv e v := by
  ext i
  simp [vectorEquiv,Atlas.fieldEquivSL,SpecialLinearGroup.map_apply_coe,
    mulVec,dotProduct,Fin.sum_univ_three]

/-- Re-identifying a two-element field preserves the original groups, points and star action. -/
noncomputable def binaryHypothesis (e : F ≃+* ZMod 2) : Hypothesis D (ZMod 2) 1 g h where
  setup := d.setup
  exponent_pos := by decide
  field_card := by simp
  span_eq := d.span_eq
  model := (d.model.trans (MulAut.conj a.basis⁻¹)).trans (Atlas.fieldEquivSL 3 e)
  coordinates := (alignedCoordinates a).trans (vectorEquiv e).toMultiplicative
  equivariant l v := by
    change vectorEquiv e (a.basis⁻¹ • (d.coordinates _).toAdd) = _
    rw [d.equivariant l v]
    have he := a.projection_natural l (d.coordinates v).toAdd
    exact (congrArg (vectorEquiv e) he.symm).trans
      (map_natural e (a.projection l) (a.basis⁻¹ • (d.coordinates v).toAdd))
  point := Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents.point.toSubmodule
  point_dimension := Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents.dimensions.1
  point_mem v := by
    rw [← aligned_point a v]
    change (alignedCoordinates a v).toAdd ∈ ScalarConstituents.naturalLine F ↔
      vectorEquiv e (alignedCoordinates a v).toAdd ∈
        Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents.point
    rw [ScalarConstituents.mem_naturalLine,
      Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents.mem_point]
    simp [vectorEquiv]
  star_U_ne_bot := d.star_U_ne_bot
  g_mem := d.g_mem
  h_mem := d.h_mem
  points_disjoint := d.points_disjoint
  third_disjoint := d.third_disjoint
  points_span := d.points_span

include d in
/-- The cubic terminal exclusion holds for every two-element field presentation. -/
theorem terminal_hasNoTwoChiefFactors :
    NoncentralChiefRefinement.HasNoTwoChiefFactors (D.L₁ ⧸ pCore 2 D.L₁) := by
  obtain ⟨a⟩ := exists_pointAlignment d
  let db := binaryHypothesis a (fieldEquiv d)
  obtain ⟨b⟩ := exists_pointAlignment db
  exact CoreAssembly.Binary.terminal_hasNoTwoChiefFactors b

include d in
/-- The original natural subgroup is retained for every source field of order two. -/
theorem V_le_residual (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U) : D.V ≤ D.L₁ := by
  obtain ⟨a⟩ := exists_pointAlignment d
  let db := binaryHypothesis a (fieldEquiv d)
  obtain ⟨b⟩ := exists_pointAlignment db
  exact IntersectionAssembly.Binary.V_le_residual b hUT hILU
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.BinaryField
