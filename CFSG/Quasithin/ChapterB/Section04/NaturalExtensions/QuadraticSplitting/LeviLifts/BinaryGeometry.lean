module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.Reduction
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry.Models
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry.OriginalTransport
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry.StandardBlock
/-!
# Assembly of binary Levi coordinates

Compose the independently constructed standard block decomposition with the
transport of the original natural submodule. The elementary-root formulas,
together with the proved exchange calculation, supply the required root in the
literal seed subgroup. This discharges the root-placement premise rather than
postulating it. The resulting coordinates feed the displacement-cocycle proof
and its application to the original quotient line.

Both geometric inputs are constructed: the original-submodule transport covers
both coherent quotient markings and arbitrary recorded changes of basis, and
the standard block decomposition deletes the fixed coordinate. Their assembly
gives binary Levi coordinates whenever the defining field has degree one and
n ≥ 4. Applying the cocycle reduction proves the binary fixed-lift step of
B.4.9(1), including the exceptional SL₃(2) Levi at n = 4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1),
printed pp.92–93.
-/

@[expose] public section
open Representation Representation.BinaryOffender Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
open QuasisimpleSource BinaryGeometry
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ} (m : QuotientCoordinates d)
  {i j : Fin n} (hij : i ≠ j)

/-- Construct the requested coordinates and the seed root from the two geometric inputs. -/
noncomputable def coordinates_of_block_and_original (hn : 4 ≤ n)
    (b : BlockCoordinates n j) (o : OriginalCoordinates m j) : BinaryLeviCoordinates m hij := by
  let e : ActionEquiv (d.space.toRepresentation.comp (m.K j).subtype) (binaryModel (n - 1)) :=
    { groupEquiv := o.action.groupEquiv.trans b.action.groupEquiv
      linearEquiv := o.action.linearEquiv.trans b.action.linearEquiv
      intertwines := by
        intro g v
        change b.action.linearEquiv (o.action.linearEquiv ((d.space.toRepresentation.comp (m.K j).subtype) g v)) = _
        rw [o.action.intertwines, b.action.intertwines]
        rfl }
  refine ⟨e, ?_⟩
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < n)
  let t : m.K j := ⟨m.action.groupEquiv.symm (transvection hki 1),
    elementary_mem_Levi m hij hki hkj 1⟩
  have ht : ∃ a c : Fin (n - 1), ∃ hac : a ≠ c, e.groupEquiv t = transvection hac 1 := by
    rcases o.roots k i hki hkj hij with h | h
    · obtain ⟨a, c, hac, he⟩ := b.roots k i hki hkj hij
      refine ⟨a, c, hac, ?_⟩
      change b.action.groupEquiv (o.action.groupEquiv t) = _
      rw [show o.action.groupEquiv t = standardRoot hki hkj hij from h]
      exact he
    · obtain ⟨a, c, hac, he⟩ := b.roots i k hki.symm hij hkj
      refine ⟨a, c, hac, ?_⟩
      change b.action.groupEquiv (o.action.groupEquiv t) = _
      rw [show o.action.groupEquiv t = standardRoot hki.symm hij hkj from h]
      exact he
  obtain ⟨a, c, hac, ht⟩ := ht
  refine ⟨a, c, hac, ?_⟩
  rw [← ht, MulEquiv.symm_apply_apply]
  exact elementary_mem_seed m hij hki hkj 1

include hij in
/-- Apply the cocycle calculation using the constructed coordinate record. -/
theorem fixed_lifts_of_block_and_original (hn : 4 ≤ n) (hq : IsQuadratic ρ (m.Q j))
    (b : BlockCoordinates n j) (o : OriginalCoordinates m j) : m.FixedLifts j :=
  fixed_lifts_of_binary_coordinates m hij hn hq (coordinates_of_block_and_original m hij hn b o)

include hij in
/-- The literal quotient-line-vector consumer of the constructed fixed lifts. -/
theorem fixed_lineVector_of_block_and_original (hn : 4 ≤ n) (hq : IsQuadratic ρ (m.Q j))
    (b : BlockCoordinates n j) (o : OriginalCoordinates m j) :
    ∃ v : V, v ∈ fixedSpace ρ (m.K j) ∧ d.space.toSubmodule.mkQ v = m.lineVector j :=
  m.exists_fixed_lineVector j (fixed_lifts_of_block_and_original m hij hn hq b o)

/-- Actual binary Levi coordinates on the original natural submodule, with a unit
elementary transvection in the literal seed subgroup. This discharges the binary
clause of `SourceLeviGeometry` for either coherent quotient marking. -/
theorem nonempty_binaryLeviCoordinates (hF : F.degree = 1) (hn : 4 ≤ n) :
    Nonempty (BinaryLeviCoordinates m hij) := by
  obtain ⟨b⟩ := nonempty_blockCoordinates hn j
  obtain ⟨o⟩ := nonempty_originalCoordinates m hF hn j
  exact ⟨coordinates_of_block_and_original m hij hn b o⟩

include hij in
/-- The binary fixed-lift step of B.4.9(1), with the coordinate and seed-root
premises discharged. Quadraticity concerns the actual quotient axis group. -/
theorem fixed_lifts_binary (hF : F.degree = 1) (hn : 4 ≤ n)
    (hq : IsQuadratic ρ (m.Q j)) : m.FixedLifts j := by
  obtain ⟨b⟩ := nonempty_binaryLeviCoordinates m hij hF hn
  exact fixed_lifts_of_binary_coordinates m hij hn hq b

include hij in
/-- A Levi-fixed lift of the original quotient line vector in the binary source
family, ready for the local-complement construction. -/
theorem exists_fixed_lineVector_binary (hF : F.degree = 1) (hn : 4 ≤ n)
    (hq : IsQuadratic ρ (m.Q j)) :
    ∃ v : V, v ∈ fixedSpace ρ (m.K j) ∧ d.space.toSubmodule.mkQ v = m.lineVector j :=
  m.exists_fixed_lineVector j (fixed_lifts_binary m hij hF hn hq)

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
