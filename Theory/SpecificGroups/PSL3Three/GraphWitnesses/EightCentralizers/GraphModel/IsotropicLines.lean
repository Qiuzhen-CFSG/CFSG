module

public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.FixedMonomial
public import Theory.SpecificGroups.PSL3Three.CandidateOrders
public import Mathlib.GroupTheory.GroupAction.SubMulAction
/-!
# Four isotropic lines and the graph-fixed S₄

The determinant-one monomial matrices act on the four pairs of opposite
nonzero isotropic vectors in the three-dimensional space over `ZMod 3`.
The action is faithful: among the signed-column matrices of determinant one,
only the identity preserves each of these pairs. Its order is 24, so the
resulting map to the symmetric group on four letters is onto.

The finite certificate tests only the 216 signed-column choices; group laws
come from the existing matrix action. The final equivalence is transported
through the literal injective SL-to-PSL projection and the proved equality
between the graph-fixed subgroup and the monomial subgroup. It is used by
the full graph-centralizer product in `EightCentralizers.GraphModel`.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10.
-/

public section

open scoped Pointwise
namespace Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
private abbrev Vec := Fin 3 → ZMod 3
private def signedVector : Fin 6 → Vec :=
  ![![1, 0, 0], ![2, 0, 0], ![0, 1, 0], ![0, 2, 0], ![0, 0, 1], ![0, 0, 2]]
private def signedMatrix (w : Fin 3 → Fin 6) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun i j => signedVector (w j) i
private def lineVector : Fin 4 → Vec :=
  ![![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2]]
private def line (i : Fin 4) : Set Vec := {lineVector i, -lineVector i}
private theorem signedVector_surjective : ∀ v : Vec,
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 → ∃ i, signedVector i = v := by decide
private theorem signedMatrix_spec : ∀ w : Fin 3 → Fin 6,
    (signedMatrix w).det = 1 →
    (∀ i, ∃ j, (signedMatrix w).mulVec (lineVector i) = lineVector j ∨
      (signedMatrix w).mulVec (lineVector i) = -lineVector j) ∧
    ((∀ i, (signedMatrix w).mulVec (lineVector i) = lineVector i ∨
      (signedMatrix w).mulVec (lineVector i) = -lineVector i) → signedMatrix w = 1) := by
  decide +kernel

private theorem exists_signedMatrix (g : monomialSL) :
    ∃ w, signedMatrix w = g.val.val := by
  have hc := (mem_monomialSL_iff_columns g.val).mp g.property
  have he (j : Fin 3) : ∃ i, signedVector i = fun k => g.val.val k j :=
    signedVector_surjective _ (hc j)
  choose w hw using he
  exact ⟨w, by ext i j; exact congrFun (hw j) i⟩

private theorem line_injective : Function.Injective line := by
  have h : ∀ i j : Fin 4, lineVector i = lineVector j ∨
      lineVector i = -lineVector j → i = j := by decide
  intro i j hij
  apply h i j
  have hi : lineVector i ∈ line i := by simp [line]
  rw [hij] at hi
  simpa [line] using hi

private theorem smul_line (g : monomialSL) (i : Fin 4) :
    (∃ j, (g : SL) • line i = line j) := by
  obtain ⟨w, hw⟩ := exists_signedMatrix g
  have hd : (signedMatrix w).det = 1 := hw ▸ g.val.property
  obtain ⟨j, hj | hj⟩ := (signedMatrix_spec w hd).1 i
  · refine ⟨j, ?_⟩
    have he : (g : SL) • lineVector i = lineVector j := by
      change g.val.val.mulVec (lineVector i) = _
      rwa [← hw]
    simp [line, Set.smul_set_insert, Set.smul_set_singleton, smul_neg, he]
  · refine ⟨j, ?_⟩
    have he : (g : SL) • lineVector i = -lineVector j := by
      change g.val.val.mulVec (lineVector i) = _
      rwa [← hw]
    simp [line, Set.smul_set_insert, Set.smul_set_singleton, smul_neg, he,
      Set.pair_comm]

private def lines : SubMulAction monomialSL (Set Vec) where
  carrier := Set.range line
  smul_mem' g _ hs := by
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨j, hj⟩ := smul_line g i
    exact ⟨j, hj.symm⟩

private def lineAction : monomialSL →* Equiv.Perm lines :=
  MulAction.toPermHom monomialSL lines

private noncomputable def linesEquiv : Fin 4 ≃ lines :=
  Equiv.ofInjective line line_injective

private theorem lineAction_injective : Function.Injective lineAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  have he : lineAction g = 1 := hg
  obtain ⟨w, hw⟩ := exists_signedMatrix g
  have hd : (signedMatrix w).det = 1 := hw ▸ g.val.property
  have hid : signedMatrix w = 1 := (signedMatrix_spec w hd).2 (by
    intro i
    have ha := congrArg (fun p : Equiv.Perm lines => p ⟨line i, ⟨i, rfl⟩⟩) he
    have hs : (g : SL) • line i = line i := congrArg Subtype.val ha
    have hv : (g : SL) • lineVector i ∈ line i := by
      rw [← hs]
      exact Set.smul_mem_smul_set (by simp [line])
    have hv' : g.val.val.mulVec (lineVector i) = lineVector i ∨
        g.val.val.mulVec (lineVector i) = -lineVector i := by
      simpa only [line, Set.mem_insert_iff, Set.mem_singleton_iff,
        SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using hv
    rwa [hw])
  exact Subtype.ext (Subtype.ext (hw.symm.trans hid))

private noncomputable def monomialPermHom : monomialSL →* Equiv.Perm (Fin 4) :=
  linesEquiv.symm.permCongrHom.toMonoidHom.comp lineAction

/-- The actual signed monomial group acts as the full symmetric group on the four lines. -/
noncomputable def monomialEquivSymmetricFour : monomialSL ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective monomialPermHom
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨
      linesEquiv.symm.permCongrHom.injective.comp lineAction_injective,
      by rw [card_monomialSL, Nat.card_eq_fintype_card]; decide⟩)

/-- The fixed group of inverse transpose in the canonical PSL₃(3) is S₄. -/
noncomputable def graphFixedEquivSymmetricFour :
    (Matrix.PSL3.OuterSolvable.graph (ZMod 3)).fixedSubgroup ≃* Equiv.Perm (Fin 4) :=
  ((MulEquiv.subgroupCongr graph_fixed_eq_monomial).trans
    (monomialSL.equivMapOfInjective project project_injective).symm).trans
      monomialEquivSymmetricFour
end Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
