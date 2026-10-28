module

public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.LocalReduction

/-!
# The cubic defect from two orthogonal ternary roots

The B and D positive root generators commute in the octonion model. Their
lift commutator therefore lies in every central-extension kernel. It is
independent of the choices of root lifts, and its cube is one because the
additive root lifts have exponent three. These statements do not assert
that this element is nonidentity.

If all positive-root multiplication errors belong to this cyclic subgroup,
the existing local-lift construction and transfer exclude divisibility by
nine in a finite perfect central kernel. That containment remains an
explicit hypothesis and is the outstanding root-relation calculation.

Source: the orthogonal-root calculation in GLS3 §6.3, printed pp.319–320
(PDF pp.336–337), in support of Aschbacher–Smith I.1.4(2), printed p.408.
The B/D coordinate convention is fixed by the attributed ATLAS port
through `TernaryLocals.Involution.Generators` (LICENSES/ATLAS.txt).
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree
open PerfectCentralCovering MultiplierOrdinary
open scoped commutatorElement

variable {E : Type*} [Group E] {f : E →* Model (ZMod 3)}

/-- The commutator of the lifted B(1) and D(1) root generators. -/
def orthogonalDefect (L : RootSections f) : E :=
  ⁅L.root 1 (.ofAdd 1), L.root 3 (.ofAdd 1)⁆

/-- The base roots commute, so their lift commutator is in the literal kernel. -/
theorem orthogonalDefect_mem_kernel (L : RootSections f) : orthogonalDefect L ∈ f.ker := by
  rw [MonoidHom.mem_ker, orthogonalDefect, map_commutatorElement]
  rw [← MonoidHom.comp_apply, L.project, ← MonoidHom.comp_apply, L.project]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact congrArg Subtype.val (TernaryLocals.Involution.root_factors_commute false false)

/-- Central changes of either root lift do not change the defect. -/
theorem orthogonalDefect_eq (hc : f.ker ≤ Subgroup.center E)
    (L M : RootSections f) : orthogonalDefect L = orthogonalDefect M := by
  apply CentralExtension.commutator_eq_of_image_eq f hc
  all_goals rw [← MonoidHom.comp_apply, L.project, ← MonoidHom.comp_apply, M.project]

/-- Additivity of the root lifts forces the central defect to have cube one. -/
theorem orthogonalDefect_cube (hc : f.ker ≤ Subgroup.center E)
    (L : RootSections f) : orthogonalDefect L ^ 3 = 1 := by
  let x := L.root 1 (.ofAdd 1)
  let y := L.root 3 (.ofAdd 1)
  have hcx : Commute ⁅x, y⁆ x :=
    (Subgroup.mem_center_iff.mp (hc (orthogonalDefect_mem_kernel L)) x).symm
  have hpow (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul,
        hcx.symm.pow_left n |>.eq, mul_inv_cancel_right, ih, ← pow_succ']
  have hx3 : x ^ 3 = 1 := by
    dsimp [x]
    rw [← map_pow]
    have h3 : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide
    rw [h3, map_one]
  change ⁅x, y⁆ ^ 3 = 1
  rw [← hpow, hx3]
  simp

/-- Only the root-error containment remains; kernel membership and the
cubic exponent of the indicated commutator are discharged here. -/
theorem not_nine_dvd_kernel_of_orthogonal_defect [Finite E]
    (c : Cover E (Model (ZMod 3))) (L : RootSections c.toMonoidHom)
    (hL : L.ProductCompatibleModulo (Subgroup.zpowers (orthogonalDefect L))) :
    ¬ 9 ∣ Nat.card c.toMonoidHom.ker :=
  not_nine_dvd_kernel_of_cubic_root_defect c L _ (orthogonalDefect_mem_kernel L)
    (orthogonalDefect_cube c.ker_le_center L) hL

end Atlas.G2.FiniteCover.MultiplierThree
end
