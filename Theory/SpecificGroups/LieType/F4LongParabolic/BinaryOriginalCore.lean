module
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryRadical
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryLeviPerfect
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.SolvableResidual.NormalSupplement

/-!
# The original normal perfect subgroup in the binary F4 action diagnostic

Perfectness of A and two-group commutator idempotence give perfectness of
L = A join [E,A]. Conjugation by E changes an element of A by [E,A] and
preserves [E,A], so L is normal in P = E join A. Since E is solvable and
P = LE, L is precisely the solvable residual of P.

These statements concern the same original matrices as the two-core action
failure in BinaryRadical. They do not identify the simple quotient or certify
all the MS hypotheses. The literal BinaryMS.commutatorCore application is in
MS93.OriginalAction.F4OriginalCore; qt-rank-two-ms93 retains the remaining
source-hypothesis test and final C.1.34 assembly.

Source: elementary perfect-group commutator and residual facts, as used in
Aschbacher--Smith C.1.31--34, printed pp.135--137; the F4 examples of MS93,
printed p.831.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates

private theorem A_isTwoPerfect : IsPPerfect 2 A := by
  let := A_isPerfect
  intro N hN hp
  let := hN
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The radical commutator is generated again by its commutators with the Levi. -/
theorem D_idempotent : ⁅D,A⁆ = D :=
  commutator_isPPerfect_idempotent A E A_isTwoPerfect E_isPGroup A_normalizes_E

/-- The candidate original component is perfect, not only its Levi quotient. -/
theorem L_isPerfect : Group.IsPerfect L := by
  let := A_isPerfect
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (commutator_le_self L)
  apply sup_le
  · exact (commutator_eq_self (H := A)).symm.le.trans
      (commutator_mono (show A ≤ L from le_sup_left) le_sup_left)
  · exact D_idempotent.symm.le.trans
      (commutator_mono (show D ≤ L from le_sup_right) le_sup_left)

/-- The whole radical normalizes the perfect subgroup A join [E,A]. -/
theorem E_normalizes_L : E ≤ normalizer (L : Set Matˣ) := by
  apply le_normalizer_iff.mpr
  intro e he x hx
  let f := (MulAut.conj e).toMonoidHom
  have hA : A.map f ≤ L := by
    rintro _ ⟨a,ha,rfl⟩
    change e * a * e⁻¹ ∈ L
    have hc : ⁅e,a⁆ ∈ D := commutator_mem_commutator he ha
    have hh := L.mul_mem ((show D ≤ L from le_sup_right) hc)
      ((show A ≤ L from le_sup_left) ha)
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hD : D.map f ≤ D :=
    (mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_left E A he)).le
  have hm : L.map f ≤ L := by
    rw [L,Subgroup.map_sup]
    exact sup_le hA (hD.trans le_sup_right)
  exact hm (mem_map_of_mem f hx)

/-- Relative normality in the actual original matrix overgroup. -/
theorem L_normal_in_P : (L.subgroupOf P).Normal :=
  (normal_subgroupOf_iff_le_normalizer L_le_P).mpr
    (sup_le E_normalizes_L ((show A ≤ L from le_sup_left).trans L.le_normalizer))

/-- The same original subgroup is the solvable residual of P. -/
theorem L_eq_residual : (solvableResidual P).map P.subtype = L := by
  let := L_isPerfect
  let : Group.IsNilpotent E := E_isPGroup.isNilpotent
  have hgen : L ⊔ E = P := le_antisymm (sup_le L_le_P le_sup_left)
    (sup_le le_sup_right ((show A ≤ L from le_sup_left).trans le_sup_left))
  rw [← hgen]
  exact map_solvableResidual_sup_eq_of_perfect_normalized L E E_normalizes_L

end Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates
