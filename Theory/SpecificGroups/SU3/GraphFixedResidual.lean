module

public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.GroupAction.InnerInvolutionGeometry
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The embedded two-residual of the binary unitary graph action

The actual fixed subgroup of the graph action is PSL₂ over the Hermitian
fixed field. For fixed-field order at least four it is perfect, hence has
no nontrivial two-group quotient. Its embedded two-residual is therefore
the full fixed subgroup, with no change in the projective embedding.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.4(6) and 16.4.9(1), printed pp.1171 and 1189 of the 1 March 2004
combined manuscript. This computes the residual, not its pointwise fixer.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
variable (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The full graph-fixed subgroup is two-perfect throughout the simple PSU₃ range. -/
theorem graph_fixed_twoResidual_eq_top {n : ℕ} (hn : 2 ≤ n)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    pResidual 2 (projectiveGraphAut J hJ).fixedSubgroup = ⊤ := by
  let K := FixedBy.subfield E J.conj
  have hK : 4 ≤ Nat.card K := by
    change 4 ≤ Nat.card {x : E // J.conj x = x}
    rw [hfixed]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have hu : 1 < Nat.card Kˣ := by
    rw [Nat.card_units]
    omega
  let : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨u, hu⟩ := exists_ne (1 : Kˣ)
  have hcomm : commutator (PSL2MatrixGroup K) = ⊤ :=
    SL2Simple.PSL_commutator_eq_top ⟨(u : K), u.ne_zero, fun hs =>
      hu (Units.val_eq_one.mp (CharTwo.sq_injective (by simpa using hs)))⟩
  let : Group.IsPerfect (PSL2MatrixGroup K) := ⟨hcomm⟩
  let e := projectiveGraphFixedEquiv J hJ
  let : Group.IsPerfect (projectiveGraphAut J hJ).fixedSubgroup :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Finite (projectiveGraphAut J hJ).fixedSubgroup :=
    Finite.of_equiv (PSL2MatrixGroup K) e.symm.toEquiv
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN hP
  let := hN
  have : Subsingleton ((projectiveGraphAut J hJ).fixedSubgroup ⧸ N) := by
    by_contra! hnontrivial
    exact Group.IsPerfect.not_isNilpotent _ hP.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
/-- The equality is inside the actual PSU₃ carrier, retaining its embedding. -/
theorem graph_embeddedFixedResidual_eq_fixed {n : ℕ} (hn : 2 ≤ n)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    MulAut.embeddedFixedResidual 2 (projectiveGraphAut J hJ) =
      (projectiveGraphAut J hJ).fixedSubgroup := by
  rw [MulAut.embeddedFixedResidual, graph_fixed_twoResidual_eq_top J hJ hn hfixed,
    ← MonoidHom.range_eq_map, range_subtype]

end BenderSuzuki.MatrixGroups.HermitianForm
