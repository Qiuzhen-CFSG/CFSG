module

public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Basic
public import Theory.SpecificGroups.SU3.BinaryInvolutionTable
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import Theory.GroupAction.FixedResidualFixerTransport

/-!
# The full PSU₃ cases of 16.1.4 and 16.1.6

All model witnesses identify the full group with the actual projective
special unitary matrix image. A Hermitian basis change makes the form
antidiagonal while retaining the matrix field of order q² and its fixed
field of order q. Inner involutions have explicit long-root representatives;
their full centralizers lie in proper isotropic-line parabolics, which gives
the embedded residual equality. Every outer involution is conjugate to the
actual graph action, whose fixed two-residual is PSL₂(q)′.

The Sylow pointwise fixer is inner for every automorphism order. This uses
full semilinear rigidity, not reduction to an involution. For involutions,
the conjugating element is a long-root involution in the specified Sylow.

Source: Aschbacher–Smith, Notation 16.1.3 and Lemmas 16.1.4(1),(6), 16.1.6,
printed pp.1171–1172, used in §§16.4–16.5. The unitary outer involutions
are called graph in this convention. Exclusion of nonsimple central covers
is a separate multiplier obligation of the chapter assembly.
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open HermitianForm.BinaryInvolutionTable
open HermitianForm.OddPrimeSylow.NormalizedOuter

variable {L : Type*} [Group L]

/-- Construct standard coordinates from the genuine full-group source witness.
The Hermitian comparison and the fixed-field cardinality are discharged. -/
theorem unitaryThree_standard_model {n : ℕ} (hn : 0 < n)
    (hL : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      ∃ _hJ : J.form = !![0,0,1;0,1,0;1,0,0],
      Nat.card E = (2 ^ n) ^ 2 ∧ (∀ x, J.conj x = x ^ (2 ^ n)) ∧
      Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := hL
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨d⟩ := FormTransport.exists_projectiveEquiv J (2 ^ n) hcard hfixed
  exact ⟨E, inferInstance, inferInstance, FormTransport.standardForm J,
    rfl, hcard, hconj, hfixed, ⟨e.trans d⟩⟩

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- The inner row with actual root matrices, a proper conjugate parabolic,
and the two residuals embedded in the original full group. -/
def UnitaryThreeInnerRow (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (r : MulAut L) : Prop :=
  ∃ (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (IsotropicPoint J))
    (p : IsotropicPoint J),
    (∀ (g : ProjectiveSpecialUnitaryMatrixGroup J) (z : IsotropicPoint J)
      (M : J.specialSubgroup), Matrix.ProjGenLinGroup.mk M.val = g.val →
      (rho g z).val = (Matrix.GeneralLinearGroup.toLin M.val).toLinearEquiv • z.val) ∧
    rootParabolic J hJ = (MulAction.stabilizer (Equiv.Perm (IsotropicPoint J)) p).comap rho ∧
  ∃ (x g : ProjectiveSpecialUnitaryMatrixGroup J) (z : hermitianUnipotentCoord J),
    orderOf x = 2 ∧ MulAut.congr e r = MulAut.conj x ∧
    z.val.1 = 0 ∧ MulAut.conj g x = Coverage.root J hJ z ∧
    let P := ((rootParabolic J hJ).comap (MulAut.conj g).toMonoidHom).comap e.toMonoidHom
    P ≠ ⊤ ∧ r.fixedSubgroup ≤ P ∧
      fixedTwoResidual L r =
        ((pResidual 2 (r.fixedSubgroup.subgroupOf P)).map
          (r.fixedSubgroup.subgroupOf P).subtype).map P.subtype

/-- The graph row uses conjugacy to the literal entrywise Hermitian action
and the derived fixed-field PSL₂ endpoint of the printed statement. -/
def UnitaryThreeGraphRow (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (r : MulAut L) : Prop :=
  ∃ c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
    MulAut.congr c (J.projectiveGraphAut hJ) = MulAut.congr e r ∧
    fixedTwoResidual L r = r.fixedSubgroup ∧
    Nonempty (fixedTwoResidual L r ≃*
      commutator (PSL2MatrixGroup (FixedBy.subfield E J.conj)))

variable [Finite L]

omit [Finite L] in
/-- The inner alternative is proved for every full model isomorphism. -/
theorem unitaryThree_inner_involution_model {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (r : MulAut L) (hr : orderOf r = 2) (hi : ∃ y : L, r = MulAut.conj y) :
    UnitaryThreeInnerRow J hJ e r := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨rho, p, hnat, hpar⟩ := rootParabolic_isotropic_stabilizer J hJ
    (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : n ≠ 0)) hcard hfixed
  obtain ⟨x, hx, he, hC⟩ := MulAut.inner_involution_representative
    (HermitianForm.BinaryInvolutionTable.center_eq_bot J hn hcard hfixed)
    (MulAut.congr e r) (by rw [MulEquiv.orderOf_eq, hr])
    ((MulAut.congr_inner_iff e r).mpr hi)
  obtain ⟨g, z, hz, hg, hCP, hP⟩ := involution_root_geometry J hJ hn hcard hfixed x hx
  let P := ((rootParabolic J hJ).comap (MulAut.conj g).toMonoidHom).comap e.toMonoidHom
  have hfix : r.fixedSubgroup ≤ P := by
    intro y hy
    apply hCP
    rw [← hC, MulAut.mem_fixedSubgroup]
    change e (r (e.symm (e y))) = e y
    rw [e.symm_apply_apply, (MulAut.mem_fixedSubgroup _ _).mp hy]
  refine ⟨rho, p, hnat, hpar, x, g, z, hx, he, hz, hg, ?_, hfix, ?_⟩
  · intro h
    apply hP
    apply top_unique
    intro y _
    obtain ⟨w, rfl⟩ := e.surjective y
    have hw : w ∈ P := by
      change P = ⊤ at h
      rw [h]
      trivial
    exact hw
  · exact MulAut.embeddedFixedResidual_eq_local 2 r P hfix

/-- The outer alternative covers arbitrary involutory automorphisms.
The residual is transported through the literal full-group isomorphism. -/
theorem unitaryThree_outer_involution_model {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (r : MulAut L) (hr : orderOf r = 2) (ho : ¬ ∃ y : L, r = MulAut.conj y) :
    UnitaryThreeGraphRow J hJ e r := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hr2 : r ^ 2 = 1 := hr ▸ pow_orderOf_eq_one r
  obtain ⟨c, hc, heq, ⟨d⟩⟩ := outer_involution_geometry J hJ hn hcard hfixed
    (MulAut.congr e r) (by rw [← map_pow, hr2, map_one])
    (fun hi => ho ((MulAut.congr_inner_iff e r).mp hi))
  have hm := MulAut.map_embeddedFixedResidual 2 e r
  let er : fixedTwoResidual L r ≃* MulAut.embeddedFixedResidual 2 (MulAut.congr e r) :=
    (e.subgroupMap (fixedTwoResidual L r)).trans (MulEquiv.subgroupCongr hm)
  have he : fixedTwoResidual L r = r.fixedSubgroup := by
    apply le_antisymm (map_subtype_le _)
    intro y hy
    have hy' : e y ∈ (MulAut.congr e r).fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup]
      change e (r (e.symm (e y))) = e y
      rw [e.symm_apply_apply, (MulAut.mem_fixedSubgroup _ _).mp hy]
    rw [← heq, ← hm] at hy'
    obtain ⟨w, hw, hew⟩ := hy'
    exact e.injective hew ▸ hw
  exact ⟨c, hc, he, ⟨er.trans d⟩⟩

/-- Full Sylow-pointwise innerness, without an order restriction. -/
theorem unitaryThree_sylow_fixing_inner_model {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 L) (r : MulAut L) (hfix : ∀ x ∈ P, r x = x) :
    ∃ x ∈ P, r = MulAut.conj x := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hq : 2 < 2 ^ n := by
    change 2 ^ 1 < 2 ^ n
    exact Nat.pow_lt_pow_right (by decide) (by omega : 1 < n)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ n) hq hcard hfixed
  exact MulAut.fixing_sylow_inner_of_equiv e
    (HermitianForm.SylowPointwiseInner.fixing_sylow_eq_mem_conj J hn hcard hconj) P r hfix

/-- For an involutory Sylow fixer, the inner representative is a genuine
long-root involution and lies in the center of the specified Sylow subgroup. -/
theorem unitaryThree_sylow_fixing_longRoot_model {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 L) (r : MulAut L) (hr : orderOf r = 2)
    (hfix : ∀ x ∈ P, r x = x) :
    ∃ y ∈ P, r = MulAut.conj y ∧ IsLongRootInvolution J hJ (e y) ∧
      ∀ z ∈ P, Commute y z := by
  obtain ⟨y, hy, he⟩ := unitaryThree_sylow_fixing_inner_model J hn hcard hconj e P r hfix
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hey : orderOf (e y) = 2 := by
    rw [← MulAut.conj_orderOf_of_center_eq_bot
      (HermitianForm.BinaryInvolutionTable.center_eq_bot J hn hcard hfixed),
      ← MulAut.congr_conj, ← he, MulEquiv.orderOf_eq, hr]
  refine ⟨y, hy, he, involution_isLongRoot J hJ hn hcard hfixed (e y) hey, ?_⟩
  intro z hz
  have hf := hfix z hz
  rw [he] at hf
  exact mul_inv_eq_iff_eq_mul.mp hf

end CFSG.Quasithin.Chapter16.LiePreliminaries

namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.BinaryInvolutionTable
variable {L : Type*} [Group L] [Finite L]

/-- The complete PSU₃ portion of 16.1.4: the root/parabolic row or the graph
row, from the full source model and no proper-K or covering-group premise. -/
theorem unitaryThree_involution_table {n : ℕ} (hn : 2 ≤ n)
    (hL : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (r : MulAut L) (hr : orderOf r = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      ∃ hJ : J.form = !![0,0,1;0,1,0;1,0,0],
      Nat.card E = (2 ^ n) ^ 2 ∧ (∀ x, J.conj x = x ^ (2 ^ n)) ∧
      Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      ∃ e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        UnitaryThreeInnerRow J hJ e r ∨ UnitaryThreeGraphRow J hJ e r := by
  obtain ⟨E, _, _, J, hJ, hcard, hconj, hfixed, ⟨e⟩⟩ :=
    unitaryThree_standard_model (by omega : 0 < n) hL
  refine ⟨E, inferInstance, inferInstance, J, hJ, hcard, hconj, hfixed, e, ?_⟩
  by_cases hi : ∃ y : L, r = MulAut.conj y
  · exact Or.inl (unitaryThree_inner_involution_model J hJ hn hcard hfixed e r hr hi)
  · exact Or.inr (unitaryThree_outer_involution_model J hJ hn hcard hfixed e r hr hi)

/-- The actual fixed residual of every outer involution is PSL₂(2ⁿ)′.
This is the unitary endpoint used by the comparisons in §§16.4–16.5. -/
theorem unitaryThree_outer_fixed_residual {n : ℕ} (hn : 2 ≤ n)
    (hL : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (r : MulAut L) (hr : orderOf r = 2) (ho : ¬ ∃ y : L, r = MulAut.conj y) :
    fixedTwoResidual L r = r.fixedSubgroup ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (fixedTwoResidual L r ≃* commutator (PSL2MatrixGroup F)) := by
  obtain ⟨E, _, _, J, hJ, hcard, _, hfixed, ⟨e⟩⟩ :=
    unitaryThree_standard_model (by omega : 0 < n) hL
  obtain ⟨_, _, he, hd⟩ := unitaryThree_outer_involution_model J hJ hn hcard hfixed e r hr ho
  exact ⟨he, FixedBy.subfield E J.conj, inferInstance, inferInstance, hfixed, hd⟩

/-- The PSU₃ case of 16.1.6, proved even without restricting the order of r. -/
theorem unitaryThree_sylow_fixing_inner {n : ℕ} (hn : 2 ≤ n)
    (hL : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (P : Sylow 2 L) (r : MulAut L) (hfix : ∀ x ∈ P, r x = x) :
    ∃ x ∈ P, r = MulAut.conj x := by
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := hL
  exact unitaryThree_sylow_fixing_inner_model J hn hcard hconj e P r hfix

/-- The long-root refinement of 16.1.6 on an actual full PSU₃ model.
The representative stays in the original Sylow subgroup and centralizes it. -/
theorem unitaryThree_sylow_fixing_longRoot {n : ℕ} (hn : 2 ≤ n)
    (hL : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (P : Sylow 2 L) (r : MulAut L) (hr : orderOf r = 2)
    (hfix : ∀ x ∈ P, r x = x) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      ∃ hJ : J.form = !![0,0,1;0,1,0;1,0,0],
      Nat.card E = (2 ^ n) ^ 2 ∧ (∀ x, J.conj x = x ^ (2 ^ n)) ∧
      Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      ∃ e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ∃ y ∈ P, r = MulAut.conj y ∧ IsLongRootInvolution J hJ (e y) ∧
          ∀ z ∈ P, Commute y z := by
  obtain ⟨E, _, _, J, hJ, hcard, hconj, hfixed, ⟨e⟩⟩ :=
    unitaryThree_standard_model (by omega : 0 < n) hL
  exact ⟨E, inferInstance, inferInstance, J, hJ, hcard, hconj, hfixed, e,
    unitaryThree_sylow_fixing_longRoot_model J hJ hn hcard hconj e P r hr hfix⟩
end CFSG.Quasithin.Chapter16.LiePreliminaries
