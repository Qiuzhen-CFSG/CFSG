module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ExtensionModels.Transport
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.ScalarKernel

/-!
# The actual split projective extensions

PGL3 is the quotient GL3/Z(GL3), and PGU3 is the image of the unitary
subgroup under GL3 → PGL3. The kernels of their conjugation actions on
PSL3 and PSU3 are exactly these scalar kernels. Consequently the first
isomorphism theorem identifies the literal extension groups with their
conjugation images. The transport module then identifies the component
and constructs compatible quotient coordinates for the local cubic actor.

For the unitary case the standard antidiagonal Hermitian form is retained
on the same field of order q squared. Its q-Frobenius is nontrivial by the
order of the field's multiplicative group. No arbitrary unitary involution
or new field parameter is substituted. Local noncontainment is an explicit
premise here; its source proof is still needed in the rank-one-Yplus case.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18(2),
printed pp.51--52, and 15.3.37 and 15.3.43, pp.1135 and 1139. The matrix
conventions are GLS3, Section 2.7. SL3 perfectness is reused from the
attributed ATLAS port in ExceptionalIsomorphisms.Elementary; its license
and attribution are retained in that imported module.
-/

public section

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels

variable {F : Type} [Field F]

private theorem linearConj_kernel : (PSL3.OuterSolvable.linearConj F).ker = center (GL (Fin 3) F) := by
  open PSL3.OuterSolvable in
  have hinj : Function.Injective (centerAction F) := by
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    have he : centerAction F = Subgroup.quotientAut (center SL(3,F)) := by
      ext a x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) x
      rw [Subgroup.quotientAut_apply_mk]
      rfl
    rw [he]
    exact MulAut.quotient_center_injective
  ext g
  constructor
  · intro hg
    have hs : PSL3.OuterSolvable.linearConjSL F g = 1 :=
      hinj (hg.trans (map_one _).symm)
    have hc (x : SL(3,F)) : g * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * g := by
      have he := congrArg SpecialLinearGroup.toGL (DFunLike.congr_fun hs x)
      rw [PSL3.OuterSolvable.linearConjSL_toGL] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    exact (congrArg Units.val (hc ⟨t.toMatrix, by simp⟩)).symm
  · intro hg
    change PSL3.OuterSolvable.linearConj F g = 1
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) z
    change PSL3.OuterSolvable.linearConj F g (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [PSL3.OuterSolvable.linearConj_mk]
    change QuotientGroup.mk (PSL3.OuterSolvable.linearConjSL F g x) = QuotientGroup.mk x
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [PSL3.OuterSolvable.linearConjSL_toGL, ← mem_center_iff.mp hg, mul_inv_cancel_right]

private noncomputable def pglEquiv : PGL(Fin 3,F) ≃* (PSL3.OuterSolvable.linearConj F).range :=
  (QuotientGroup.quotientMulEquivOfEq linearConj_kernel.symm).trans
    (QuotientGroup.quotientKerEquivRange (PSL3.OuterSolvable.linearConj F))

private noncomputable def pguEquiv [CharP F 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hconj : ∃ t : F, J.conj t ≠ t) :
    J.unitarySubgroup.map ProjGenLinGroup.mk ≃* J.unitaryConjHom.range := by
  let f := ProjGenLinGroup.mk.subgroupMap J.unitarySubgroup
  have hk : f.ker = J.unitaryConjHom.ker := by
    ext u
    change f u = 1 ↔ J.unitaryConjHom u = 1
    constructor
    · intro hu
      have hq := congrArg Subtype.val hu
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [J.unitaryConjHom_apply, J.unitaryConj_apply_val]
      change ProjGenLinGroup.mk u.val = 1 at hq
      rw [hq, one_mul, inv_one, mul_one, MulAut.one_apply]
    · intro hu
      apply Subtype.ext
      apply ProjGenLinGroup.mk_eq_one.mpr
      apply J.projective_centralizer_scalar hJ hconj
      intro x
      apply mul_inv_eq_iff_eq_mul.mp
      simpa only [J.unitaryConjHom_apply, J.unitaryConj_apply_val, MulAut.one_apply] using
        congrArg Subtype.val (MulEquiv.congr_fun hu x)
  exact (QuotientGroup.quotientKerEquivOfSurjective f
    (ProjGenLinGroup.mk.subgroupMap_surjective J.unitarySubgroup)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivRange J.unitaryConjHom))

private theorem conj_nontrivial [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {q : ℕ} (hq : 1 < q) (hcard : Nat.card F = q ^ 2)
    (hfrob : ∀ x, J.conj x = x ^ q) : ∃ t : F, J.conj t ≠ t := by
  by_contra! h
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hp : u ^ (q - 1) = 1 := by
    apply mul_right_cancel (b := u)
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), one_mul]
    exact Units.ext ((hfrob u).symm.trans (h u))
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hu, Nat.card_units, hcard] at hd
  have hb := Nat.le_of_dvd (by omega : 0 < q - 1) hd
  have hh : q < q ^ 2 := by nlinarith
  omega

variable {G : Type*} [Group G] [Finite G]

/-- An unmarked isomorphism with the literal PGL3 extension gives an actual
diagonal actor in Yplus when local noncontainment is known. -/
theorem linear_actor_of_pgl {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L)
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    [Finite F] {q : ℕ} (hcard : Nat.card F = q)
    (e : Residual I ≃* PGL(Fin 3,F))
    (model : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    ∃ y ∈ Yplus, orderOf y = 3 ∧ y ∉ L ∧ LinearDiagonalOnTwoQuotient L y q :=
  linear_actor_of_not_le hθ hnot hLI hcomp hodd hrankL hrankI hindex hcard
    (e.trans pglEquiv) model

/-- The same deduction from the literal standard PGU3 image preserves q, q squared,
and the q-Frobenius. Compatibility of component coordinates is proved, not assumed. -/
theorem unitary_actor_of_pgu {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L)
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hfrob : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : Residual I ≃* J.unitarySubgroup.map ProjGenLinGroup.mk)
    (model : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ y ∈ Yplus, orderOf y = 3 ∧ y ∉ L ∧ UnitaryDiagonalOnTwoQuotient L y (2 ^ n) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [pow_mul, ← Nat.card_eq_fintype_card] using hcard)
  have hq : 1 < 2 ^ n := Nat.one_lt_pow hn.ne' (by decide)
  exact unitary_actor_of_not_le hθ hnot hLI hcomp hodd hrankL hrankI hindex J hcard hfrob
    (e.trans (pguEquiv J hJ (conj_nontrivial J hq hcard hfrob))) model

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels
