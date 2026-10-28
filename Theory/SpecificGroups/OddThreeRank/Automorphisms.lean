module

public import Theory.SpecificGroups.OddThreeRank
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.SU3.CyclicNormalOuter.OddCoverage
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.MatrixCocycle
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Automorphism two-rank for odd-prime groups of degree three

The projective inner groups have two-rank at most two. For PSL₃ over a
prime field, standard automorphism coverage gives two cosets of the diagonal
outer subgroup, whose elements have cube one. Thus an elementary two-subgroup
of the outer group has at most two elements. For PSU₃, arbitrary-automorphism
coverage gives a cyclic quotient above the same odd diagonal contribution.
The kernel/image rank inequality therefore bounds the full automorphism rank
by three.

For the special groups, perfectness makes descent through the whole center
faithful. The unitary scalar-centralizer calculation identifies that center
with the kernel of the actual special-to-projective map. Quasisimplicity is
inherited where needed for unitary simplicity; no rank, representation-degree,
or automorphism-coverage hypothesis is assumed in the resulting bounds.

Source: Aschbacher–Smith, G.7.3(1), printed p.348 (PDF p.359);
GLS3, Theorem 2.5.12 and §2.7 for the standard automorphism coverage.
-/

noncomputable section
public section

open Subgroup Matrix
open scoped MatrixGroups
open Theory.GroupTheory BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport

namespace Theory.SpecificGroups.OddThreeRank

private theorem standard_psu_center_eq_bot {E : Type*} [Field E]
    (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (h2 : (2 : E) ≠ 0) (hconj : ∃ t : E, J.conj t ≠ t) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  apply mem_bot.mpr
  apply Subtype.ext
  rw [J.specialToProjective_apply_val]
  apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
  apply BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent.projective_centralizer_scalar J hJ h2 hconj
  intro b
  have he := congrArg Subtype.val ((mem_center_iff.mp hx b).symm)
  apply (commute_iff_eq _ _).mpr
  simpa only [Subgroup.coe_mul, J.specialToProjective_apply_val] using he

private theorem standard_psu_automorphism_two_rank_le_three
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card E = p ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ p)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3 := by
  have h2 := two_ne_zero_of_odd_card ho hcard
  have hnonfixed : ∃ t : E, J.conj t ≠ t := by
    by_contra! h
    have hc : Nat.card {x : E // J.conj x = x} = Nat.card E :=
      Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [hcard, hfixed] at hc
    have hp2 : 1 < p := hp.one_lt
    nlinarith
  have hcenter := standard_psu_center_eq_bot J hJ h2 hnonfixed
  let e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
      MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hcenter)
  have hi : primeRank 2 (MulAut.innerSubgroup
      (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 2 := by
    exact (primeRank_equiv 2 e).symm.le.trans
      (psu3_primeRank_two_le J hp ho hcard hconj)
  have hout := BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.outer_two_rank_le_of_coverage
    J hJ hcoverage
  have h := primeRank_le_ker_add (p := 2)
    (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
  rw [QuotientGroup.ker_mk'] at h
  have hout' : primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J) ⧸
      MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 1 := hout
  exact h.trans (Nat.add_le_add hi hout')

/-- Semilinear coverage bounds the full automorphism group of the simple
projective unitary model over every odd prime, for any Hermitian form. -/
theorem psu3_automorphism_two_rank_le_three
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card E = p ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ p) :
    primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3 := by
  let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let _ : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    simpa only [pow_one] using
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hconj))
  obtain ⟨e⟩ := exists_projectiveEquiv J p hcard hfixed
  let K := standardForm J
  let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup K) :=
    Finite.of_equiv _ e.toEquiv
  let _ : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup K) := e.symm.isSimpleGroup
  rw [primeRank_equiv 2 (MulAut.congr e)]
  apply standard_psu_automorphism_two_rank_le_three K rfl hp ho hcard
    (by simpa only [K, standardForm_conj] using hconj) hfixed
  exact BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.semilinear_coverage_odd K rfl hp ho hcard hfixed

private def oddRankInverseTransposeGL {F : Type*} [Field F] :
    GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

private theorem oddRankGraphSL_toGL {F : Type*} [Field F] (x : SL(3,F)) :
    SpecialLinearGroup.toGL (Matrix.PSL3.OuterSolvable.graphSL F x) =
      oddRankInverseTransposeGL (SpecialLinearGroup.toGL x) := by
  apply Units.ext
  exact (Matrix.adjugate_transpose x.val).symm

private theorem oddRankGraphLinearConj {F : Type*} [Field F]
    (g : GL (Fin 3) F) :
    Matrix.PSL3.OuterSolvable.graph F *
        Matrix.PSL3.OuterSolvable.linearConj F g =
      Matrix.PSL3.OuterSolvable.linearConj F (oddRankInverseTransposeGL g) *
        Matrix.PSL3.OuterSolvable.graph F := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) y
  change QuotientGroup.mk
      (Matrix.PSL3.OuterSolvable.graphSL F
        (Matrix.PSL3.OuterSolvable.linearConjSL F g x)) =
    QuotientGroup.mk
      (Matrix.PSL3.OuterSolvable.linearConjSL F (oddRankInverseTransposeGL g)
        (Matrix.PSL3.OuterSolvable.graphSL F x))
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [oddRankGraphSL_toGL,
    Matrix.PSL3.OuterSolvable.linearConjSL_toGL, map_mul, map_mul, map_inv,
    Matrix.PSL3.OuterSolvable.linearConjSL_toGL, oddRankGraphSL_toGL]

private theorem psl3_outer_two_rank_le_one {F : Type*} [Field F] [Finite F]
    [IsSimpleGroup PSL(3,F)] (hns : ¬ Group.IsSolvable PSL(3,F))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) :
    primeRank 2 (MulAut.Outer PSL(3,F)) ≤ 1 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  let C := Matrix.PSL3.OuterSolvable.innerDiagonalOuter F
  let t : MulAut.Outer PSL(3,F) := q (Matrix.PSL3.OuterSolvable.graph F)
  have hfield (σ : F ≃+* F) : σ = 1 :=
    FiniteField.ringAut_eq_one_of_card_prime hp hF σ
  have hstandard := Matrix.PSL3.OuterSolvable.standard_eq_top_of_odd_prime_card
    F hns hp ho hF
  have hcase (z : MulAut.Outer PSL(3,F)) :
      z ∈ C ∨ ∃ g : GL (Fin 3) F,
        z = q (Matrix.PSL3.OuterSolvable.linearConj F g) * t := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (MulAut.innerSubgroup PSL(3,F)) z
    obtain ⟨g, σ, ha⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization F
      (by intro σ m; rw [hfield σ, map_one, one_mul, mul_one]; rfl)
      (fun g => ⟨oddRankInverseTransposeGL g, oddRankGraphLinearConj g⟩)
      (by intro σ; rw [hfield σ, map_one]; exact Commute.one_left _)
      a (hstandard ▸ mem_top a)
    simp only [hfield σ, map_one, mul_one] at ha
    rcases ha with ha | ha
    · left
      refine ⟨g, ?_⟩
      exact ha ▸ rfl
    · right
      refine ⟨g, ?_⟩
      rw [ha, map_mul]

  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let _ : IsElementaryAbelian 2 A := hA
  have hcube (x : C) : x ^ 3 = 1 := by
    obtain ⟨g, hg⟩ := x.property
    apply Subtype.ext
    change (x : MulAut.Outer PSL(3,F)) ^ 3 = 1
    rw [← hg]
    change (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
      (Matrix.PSL3.OuterSolvable.linearConj F g)) ^ 3 = 1
    obtain ⟨u, hu⟩ := Matrix.PSL3.CartanActions.ResidualInner.linearConj_cube_inner g
    rw [← map_pow, ← hu]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
  have hone_of_mem (x : MulAut.Outer PSL(3,F)) (hx : x ∈ C)
      (hx2 : x ^ 2 = 1) : x = 1 := by
    have hx3 := congrArg Subtype.val (hcube ⟨x, hx⟩)
    change x ^ 3 = 1 at hx3
    simpa only [show (3 : ℕ) = 2 + 1 by decide, pow_succ, hx2, one_mul] using hx3
  have hmul_mem (x y : MulAut.Outer PSL(3,F))
      (hx : ∃ g : GL (Fin 3) F,
        x = q (Matrix.PSL3.OuterSolvable.linearConj F g) * t)
      (hy : ∃ g : GL (Fin 3) F,
        y = q (Matrix.PSL3.OuterSolvable.linearConj F g) * t) : x * y ∈ C := by
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨h, rfl⟩ := hy
    refine ⟨g * oddRankInverseTransposeGL h, ?_⟩
    change Matrix.PSL3.OuterSolvable.linearOuterAction F
        (g * oddRankInverseTransposeGL h) =
      (q (Matrix.PSL3.OuterSolvable.linearConj F g) * t) *
        (q (Matrix.PSL3.OuterSolvable.linearConj F h) * t)
    rw [map_mul]
    have hrel := congrArg q (oddRankGraphLinearConj h)
    simp only [map_mul] at hrel
    have ht2 : t * t = 1 := by
      dsimp [t]
      rw [← map_mul, ← pow_two, Matrix.PSL3.OuterSolvable.graph_sq, map_one]
    change q (Matrix.PSL3.OuterSolvable.linearConj F g) *
        q (Matrix.PSL3.OuterSolvable.linearConj F (oddRankInverseTransposeGL h)) = _
    calc
      _ = q (Matrix.PSL3.OuterSolvable.linearConj F g) *
          ((q (Matrix.PSL3.OuterSolvable.linearConj F (oddRankInverseTransposeGL h)) * t) * t) := by
        simp only [mul_assoc, ht2, mul_one]
      _ = _ := by rw [← hrel]; simp only [mul_assoc, t]
  have hpowA (z : A) : (z : MulAut.Outer PSL(3,F)) ^ 2 = 1 := by
    exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p z)
  by_cases hgraph : ∃ x : A, (x : MulAut.Outer PSL(3,F)) ≠ 1 ∧
      ∃ g : GL (Fin 3) F,
      (x : MulAut.Outer PSL(3,F)) =
        q (Matrix.PSL3.OuterSolvable.linearConj F g) * t
  · obtain ⟨x, hxne, gx, hx⟩ := hgraph
    have hx2 : (x : MulAut.Outer PSL(3,F)) ^ 2 = 1 := by
      exact hpowA x
    have hle : A ≤ Subgroup.zpowers (x : MulAut.Outer PSL(3,F)) := by
      intro y hy
      by_cases hy1 : (y : MulAut.Outer PSL(3,F)) = 1
      · rw [hy1]
        exact Subgroup.one_mem _
      obtain hcyc | ⟨g, hgy⟩ := hcase (y : MulAut.Outer PSL(3,F))
      · have hy1 : (y : MulAut.Outer PSL(3,F)) = 1 := by
          apply hone_of_mem _ hcyc
          exact hpowA ⟨y, hy⟩
        rw [hy1]
        exact Subgroup.one_mem _
      · have hxy : (x : MulAut.Outer PSL(3,F)) * y ∈ C := by
          apply hmul_mem _ _ ⟨gx, hx⟩
          exact ⟨g, hgy⟩
        have hxy1 : (x : MulAut.Outer PSL(3,F)) * y = 1 := by
          apply hone_of_mem _ hxy
          exact hpowA (x * ⟨y, hy⟩)
        have hyx : (y : MulAut.Outer PSL(3,F)) = x := by
          calc
            (y : MulAut.Outer PSL(3,F)) = 1 * y := by simp
            _ = ((x : MulAut.Outer PSL(3,F)) * y) * y := by rw [hxy1]
            _ = x * (y * y) := by simp [mul_assoc]
            _ = x := by
              have hy2 : y * y = 1 := by simpa [pow_two] using hpowA ⟨y, hy⟩
              rw [hy2, mul_one]
        rw [hyx]
        exact Subgroup.mem_zpowers _
    have hcard : Nat.card A ≤ 2 := by
      have horder : orderOf (x : MulAut.Outer PSL(3,F)) = 2 :=
        orderOf_eq_prime hx2 hxne
      exact (Subgroup.card_le_of_le hle).trans (by
        rw [Nat.card_zpowers, horder])
    exact hcard
  · have hle : A ≤ (⊥ : Subgroup (MulAut.Outer PSL(3,F))) := by
      intro x hx
      obtain hcyc | hcyc := hcase (x : MulAut.Outer PSL(3,F))
      · exact mem_bot.mpr (hone_of_mem _ hcyc (by
          exact hpowA ⟨x, hx⟩))
      · by_cases h1 : (x : MulAut.Outer PSL(3,F)) = 1
        · exact mem_bot.mpr h1
        · exact (hgraph ⟨⟨x, hx⟩, h1, hcyc⟩).elim
    exact (Subgroup.card_le_of_le hle).trans (by norm_num)

/-- All automorphisms of PSL₃ over an odd prime field have two-rank at most three. -/
theorem psl3_automorphism_two_rank_le_three
    {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) :
    primeRank 2 (MulAut PSL(3,F)) ≤ 3 := by
  let _ : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  let _ : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  have hcenter : center PSL(3,F) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  let e : PSL(3,F) ≃* MulAut.innerSubgroup PSL(3,F) :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hcenter)
  have hi : primeRank 2 (MulAut.innerSubgroup PSL(3,F)) ≤ 2 :=
    (primeRank_equiv 2 e).symm.le.trans (psl3_primeRank_two_le hp ho hF)
  have h := primeRank_le_ker_add (p := 2)
    (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))
  rw [QuotientGroup.ker_mk'] at h
  exact h.trans (Nat.add_le_add hi
    (psl3_outer_two_rank_le_one (Group.IsPerfect.not_isSolvable PSL(3,F)) hp ho hF))

/-- Automorphisms of the special linear cover descend faithfully through its center. -/
theorem sl3_automorphism_two_rank_le_three
    {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) :
    primeRank 2 (MulAut SL(3,F)) ≤ 3 := by
  let _ : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  exact (automorphism_primeRank_le_quotient_center (E := SL(3,F)) 2).trans
    (psl3_automorphism_two_rank_le_three hp ho hF)

private theorem psu3_center_eq_bot
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card E = p ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ p) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    simpa only [pow_one] using
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hconj))
  have hnonfixed : ∃ t : E, J.conj t ≠ t := by
    by_contra! h
    have hc : Nat.card {x : E // J.conj x = x} = Nat.card E :=
      Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [hcard, hfixed] at hc
    have hp2 := hp.one_lt
    nlinarith
  obtain ⟨e⟩ := exists_projectiveEquiv J p hcard hfixed
  have hcenter := standard_psu_center_eq_bot (standardForm J) rfl
    (two_ne_zero_of_odd_card ho hcard) hnonfixed
  apply bot_unique
  intro x hx
  have hx' := (Subgroup.centerCongr e ⟨x, hx⟩).property
  change e x ∈ center (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) at hx'
  rw [hcenter, mem_bot] at hx'
  exact mem_bot.mpr (e.injective (hx'.trans (map_one e).symm))

/-- Quasisimplicity supplies the simple-group premise of semilinear coverage. -/
theorem quasisimple_psu3_automorphism_two_rank_le_three
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card E = p ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ p) :
    primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3 := by
  let P := ProjectiveSpecialUnitaryMatrixGroup J
  have hcenter := psu3_center_eq_bot J hp ho hcard hconj
  let e : (P ⧸ center P) ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot)
  let _ : IsSimpleGroup (P ⧸ center P) := IsQuasisimple.simple
  let _ : IsSimpleGroup P := e.symm.isSimpleGroup
  exact psu3_automorphism_two_rank_le_three J hp ho hcard hconj

/-- Faithful central descent handles SU₃, including a nontrivial scalar center. -/
theorem su3_automorphism_two_rank_le_three
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsQuasisimple J.specialSubgroup]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card E = p ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ p) :
    primeRank 2 (MulAut J.specialSubgroup) ≤ 3 := by
  let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hk := J.specialToProjective_ker_eq_center
    (psu3_center_eq_bot J hp ho hcard hconj)
  let f : PerfectCentralCovering.Cover J.specialSubgroup
      (ProjectiveSpecialUnitaryMatrixGroup J) := {
    toMonoidHom := J.specialToProjective
    surjective := J.specialToProjective_surjective
    isPerfect := inferInstance
    ker_le_center := J.specialToProjective_ker_le_center }
  let e : (J.specialSubgroup ⧸ center J.specialSubgroup) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
        J.specialToProjective_surjective)
  let _ : IsSimpleGroup (J.specialSubgroup ⧸ center J.specialSubgroup) :=
    IsQuasisimple.simple
  let _ : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  exact (f.automorphism_primeRank_le hk 2).trans
    (psu3_automorphism_two_rank_le_three J hp ho hcard hconj)

end Theory.SpecificGroups.OddThreeRank
