module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.MarkedInvariants
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.SpecificGroups.PSL2.TwoResidual

/-!
# Model invariants for the binary PSL₃ involution comparison

Every inner involutory automorphism fixes a conjugate of the highest-root
centralizer, including over F₂. The torus–unipotent factorization makes this
centralizer solvable. At field orders two and four its order has no factor
three; the projective scalar divisor is retained in the calculation.

The possible larger outer residual models are nonsolvable: PSL₃ by elementary
matrix perfectness, PSL₂ by the transvection commutator argument, and PSU₃ by
its actual graph-fixed PSL₂ subgroup. The binary PSL₂ derived subgroup always
has an element of order three, including the nonperfect PSL₂(2) endpoint.

These intrinsic results supply the comparison of 16.1.4(1),(4)–(6) in
Aschbacher–Smith, combined manuscript of 1 March 2004, printed pp.1170–1171
and 1193. The automorphism classification and its outer residual rows are
separate inputs; this module does not assume them.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Matrix.PSL3
open scoped MatrixGroups
namespace Matrix.PSL3Even.ResidualComparison
open Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.EvenInnerCentralizers

private theorem binary_char (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) : ringChar F = 2 := by
  let := Fintype.ofFinite F
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hF]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn))


/-- The positive-exponent version of the existing involution conjugacy
calculation; the Sylow argument also covers the binary field itself. -/
theorem involution_isConj_root_of_pos (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (t : PSL(3,F)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsConj t (root F) := by
  let : CharP F 2 := ringChar.of_eq (binary_char F hn hF)
  obtain ⟨y, hty⟩ :=
    (Matrix.PSL3.LinearThree.unipotentSylow F hn hF).exists_isConj_of_orderOf_eq_prime_pow
      (n := 1) (by simpa only [pow_one] using orderOf_eq_prime ht2 ht)
  have hy : (y : PSL(3,F)) ∈ (projective F).range :=
    (Matrix.PSL3.LinearThree.projective_range F).ge y.property
  obtain ⟨u, hu⟩ := hy
  obtain ⟨g, hg⟩ := isConj_iff.mp hty
  have hconj : MulAut.conj g t = projective F u := hg.trans hu.symm
  have hu2 : u ^ 2 = 1 := by
    apply projective_injective F
    rw [map_pow, ← hconj, ← map_pow, ht2, map_one, map_one]
  have hun : u ≠ 1 := by
    intro he
    apply ht
    apply (MulAut.conj g).injective
    rw [hconj, he, map_one, map_one]
  have hroot : IsConj (projective F u) (root F) :=
    (projection F).map_isConj (specialLinear_isConj_root F u hun hu2)
  exact hty.trans (hu ▸ hroot)

/-- Every inner involutory action fixes a conjugate of the marked root
centralizer, including at field order two. -/
theorem inner_fixed_equiv_root (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (a : MulAut PSL(3,F))
    (ha : orderOf a = 2) (hi : ∃ x, a = MulAut.conj x) :
    Nonempty (a.fixedSubgroup ≃* Matrix.PSL3.EvenInnerCentralizers.centralizer F) := by
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  obtain ⟨t, ht, _, he⟩ := MulAut.inner_involution_representative
    center_eq_bot_of_simple_perfect a ha hi
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  obtain ⟨g, hg⟩ := isConj_iff.mp (involution_isConj_root_of_pos F hn hF t ht1
    (ht ▸ pow_orderOf_eq_one t))
  let e := MulAut.conj g
  have hm : (Subgroup.centralizer ({t} : Set PSL(3,F))).map e.toMonoidHom =
      Matrix.PSL3.EvenInnerCentralizers.centralizer F := by
    ext x
    rw [Subgroup.mem_map_equiv]
    change e.symm x ∈ Subgroup.centralizer {t} ↔ x ∈ Subgroup.centralizer {root F}
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    rw [← e.injective.eq_iff, map_mul, map_mul, show e t = root F from hg,
      e.apply_symm_apply]
  exact ⟨((MulEquiv.subgroupCongr he).trans (e.subgroupMap _)).trans
    (MulEquiv.subgroupCongr hm)⟩

/-- The root centralizer is an extension of a binary unipotent group by a torus. -/
theorem root_centralizer_solvable (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    Group.IsSolvable (Matrix.PSL3.EvenInnerCentralizers.centralizer F) := by
  let : CharP F 2 := ringChar.of_eq (binary_char F hn hF)
  have hp : IsPGroup 2 (U F) := IsPGroup.of_card (n := n * 3) (by
    rw [card_U, hF, pow_mul])
  let : Group.IsNilpotent (U F) := hp.isNilpotent
  let f : U F →* centralizerSL F :=
    (specialLinear F).codRestrict (centralizerSL F) (specialLinear_mem_centralizerSL F)
  let : Group.IsSolvable (centralizerSL F) := by
    apply Group.isSolvable_of_ker_le_range f (diagonalHom F)
    intro x hx
    refine ⟨unipotentPart F x, ?_⟩
    apply Subtype.ext
    change specialLinear F (unipotentPart F x) = x.val
    have he := centralizerSL_factorization F x
    have hx' : diagonalHom F x = 1 := hx
    simpa only [hx', map_one, one_mul] using he.symm
  let p : centralizerSL F →* Matrix.PSL3.EvenInnerCentralizers.centralizer F :=
    ((projection F).comp (centralizerSL F).subtype).codRestrict _ (by
      intro x
      rw [← centralizer_map F]
      exact ⟨x, x.property, rfl⟩)
  apply Group.isSolvable_of_surjective (f := p)
  rintro ⟨y, hy⟩
  rw [← centralizer_map F] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The scalar torus quotient leaves no odd divisor at field order two or four. -/
theorem root_centralizer_small (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : n = 1 ∨ n = 2) (hF : Nat.card F = 2 ^ n) :
    ¬ 3 ∣ Nat.card (Matrix.PSL3.EvenInnerCentralizers.centralizer F) := by
  have hn0 : 0 < n := by rcases hn with rfl | rfl <;> omega
  have hc := (unipotentInCentralizer F).range.card_mul_index
  rw [(MarkedInvariants.torus_complement F hF hn0).index_eq_card,
    MarkedInvariants.unipotent_card, MarkedInvariants.torus_card, hF] at hc
  rw [← hc]
  rcases hn with rfl | rfl <;> norm_num

/-- Elementary-matrix perfectness excludes solvability of the derived PSL₃ model. -/
theorem psl_three_commutator_not_solvable (F : Type*) [Field F] :
    ¬ Group.IsSolvable (commutator PSL(3,F)) := by
  let : Nontrivial PSL(3,F) := ⟨⟨root F, 1, root_ne_one F⟩⟩
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  intro h
  let := h
  let e : commutator PSL(3,F) ≃* PSL(3,F) :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv
  exact Group.IsPerfect.not_isSolvable PSL(3,F)
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

/-- A binary PSL₂ model of field order at least four is nonsolvable. -/
theorem psl_two_not_solvable (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) : ¬ Group.IsSolvable (PSL2MatrixGroup F) := by
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  have hc : commutator (PSL2MatrixGroup F) = ⊤ :=
    SL2Simple.PSL_commutator_eq_top ⟨(u : F), u.ne_zero, fun hs =>
      hu (Units.val_eq_one.mp (CharTwo.sq_injective (by simpa using hs)))⟩
  let : Group.IsPerfect (PSL2MatrixGroup F) := ⟨hc⟩
  exact Group.IsPerfect.not_isSolvable _

/-- The derived binary PSL₂ model is nonsolvable outside the field-order-two endpoint. -/
theorem binary_psl_two_commutator_not_solvable {n : ℕ} (hn : 2 ≤ n) :
    ¬ Group.IsSolvable (commutator (PSL2BinaryMatrixGroup n)) := by
  obtain ⟨x, hx, hx1⟩ := BenderSuzuki.Converse.exists_ne_zero_ne_one n hn
  have hc : commutator (PSL2BinaryMatrixGroup n) = ⊤ :=
    SL2Simple.PSL_commutator_eq_top ⟨x, hx, fun hs => by
      rcases sq_eq_one_iff.mp hs with hs | hs
      · exact hx1 hs
      · exact hx1 (by simpa only [CharTwo.neg_eq] using hs)⟩
  intro h
  let := h
  let e : commutator (PSL2BinaryMatrixGroup n) ≃* PSL2BinaryMatrixGroup n :=
    (MulEquiv.subgroupCongr hc).trans topEquiv
  exact psl_two_not_solvable (BinaryGaloisField n) (by
    rw [BenderSuzuki.Converse.card_binaryGaloisField n (by omega)]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn)
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

/-- The actual graph-fixed PSL₂ subgroup witnesses nonsolvability of PSU₃. -/
theorem unitary_not_solvable {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {m : ℕ} (hm : 2 ≤ m)
    (hcard : Nat.card E = (2 ^ m) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ m)
    (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0]) :
    ¬ Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : CharP E 2 := ringChar.of_eq (binary_char E (n := m * 2) (by omega)
    (by simpa only [pow_mul] using hcard))
  let K := FixedBy.subfield E J.conj
  have hK : 4 ≤ Nat.card K := by
    change 4 ≤ Nat.card {x : E // J.conj x = x}
    rw [hfixed]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm
  intro h
  let := h
  let e := J.projectiveGraphFixedEquiv hJ
  exact psl_two_not_solvable K hK
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

/-- The order-three matrix survives in the derived subgroup, including PSL₂(2)′. -/
theorem three_dvd_binary_psl_two_commutator {n : ℕ} (hn : 0 < n) :
    3 ∣ Nat.card (commutator (PSL2BinaryMatrixGroup n)) := by
  let F := BinaryGaloisField n
  let c : BenderSuzuki.Converse.SL2 F :=
    ⟨!![0,1;1,1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
  have hpow : c ^ 3 = 1 := by
    apply Subtype.ext
    change ((!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 3) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hne : c ≠ 1 := by
    intro h
    have he := congrArg (fun a : BenderSuzuki.Converse.SL2 F => a.val 0 0) h
    simp [c] at he
  have horder : orderOf (BenderSuzuki.Converse.pi F c) = 3 :=
    (orderOf_injective (BenderSuzuki.Converse.pi F)
      BenderSuzuki.Converse.pi_injective c).trans (orderOf_eq_prime hpow hne)
  have hc : BenderSuzuki.Converse.pi F c ∈ commutator (PSL2BinaryMatrixGroup n) := by
    rw [← Theory.PSL2.binary_twoResidual_eq_commutator hn]
    apply mem_pResidual_of_orderOf_coprime
    rw [horder]
    decide
  let u : commutator (PSL2BinaryMatrixGroup n) := ⟨BenderSuzuki.Converse.pi F c, hc⟩
  have hu : orderOf u = 3 :=
    (orderOf_injective (commutator (PSL2BinaryMatrixGroup n)).subtype
      (Subgroup.subtype_injective _) u).symm.trans horder
  exact hu ▸ orderOf_dvd_natCard u

end Matrix.PSL3Even.ResidualComparison
