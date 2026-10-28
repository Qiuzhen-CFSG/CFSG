module

public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootRigidity
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.OppositePair
public import Theory.GroupTheory.PResidual.PrimeToMonotone
public import Theory.GroupAction.AutomorphismFixerTransport

/-!
# Residual rigidity above a PSL₃ Borel

For a finite field of order 2ⁿ, n > 0, a strict overgroup J of the
normalizer of a specified Sylow two-subgroup has trivial pointwise
Aut(PSL₃)-fixer on its embedded O^{2′}(J). The residual is computed in J
before mapping into PSL₃. The proof includes the fields of orders two and
four and uses neither simplicity nor a covering-group hypothesis.

The intrinsic argument avoids a parabolic-overgroup classification.
An automorphism fixing the upper Sylow subgroup is corrected by an upper
unipotent element to preserve an opposite Sylow pair. Root orientation and
field reconstruction then show that it is conjugation by a highest-root
element. Trace removes projective scalar ambiguity, and the centralizer of
any nonidentity highest-root element lies in the Borel. Since O^{2′}(J)
contains the Sylow subgroup, a nonidentity residual fixer would put the
residual inside the Borel. Frattini's argument would then put J inside the
Borel as well. Sylow conjugacy transports the result with its marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
`refs/quasithin.pdf`, proof of E.6.8, printed p.248 (PDF p.259).
The imported matrix root geometry follows GLS3, Theorem 2.5.12(a) and §2.7.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3Even.AutomorphismCoverage
namespace Matrix.PSL3.LinearThree.ResidualRigidity
variable {F : Type*} [Field F]

private theorem root01 (a : F) :
    rootElement (by decide : (0 : Fin 3) ≠ 1) a = projective F ⟨a, 0, 0⟩ := by
  apply congrArg (QuotientGroup.mk : SL(3, F) → PSL(3, F))
  apply Subtype.ext
  change 1 + Matrix.single 0 1 a = matrix F ⟨a, 0, 0⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

private theorem root12 (a : F) :
    rootElement (by decide : (1 : Fin 3) ≠ 2) a = projective F ⟨0, a, 0⟩ := by
  apply congrArg (QuotientGroup.mk : SL(3, F) → PSL(3, F))
  apply Subtype.ext
  change 1 + Matrix.single 1 2 a = matrix F ⟨0, a, 0⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

private theorem field_root (σ : F ≃+* F) {i j : Fin 3} (hij : i ≠ j) (a : F) :
    fieldAction F σ (rootElement hij a) = rootElement hij (σ a) := by
  rw [rootElement, fieldAction_mk]
  congr 1
  apply Subtype.ext
  ext k l
  change σ ((1 + Matrix.single i j a) k l) = (1 + Matrix.single i j (σ a)) k l
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add]
  split_ifs <;> simp

private theorem exists_upper_correction [Finite F] {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (α : MulAut PSL(3, F)) (hfix : ∀ u : U F, α (projective F u) = projective F u) :
    ∃ b : U F, PreservesUnipotentPair F (MulAut.conj (projective F b) * α) := by
  have ha : (upperUnipotent F).map α.toMonoidHom = upperUnipotent F := by
    change (unipotent F).map α.toMonoidHom = unipotent F
    rw [← projective_range]
    ext x
    constructor
    · rintro ⟨_,⟨u,rfl⟩,rfl⟩
      exact ⟨u,hfix u |>.symm⟩
    · rintro ⟨u,rfl⟩
      exact ⟨projective F u,⟨u,rfl⟩,hfix u⟩
  have hd : Disjoint (upperUnipotent F) ((lowerUnipotent F).map α.toMonoidHom) := by
    simpa only [ha] using Subgroup.disjoint_map (f := α.toMonoidHom) α.injective
      (OppositePair.disjoint_upper_lower F)
  let S := unipotentSylow F hn hF
  let L := S.mapSurjective (f := (graph F).toMonoidHom) (graph F).surjective
  let V := L.mapSurjective (f := α.toMonoidHom) α.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3, F) S V
  have hs : (upperUnipotent F).map (MulAut.conj g).toMonoidHom =
      (lowerUnipotent F).map α.toMonoidHom := congrArg Sylow.toSubgroup hg
  obtain ⟨b,hb,hbl⟩ := OppositePair.exists_unipotent_conjugator F g (hs.symm ▸ hd)
  rw [hs] at hbl
  have hbu := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((upperUnipotent F).le_normalizer hb)
  change b ∈ unipotent F at hb
  rw [← projective_range] at hb
  obtain ⟨u,rfl⟩ := hb
  refine ⟨u,?_,?_⟩
  · change (upperUnipotent F).map ((MulAut.conj (projective F u)).toMonoidHom.comp
      α.toMonoidHom) = _
    rw [← Subgroup.map_map,ha]
    exact hbu
  · change (lowerUnipotent F).map ((MulAut.conj (projective F u)).toMonoidHom.comp
      α.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hbl

private theorem diagonal_field_eq_one (d : Fin 3 → Fˣ) (σ : F ≃+* F)
    (b : U F)
    (hh : ∀ u : U F, (linearConj F (diagonalGL d) * fieldAction F σ) (projective F u) =
      projective F (b * u * b⁻¹)) :
    linearConj F (diagonalGL d) * fieldAction F σ = 1 := by
  have h01 (a : F) : projective F ⟨σ a * (d 0 : F) * (↑(d 1)⁻¹ : F),0,0⟩ =
      projective F (b * ⟨a, 0, 0⟩ * b⁻¹) := by
    have h := hh ⟨a, 0, 0⟩
    rw [← root01, MulAut.mul_apply, field_root, linearConj_diagonalGL_rootElement,
      root01] at h
    exact h
  have h12 (a : F) : projective F ⟨0,σ a * (d 1 : F) * (↑(d 2)⁻¹ : F),0⟩ =
      projective F (b * ⟨0, a, 0⟩ * b⁻¹) := by
    have h := hh ⟨0, a, 0⟩
    rw [← root12, MulAut.mul_apply, field_root, linearConj_diagonalGL_rootElement,
      root12] at h
    exact h
  have hd01 : d 0 = d 1 := by
    have h := congrArg U.x (projective_injective F (h01 1))
    change σ 1 * (d 0 : F) * (↑(d 1)⁻¹ : F) = b.x + 1 + -b.x at h
    have hv : ((d 0 * (d 1)⁻¹ : Fˣ) : F) = 1 := by simpa using h
    exact mul_inv_eq_one.mp (Units.ext hv)
  have hd12 : d 1 = d 2 := by
    have h := congrArg U.y (projective_injective F (h12 1))
    change σ 1 * (d 1 : F) * (↑(d 2)⁻¹ : F) = b.y + 1 + -b.y at h
    have hv : ((d 1 * (d 2)⁻¹ : Fˣ) : F) = 1 := by simpa using h
    exact mul_inv_eq_one.mp (Units.ext hv)
  have hσ : σ = 1 := by
    ext a
    have h := congrArg U.x (projective_injective F (h01 a))
    change σ a * (d 0 : F) * (↑(d 1)⁻¹ : F) = b.x + a + -b.x at h
    simpa [hd01, mul_assoc] using h
  have hd (i : Fin 3) : d i = d 0 := by
    fin_cases i
    · rfl
    · exact hd01.symm
    · exact (hd01.trans hd12).symm
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext
  intro i j hij a
  change (linearConj F (diagonalGL d) * fieldAction F σ) (rootElement hij a) = _
  simp [linearConj_diagonalGL_rootElement,hσ,hd]

/-- Every pointwise Sylow fixer is a highest-root inner action. -/
theorem fixer_unipotent_is_root_inner [Finite F] [CharP F 2] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (α : MulAut PSL(3, F))
    (hfix : α ∈ fixingSubgroup (MulAut PSL(3, F)) (unipotent F : Set PSL(3, F))) :
    ∃ a : F, α = MulAut.conj (projective F ⟨0, 0, a⟩) := by
  have hα (u : U F) : α (projective F u) = projective F u :=
    hfix ⟨_, by rw [← projective_range]; exact ⟨u,rfl⟩⟩
  obtain ⟨b,hb⟩ := exists_upper_correction hn hF α hα
  let β := MulAut.conj (projective F b) * α
  have hβ (u : U F) : β (projective F u) = projective F (b * u * b⁻¹) := by
    simp only [β,MulAut.mul_apply,hα,MulAut.conj_apply,map_mul,map_inv]
  obtain ⟨ε,hε⟩ := exists_oppositionGraph_preserves_roots_of_charTwo F β hb
  obtain ⟨d,σ,hd⟩ := eq_diagonal_field_of_preservesRootGroups _ hε
  have he : β = (oppositionGraph F ^ (ε : ℕ)) *
      (linearConj F (diagonalGL d) * fieldAction F σ) := by
    rw [← hd,mul_inv_cancel_left]
  have he1 : β = 1 := by
    fin_cases ε
    · simp only [pow_zero,one_mul] at he
      rw [he]
      exact diagonal_field_eq_one d σ b (by rwa [← he])
    · simp only [pow_one] at he
      have h := hβ ⟨1, 0, 0⟩
      rw [he,← root01] at h
      simp only [MulAut.mul_apply,field_root,map_one,linearConj_diagonalGL_rootElement,
        oppositionGraph_rootElement] at h
      change rootElement (by decide : (1 : Fin 3) ≠ 2) _ = _ at h
      rw [root12] at h
      have hx := congrArg U.x (projective_injective F h)
      change 0 = b.x + 1 + -b.x at hx
      simp at hx
  have ha : α = MulAut.conj (projective F b⁻¹) := by
    have h : MulAut.conj (projective F b) * α = 1 := he1
    rw [← inv_eq_iff_mul_eq_one] at h
    simpa only [map_inv] using h.symm
  have hz : b⁻¹ ∈ Z F := by
    rw [Z_eq_center,Subgroup.mem_center_iff]
    intro u
    have h := hα u
    rw [ha,MulAut.conj_apply,← map_inv,← map_mul,← map_mul] at h
    have hh := projective_injective F h
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨hx,hy⟩ := (mem_Z F b⁻¹).mp hz
  refine ⟨(b⁻¹).c,?_⟩
  have hb' : b⁻¹ = ⟨0,0,(b⁻¹).c⟩ := U.ext hx hy rfl
  rwa [← hb']

private theorem root_trace [CharP F 2] (a : F) :
    Matrix.trace (specialLinear F ⟨0, 0, a⟩).val = 1 := by
  change Matrix.trace (matrix F ⟨0, 0, a⟩) = 1
  simp [matrix, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

/-- A projective commutation with a highest-root element lifts exactly.
The root element has trace one in characteristic two, removing scalars. -/
private theorem root_commute_of_projective [CharP F 2] (g : SL(3, F)) (a : F)
    (hc : projection F g * projective F ⟨0, 0, a⟩ =
      projective F ⟨0, 0, a⟩ * projection F g) :
    g * specialLinear F ⟨0, 0, a⟩ = specialLinear F ⟨0, 0, a⟩ * g := by
  let u := specialLinear F ⟨0, 0, a⟩
  have he : projection F (g*u*g⁻¹) = projection F u := by
    change projection F g * projective F ⟨0, 0, a⟩ * (projection F g)⁻¹ = _
    rw [hc, mul_inv_cancel_right]
    rfl
  have hk := (projection F).eq_iff.mp he
  rw [projection_ker] at hk
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hk
  have hv : (g*u*g⁻¹).val = r • u.val := by
    calc
      (g*u*g⁻¹).val = (u * (u⁻¹ * (g*u*g⁻¹))).val := by simp only [mul_inv_cancel_left]
      _ = u.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
      _ = r • u.val := by
        ext i j
        simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]
  have ht : Matrix.trace (g*u*g⁻¹).val = 1 := by
    change Matrix.trace (g.val*u.val*g⁻¹.val) = 1
    rw [Matrix.trace_mul_cycle]
    have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
    rw [hi, one_mul]
    exact root_trace a
  rw [hv, Matrix.trace_smul, root_trace a, smul_eq_mul, mul_one] at ht
  have hg : g*u*g⁻¹ = u := Subtype.ext (by simpa [ht] using hv)
  exact mul_inv_eq_iff_eq_mul.mp hg

/-- A nonidentity highest-root element has its full centralizer in the Borel. -/
theorem root_centralizer_le_borel [Finite F] [CharP F 2] (a : F) (ha : a ≠ 0) :
    centralizer ({projective F ⟨0, 0, a⟩} : Set PSL(3, F)) ≤ borel F := by
  intro x hx
  obtain ⟨g,rfl⟩ := projection_surjective F x
  have hc := mem_centralizer_singleton_iff.mp hx
  have hh : g.val * matrix F ⟨0, 0, a⟩ = matrix F ⟨0, 0, a⟩ * g.val :=
    congrArg Subtype.val (root_commute_of_projective g a hc)
  have h1 := congrArg (fun m => m 0 0) hh
  have h2 := congrArg (fun m => m 0 1) hh
  have h3 := congrArg (fun m => m 1 2) hh
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h1 h2 h3
  exact mem_map_of_mem _ ((mem_borelSL_iff F g).mpr
    ⟨h3.resolve_right ha,h1.resolve_left ha,h2.resolve_left ha⟩)

private theorem sylow_le_residual {G : Type*} [Group G] {p : ℕ}
    (S : Sylow p G) : (S : Subgroup G) ≤ primeToResidual p G := by
  intro x hx
  obtain ⟨n,hn⟩ := S.isPGroup' ⟨x,hx⟩
  exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)

private theorem le_normalizer_of_residual_le {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (J : Subgroup G)
    (hSJ : (S : Subgroup G) ≤ J)
    (hR : (primeToResidual p J).map J.subtype ≤ normalizer (S : Set G)) :
    J ≤ normalizer (S : Set G) := by
  let T := S.subtype hSJ
  have hf := T.normalizer_sup_eq_top' (sylow_le_residual T)
  have he : normalizer (T : Set J) = (normalizer (S : Set G)).subgroupOf J := by
    exact (subgroupOf_normalizer_eq hSJ).symm
  rw [he] at hf
  have hl : (primeToResidual p J) ≤ (normalizer (S : Set G)).subgroupOf J :=
    (map_le_iff_le_comap).mp hR
  rw [sup_of_le_left hl] at hf
  exact (subgroupOf_eq_top.mp hf)

/-- Strict overgroups of the standard Borel have no nonidentity residual fixer. -/
theorem borel_residual_fixer_eq_bot [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (J : Subgroup PSL(3, F))
    (hJ : borel F < J) :
    fixingSubgroup (MulAut PSL(3, F))
      ((primeToResidual 2 J).map J.subtype : Set PSL(3, F)) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card,hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hn])
  let : CharP F 2 := ringChar.of_eq hc
  let S := unipotentSylow F hn hF
  have hSJ : (S : Subgroup PSL(3, F)) ≤ J :=
    (show unipotent F ≤ borel F from
      (normalizer_unipotent F hn hF) ▸ (unipotent F).le_normalizer).trans hJ.le
  have hSR : unipotent F ≤ (primeToResidual 2 J).map J.subtype := by
    have h := Subgroup.map_mono (f := J.subtype) (sylow_le_residual (S.subtype hSJ))
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hSJ] at h
  apply le_bot_iff.mp
  intro α hα
  have hfix : α ∈ fixingSubgroup (MulAut PSL(3, F)) (unipotent F : Set PSL(3, F)) := by
    rw [mem_fixingSubgroup_iff]
    intro u hu
    exact hα ⟨u,hSR hu⟩
  obtain ⟨a,rfl⟩ := fixer_unipotent_is_root_inner hn hF α hfix
  by_cases ha : a = 0
  · subst a
    have he : (⟨0, 0, 0⟩ : U F) = 1 := rfl
    simp only [he,map_one,mem_bot]
  · have hR : (primeToResidual 2 J).map J.subtype ≤ borel F := by
      apply le_trans _ (root_centralizer_le_borel a ha)
      intro x hx
      rw [mem_centralizer_singleton_iff]
      have hh : projective F ⟨0, 0, a⟩ * x * (projective F ⟨0, 0, a⟩)⁻¹ = x :=
        hα ⟨x,hx⟩
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hN := le_normalizer_of_residual_le S J hSJ
      (hR.trans (normalizer_unipotent F hn hF).ge)
    exact (hJ.not_ge (hN.trans (normalizer_unipotent F hn hF).le)).elim

/-- For every marked Sylow two-subgroup, a strict overgroup of its normalizer
has trivial full automorphism fixer on its embedded prime-to-two residual. -/
theorem residual_fixer_eq_bot [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3, F))
    (J : Subgroup PSL(3, F)) (hJ : normalizer (S : Set PSL(3, F)) < J) :
    fixingSubgroup (MulAut PSL(3, F))
      ((primeToResidual 2 J).map J.subtype : Set PSL(3, F)) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3, F) (unipotentSylow F hn hF) S
  let e : PSL(3, F) ≃* PSL(3, F) := MulAut.conj g
  have hS : (unipotent F).map e.toMonoidHom = (S : Subgroup PSL(3, F)) :=
    congrArg Sylow.toSubgroup hg
  have hN : (borel F).map e.toMonoidHom = normalizer (S : Set PSL(3, F)) := by
    rw [← normalizer_unipotent F hn hF, map_equiv_normalizer_eq, hS]
    rfl
  let K := J.map e.symm.toMonoidHom
  have hKJ : K.map e.toMonoidHom = J := by
    simp [K,Subgroup.map_map]
  have hK : borel F < K := by
    apply (map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hN,hKJ]
    exact hJ
  have hfix := borel_residual_fixer_eq_bot hn hF K hK
  have he := MulAut.map_fixingSubgroup_congr e ((primeToResidual 2 K).map K.subtype)
  rw [hfix,Subgroup.map_bot,map_embedded_primeToResidual,hKJ] at he
  exact he.symm

end Matrix.PSL3.LinearThree.ResidualRigidity
