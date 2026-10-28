module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.FourSpace
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The orthogonal cubic obstruction in A.2.17

The source uses `J = O^{p′}(C(K))`, a subgroup of the centralizer, and proves
`m₃(J) ≥ 2` from its orthogonal central-product description. Here the literal
nested residual is retained, together with its isomorphic image in the ambient
group. The two cubic factors are mapped into this residual and give an actual
elementary abelian subgroup of order nine, contradicting the source bound.

The adapters use exactly the scalar quotient of the elementary odd/split
carrier, or of the commutator minus carrier. Their structural premises remain
explicit: a faithful covering block map, containment of its projective image
in the residual, and a cubic element in the complementary Omega group.
The latter premise is discharged here in dimensions seven and split eight.
Constructing the ambient fundamental subgroup and proving the full residual
image equality are still required to complete the orthogonal source branch.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma A.2.17, printed p.39. This module neither
imports the sibling classical branches nor asserts the completed lemma.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.Orthogonal
open ClassicalOrthogonal Matrix

variable {G : Type*} [Group G]

/-- The literal prime-to-p residual of the centralizer of K. -/
@[expose] def residual (p : ℕ) (K : Subgroup G) : Subgroup (Subgroup.centralizer (K : Set G)) :=
  Subgroup.primeToResidual p (Subgroup.centralizer (K : Set G))

/-- Its image in the ambient group, for comparing the block maps. -/
@[expose] def residualImage (p : ℕ) (K : Subgroup G) : Subgroup G :=
  (residual p K).map (Subgroup.centralizer (K : Set G)).subtype

/-- Inclusion into the ambient group loses no elements of the nested residual. -/
def residualEquivImage (p : ℕ) (K : Subgroup G) :
    residual p K ≃* residualImage p K :=
  (residual p K).equivMapOfInjective _ Subtype.val_injective

/-- A product with square-one kernel constructs a nine-subgroup of the actual J. -/
theorem residual_nine_of_productMap {A B : Type*} [Group A] [Group B]
    (p : ℕ) (K : Subgroup G) (f : A × B →* G)
    (hker : ∀ x, f x = 1 → x ^ 2 = 1)
    (hJ : f.range ≤ residualImage p K)
    (a : A) (b : B) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ E : Subgroup (residual p K), IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  let fJ : A × B →* residualImage p K :=
    f.codRestrict _ (fun x => hJ ⟨x, rfl⟩)
  obtain ⟨E, _, hE, hc⟩ := CubicProductQuotient.exists_nine fJ
    (fun x hx => hker x (congrArg Subtype.val hx)) a b ha hb
  let := hE
  let e := residualEquivImage p K
  refine ⟨E.map e.symm.toMonoidHom, IsElementaryAbelian.map _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective]
  exact hc

/-- The nine-subgroup gives three-rank at least two and contradicts source (*). -/
theorem residual_rank_obstruction [Finite G] (p : ℕ) (K : Subgroup G)
    (h : ∃ E : Subgroup (residual p K), IsElementaryAbelian 3 E ∧ Nat.card E = 9) :
    2 ≤ primeRank 3 (residual p K) ∧ ¬ primeRank 3 (residual p K) ≤ 1 := by
  obtain ⟨E, hE, hc⟩ := h
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hr : 2 ≤ primeRank 3 (residual p K) :=
    primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 E)) hc E.subtype E.subtype_injective
  exact ⟨hr, fun hl => (by omega)⟩

universe u
variable {F : Type u} [Field F]

/-- Rank step for the literal odd orthogonal block map and scalar quotient. -/
theorem odd_residual_nine_of_blocks {n p : ℕ}
    (K : Subgroup (POmegaOdd n F))
    (f : Matrix.SpecialLinearGroup (Fin 2) F × OmegaOdd (n - 2) F →* OmegaOdd n F)
    (hf : Function.Injective f)
    (hJ : ((projectiveElementaryMap (formB n F)).comp f).range ≤ residualImage p K)
    (hcomp : ∃ b : OmegaOdd (n - 2) F, orderOf b = 3) :
    ∃ E : Subgroup (residual p K), IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := hcomp
  exact residual_nine_of_productMap p K ((projectiveElementaryMap (formB n F)).comp f)
    (Fundamental.elementaryProjective_kernel_square (formB n F) f hf) hJ
    Fundamental.cubicSL b Fundamental.cubicSL_order hb

/-- Rank step for the literal split orthogonal block map and scalar quotient. -/
theorem plus_residual_nine_of_blocks {n p : ℕ}
    (K : Subgroup (POmegaPlus n F))
    (f : Matrix.SpecialLinearGroup (Fin 2) F × OmegaPlus (n - 2) F →* OmegaPlus n F)
    (hf : Function.Injective f)
    (hJ : ((projectiveElementaryMap (formD n F)).comp f).range ≤ residualImage p K)
    (hcomp : ∃ b : OmegaPlus (n - 2) F, orderOf b = 3) :
    ∃ E : Subgroup (residual p K), IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := hcomp
  exact residual_nine_of_productMap p K ((projectiveElementaryMap (formD n F)).comp f)
    (Fundamental.elementaryProjective_kernel_square (formD n F) f hf) hJ
    Fundamental.cubicSL b Fundamental.cubicSL_order hb

/-- Rank step for the actual minus commutator carrier and its scalar quotient. -/
theorem minus_residual_nine_of_blocks [Finite F] {n p : ℕ}
    (K : Subgroup (ClassicalGroup.POmegaMinus n F))
    (f : Matrix.SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F ((n - 2) - 1)) (Minus.quadraticForm F (n - 2)) →*
      Minus.Omega F (Minus.Space F (n - 1)) (Minus.quadraticForm F n))
    (hf : Function.Injective f)
    (hJ : ((QuotientGroup.mk' (Minus.scalarSubgroup F (Minus.Space F (n - 1))
      (Minus.quadraticForm F n))).comp f).range ≤ residualImage p K)
    (hcomp : ∃ b : Minus.Omega F (Minus.Space F ((n - 2) - 1))
      (Minus.quadraticForm F (n - 2)), orderOf b = 3) :
    ∃ E : Subgroup (residual p K), IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := hcomp
  have hQ : ∃ v, Minus.quadraticForm F n v ≠ 0 := by
    refine ⟨(0, (1, 0)), ?_⟩
    simp [Minus.quadraticForm, Minus.form_apply, Minus.plane_apply]
  exact residual_nine_of_productMap p K
    ((QuotientGroup.mk' (Minus.scalarSubgroup F (Minus.Space F (n - 1))
      (Minus.quadraticForm F n))).comp f)
    (Fundamental.omegaProjective_kernel_square (Minus.quadraticForm F n) hQ f hf) hJ
    Fundamental.cubicSL b Fundamental.cubicSL_order hb

/-- In dimension seven the complementary cubic is supplied by Ω₃ itself. -/
theorem seven_residual_nine_of_blocks {p : ℕ}
    (K : Subgroup (POmegaOdd 3 F))
    (f : Matrix.SpecialLinearGroup (Fin 2) F × OmegaOdd 1 F →* OmegaOdd 3 F)
    (hf : Function.Injective f)
    (hJ : ((projectiveElementaryMap (formB 3 F)).comp f).range ≤ residualImage p K) :
    ∃ E : Subgroup (residual p K), IsElementaryAbelian 3 E ∧ Nat.card E = 9 :=
  odd_residual_nine_of_blocks K f hf hJ Fundamental.oddRankOne_exists_cubic

/-- In split dimension eight the complementary cubic comes from a marked SL₂. -/
theorem eightPlus_residual_nine_of_blocks {p : ℕ}
    (K : Subgroup (POmegaPlus 4 F))
    (f : Matrix.SpecialLinearGroup (Fin 2) F × OmegaPlus 2 F →* OmegaPlus 4 F)
    (hf : Function.Injective f)
    (hJ : ((projectiveElementaryMap (formD 4 F)).comp f).range ≤ residualImage p K) :
    ∃ E : Subgroup (residual p K), IsElementaryAbelian 3 E ∧ Nat.card E = 9 :=
  plus_residual_nine_of_blocks K f hf hJ Fundamental.plusRankTwo_exists_cubic

end CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.Orthogonal
