module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Abelian outer groups of the external linear components

For PSL₂ over a binary field, proved semilinear coverage makes the actual
outer quotient an image of the cyclic field automorphism group. For PSL₃
in odd binary degree, cubing is bijective on the field units. A scalar
determinant correction therefore makes every linear conjugation inner.
The proved opposite-pair normalization and root orientation supply full
automorphism coverage; the remaining field and inverse-transpose generators
commute, so the actual outer quotient is abelian.

Both conclusions transport through the genuine matrix-group isomorphisms in
`ClassicalGroup.IsPSL`. No coverage premise remains, and neither quasisimplicity
nor centerlessness is needed for these intrinsic model facts. They supply the
two linear cases of the outer-group input to the source cubic generation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20(a), printed p.954; GLS3 Theorem 2.5.12(a–e) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`. The imported field transport retains its
ATLAS attribution and license.
-/

public section

open scoped MatrixGroups IsMulCommutative
open Matrix Subgroup
open Matrix.PSL3.OuterSolvable

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.OuterAutomorphisms

private theorem linearConj_scalar {F : Type*} [Field F] (u : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) y
  change QuotientGroup.mk (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) u) x) =
    QuotientGroup.mk x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

private theorem innerDiagonal_eq_inner_of_odd {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Odd n) :
    innerDiagonal F = MulAut.innerSubgroup PSL(3,F) := by
  apply le_antisymm _ (inner_le_innerDiagonal F)
  rintro _ ⟨g, rfl⟩
  have hcop : (Nat.card Fˣ).Coprime 3 := by
    rw [Nat.card_units, hF]
    exact (Nat.BinaryTorusParity.coprime_three_sub_one hn).symm
  obtain ⟨d, hd⟩ := hcop.pow_left_bijective.surjective (GeneralLinearGroup.det g)⁻¹
  change d ^ 3 = (GeneralLinearGroup.det g)⁻¹ at hd
  let x : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker :=
    ⟨GeneralLinearGroup.scalar (Fin 3) d * g, by
      change GeneralLinearGroup.det _ = 1
      rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hd, inv_mul_cancel]⟩
  refine ⟨QuotientGroup.mk ((slEquivDetKernel F).symm x), ?_⟩
  rw [← linearConj_toGL, slEquivDetKernel_symm_toGL]
  change linearConj F (GeneralLinearGroup.scalar (Fin 3) d * g) = _
  rw [map_mul, linearConj_scalar, one_mul]

private theorem field_commute_graph {F : Type*} [Field F] (τ : F ≃+* F) :
    Commute (fieldAction F τ) (graph F) := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, graph_mk]
    rw [map_inv]
    congr 2

private theorem psl3_outer_abelian {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : 1 < n) (hodd : Odd n) (hF : Nat.card F = 2 ^ n) :
    IsMulCommutative (MulAut.Outer PSL(3,F)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  let f := q.comp (fieldAction F)
  let c := q (graph F)
  let S : Set (MulAut.Outer PSL(3,F)) := Set.range f ∪ {c}
  have hc : standard F = ⊤ :=
    Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation F (by omega) hF
      (Matrix.PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots F hn hF)
  have hmap : (standard F).map q = ⊤ := by
    rw [hc, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hgen : closure S = ⊤ := by
    rw [standard, Subgroup.map_sup, Subgroup.map_sup,
      innerDiagonal_eq_inner_of_odd hF hodd, QuotientGroup.map_mk'_self, bot_sup_eq,
      ← MonoidHom.range_comp, MonoidHom.map_zpowers] at hmap
    change f.range ⊔ zpowers c = ⊤ at hmap
    rw [← hmap]
    dsimp only [S]
    rw [Subgroup.closure_union, ← MonoidHom.coe_range, Subgroup.closure_eq,
      ← Subgroup.zpowers_eq_closure]
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x (⟨σ, rfl⟩ | hx) y (⟨τ, rfl⟩ | hy)
    · exact (f.map_mul σ τ).symm.trans ((congrArg f (mul_comm σ τ)).trans (f.map_mul τ σ))
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact ((field_commute_graph σ).map q).eq
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact ((field_commute_graph τ).map q).eq.symm
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  let := Subgroup.isMulCommutative_closure hcomm
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : x ∈ closure S := hgen.symm ▸ mem_top x
  have hy : y ∈ closure S := hgen.symm ▸ mem_top y
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : closure S) ⟨y, hy⟩)

private theorem outer_commutative_of_equiv {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) [IsMulCommutative (MulAut.Outer E)] :
    IsMulCommutative (MulAut.Outer D) := by
  refine ⟨⟨fun x y => (MulAut.outerCongr e).injective ?_⟩⟩
  simp only [map_mul, mul_comm]

/-- The actual outer automorphism group in the `ExternalCarrier.linearTwo`
case is abelian, with all semilinear coverage and isomorphism transport proved. -/
theorem linearTwo_outer_isMulCommutative {D : Type*} [Group D]
    {n : ℕ} (hn : 1 < n) (h : ClassicalGroup.IsPSL D 2 (2 ^ n)) :
    IsMulCommutative (MulAut.Outer D) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, show n ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  let : IsCyclic (MulAut.Outer PSL(2,F)) :=
    Theory.PSL2.OuterSolvable.outer_isCyclic_of_field_coverage
      BenderSuzuki.ZD.Linear.semilinear_coverage
  exact outer_commutative_of_equiv e

/-- The actual outer automorphism group in the `ExternalCarrier.linearThree`
case is abelian: odd degree removes the diagonal part, and field and graph commute. -/
theorem linearThree_outer_isMulCommutative {D : Type*} [Group D]
    {n : ℕ} (hn : 1 < n) (hodd : Odd n) (h : ClassicalGroup.IsPSL D 3 (2 ^ n)) :
    IsMulCommutative (MulAut.Outer D) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := psl3_outer_abelian hn hodd hF
  exact outer_commutative_of_equiv e

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.OuterAutomorphisms
