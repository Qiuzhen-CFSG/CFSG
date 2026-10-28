module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer


/-!
# Lifting the residual to the unquotiented point centralizer

Suppose D centralizes V₁ and [V₂,D] lies in the elementary binary layer V₁.
The commutator identity shows that every square in D centralizes V₂. Thus
its action on V₂ has a two-group image and O²(D) centralizes V₂. If D
contains C_H(V₂), monotonicity and idempotence of the residual give equality
of their embedded residuals. Mapping through the actual actor homomorphism
then computes the residual image without identifying the full centralizers.

This is the centralizer-lifting step in Aschbacher–Smith 14.7.55(6), combined
manuscript (1 March 2004), printed p.1066. H here is the source local group,
not the ambient simple group. The concrete parabolic quotient, commutator
span and three-line orbit calculations remain separate source obligations.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
open Subgroup
open scoped commutatorElement
variable {H J : Type*} [Group H] [Group J] [Finite H]

omit [Finite H] in
/-- A group fixing both layers of a central binary extension has an elementary
binary action on the extension: every square centralizes it. -/
theorem square_centralizes_of_binary_layer (V₂ V₁ D : Subgroup H)
    [IsElementaryAbelian 2 V₁]
    (hcomm : ⁅V₂,D⁆ ≤ V₁) (hcentral : D ≤ centralizer (V₁ : Set H))
    (d : D) : (d : H) ^ 2 ∈ centralizer (V₂ : Set H) := by
  rw [mem_centralizer_iff]
  intro v hv
  have hc : ⁅(d : H),v⁆ ∈ V₁ := by
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator d.property hv)
  have hfix : (d : H) * ⁅(d : H),v⁆ * (d : H)⁻¹ = ⁅(d : H),v⁆ := by
    have hh := (mem_centralizer_iff.mp (hcentral d.property)) _ hc
    rw [← hh]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hpow : ⁅(d : H),v⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc
  have hh : ⁅(d : H)^2,v⁆ = 1 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hfix, ← pow_two, hpow]
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm

omit [Finite H] in
/-- The two-residual of the quotient-point preimage centralizes the original
unquotiented `V₂`. Only relative normality is used. -/
theorem residual_le_unquotiented_centralizer (V₂ V₁ D : Subgroup H)
    [IsElementaryAbelian 2 V₁] (hV₁ : V₁ ≤ V₂)
    (hcomm : ⁅V₂,D⁆ ≤ V₁) (hcentral : D ≤ centralizer (V₁ : Set H)) :
    (pResidual 2 D).map D.subtype ≤ centralizer (V₂ : Set H) := by
  have hn : D ≤ normalizer V₂ :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hV₁)
  let C := (centralizer (V₂ : Set H)).subgroupOf D
  let a : D →* MulAut V₂ := V₂.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hk : a.ker = C := by
    ext d
    rw [MonoidHom.mem_ker]
    change V₂.normalizerMonoidHom ⟨(d : H), hn d.property⟩ = 1 ↔
      (d : H) ∈ centralizer (V₂ : Set H)
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
    rfl
  let : C.Normal := hk ▸ inferInstanceAs a.ker.Normal
  have hp : IsPGroup 2 (D ⧸ C) := by
    intro x
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective C x
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact square_centralizes_of_binary_layer V₂ V₁ D hcomm hcentral d
  have hr : pResidual 2 D ≤ C := sInf_le ⟨inferInstance,hp⟩
  rintro x ⟨d,hd,rfl⟩
  exact hr hd

/-- The residual may be computed in the quotient-point preimage without
identifying that preimage with `C_H(V₂)`. This is the centralizer-lifting
step needed in 14.7.55(6). Here the ambient group is the source H. -/
theorem source_centralizer_residual_eq (V₂ V₁ D : Subgroup H)
    [IsElementaryAbelian 2 V₁] (hV₁ : V₁ ≤ V₂)
    (hcomm : ⁅V₂,D⁆ ≤ V₁) (hcentral : D ≤ centralizer (V₁ : Set H))
    (hCD : centralizer (V₂ : Set H) ≤ D) :
    (pResidual 2 (centralizer (V₂ : Set H))).map (centralizer (V₂ : Set H)).subtype =
      (pResidual 2 D).map D.subtype := by
  let R := (pResidual 2 D).map D.subtype
  have hRC : R ≤ centralizer (V₂ : Set H) :=
    residual_le_unquotiented_centralizer V₂ V₁ D hV₁ hcomm hcentral
  apply le_antisymm (embedded_pResidual_mono 2 hCD)
  have h := embedded_pResidual_mono 2 hRC
  have hr : pResidual 2 R = ⊤ :=
    (pResidual_eq_top_iff 2 R).mpr (isPPerfect_embedded_pResidual 2 D)
  rw [hr, ← MonoidHom.range_eq_map, R.range_subtype] at h
  exact h

/-- Apply the residual equality through the actual actor homomorphism.
The actor image on D is an input; equality of the full centralizer image
with a quotient-point stabilizer is neither assumed nor inferred. -/
theorem source_centralizer_residual_image (V₂ V₁ D : Subgroup H)
    [IsElementaryAbelian 2 V₁] (hV₁ : V₁ ≤ V₂)
    (hcomm : ⁅V₂,D⁆ ≤ V₁) (hcentral : D ≤ centralizer (V₁ : Set H))
    (hCD : centralizer (V₂ : Set H) ≤ D) (π : H →* J) :
    ((pResidual 2 (centralizer (V₂ : Set H))).map
      (centralizer (V₂ : Set H)).subtype).map π =
      (pResidual 2 (D.map π)).map (D.map π).subtype := by
  rw [source_centralizer_residual_eq V₂ V₁ D hV₁ hcomm hcentral hCD,
    map_embedded_pResidual]
end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
