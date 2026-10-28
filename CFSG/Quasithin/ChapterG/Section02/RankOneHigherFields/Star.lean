module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.GeometryData
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.RootGeometry
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.Borel

/-!
# The starred higher-field branch of G.2.3

The literal star quotient acts faithfully on the given natural module.
Pointwise fixation of the marked field line and G.2.2's Frattini bound place
U* inside the actual SL₂ copy L*. Consequently L*U* has that same model.
The full point normalizer maps onto the setwise matrix line stabilizer and
normalizes the nontrivial matrix U-image.

Line-root geometry identifies U* with the full root group, giving its Sylow
property, order, and generation by the original marked pair. The Borel
two-residual calculation then gives L₁* = N_{L*}(U*) and [U*,L₁*] = U*.
These deductions discharge the starred-generation premise of `Reduction`,
yielding I = LU, the source series, and the literal core-quotient comparison.
Only the preceding G.2.2 containment and Frattini conclusions remain inputs.
The central-cover and quotient-module branches of G.2.3 are separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3(1–2), printed pp.333–334, PDF pp.344–345.
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F] {n : ℕ} {g : G}
  (d : Hypothesis D F n g)
include d

/-- The Borel commutators exhaust U*, with the line-root premise discharged. -/
theorem star_commutator_U_L₁ (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U :=
  d.star_U_commutator_L₁ hUT hf (d.matrixU_eq_fixingSubgroup hUT hf)

/-- The original embedded two-residual has the full relative normalizer image. -/
theorem star_L₁_eq_normalizer (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.star D.L₁ = D.star D.L ⊓ normalizer (D.star D.U : Set D.Star) :=
  d.star_L₁_eq_pointNormalizer.trans (d.star_pointNormalizer_eq hUT hf)

/-- Clause (1)'s Sylow witness in the actual product, modeled by `starJoinEquiv`.
The companion `exists_star_U_sylow` gives the witness directly in L*. -/
theorem exists_starJoin_U_sylow (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    ∃ P : Sylow 2 (D.star D.L ⊔ D.star D.U : Subgroup D.Star),
      (P : Subgroup (D.star D.L ⊔ D.star D.U : Subgroup D.Star)).map
        (D.star D.L ⊔ D.star D.U).subtype = D.star D.U := by
  rw [sup_eq_left.mpr (d.star_U_le_star_L hUT hf)]
  exact d.exists_star_U_sylow hUT hf

/-- G.2.3(2), retaining the original marked conjugator. -/
theorem I_eq_LU (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : D.I g = D.L ⊔ D.U :=
  d.I_eq_LU_of_star hUT (d.star_I_eq_star_L hUT hf).ge

/-- The join in clause (2) is the literal subgroup product LU. -/
theorem I_product (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) :=
  d.I_product_of_star hUT (d.star_I_eq_star_L hUT hf).ge

theorem L_le_I (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : D.L ≤ D.I g :=
  d.L_le_I_of_star hUT (d.star_I_eq_star_L hUT hf).ge

/-- No replacement of the source's g is needed in the later quotient branches. -/
theorem g_mem_I (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : g ∈ D.I g :=
  d.g_mem_I_of_star hUT (d.star_I_eq_star_L hUT hf).ge

/-- G.2.3(4–5), with all three normalities relative to the original I. -/
theorem series (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.V ≤ D.S₂ g ∧ D.S₂ g ≤ D.S g ∧
    (D.V.subgroupOf (D.I g)).Normal ∧
    ((D.S₂ g).subgroupOf (D.I g)).Normal ∧
    ((D.S g).subgroupOf (D.I g)).Normal ∧
    D.V ≤ centralizer (D.S g : Set G) ∧
    ⁅D.S₂ g, D.I g⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ g) :=
  d.series_of_star hUT hf (d.star_I_eq_star_L hUT hf).ge

/-- The two-core of the generated group is the kernel of the original star map. -/
theorem S_eq_star_kernel (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.S g = D.I g ⊓ D.LT.pCoreIn 2 :=
  d.S_eq_star_kernel_of_star hUT (d.star_I_eq_star_L hUT hf).ge

/-- The literal I/O₂(I) model after proving starred generation. -/
noncomputable def generatedCoreQuotientEquiv (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* SL(2,F) :=
  d.coreQuotientEquiv hUT (d.star_I_eq_star_L hUT hf)

/-- The quotient comparison uses the actual star projection on I. -/
theorem generatedCoreQuotientEquiv_mk (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (i : D.I g) :
    d.generatedCoreQuotientEquiv hUT hf (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      d.model (d.IStarProjection hUT (d.star_I_eq_star_L hUT hf) i) :=
  d.coreQuotientEquiv_mk hUT (d.star_I_eq_star_L hUT hf) i

/-- The comparison preserves the given marked L-model. -/
theorem generatedCoreQuotientEquiv_on_L (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (l : D.L) :
    d.generatedCoreQuotientEquiv hUT hf (QuotientGroup.mk' (pCore 2 (D.I g))
      (inclusion (d.L_le_I hUT hf) l)) = d.model (starProjection D l) :=
  d.coreQuotientEquiv_on_L hUT (d.star_I_eq_star_L hUT hf) l

/-- The same comparison intertwines the original I-action on V. -/
theorem generatedCoreQuotientEquiv_equivariant (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (i : D.I g) (v : D.V) :
    (d.coordinates ⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT i.property) v).mp v.property⟩).toAdd =
      (d.generatedCoreQuotientEquiv hUT hf
        (QuotientGroup.mk' (pCore 2 (D.I g)) i)).val *ᵥ (d.coordinates v).toAdd :=
  d.coreQuotientEquiv_equivariant hUT (d.star_I_eq_star_L hUT hf) i v

/-- The index used in G.2.3(7), from the literal U-kernel and the root order. -/
theorem W_index (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (D.W g).relIndex D.U = 2 ^ n :=
  (d.W_index_of_star hUT (d.star_I_eq_star_L hUT hf)).trans (d.card_star_U hUT hf)

end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
