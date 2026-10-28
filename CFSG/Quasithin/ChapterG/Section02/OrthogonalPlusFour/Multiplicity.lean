module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Assembly

/-!
# Invariance and transport for the common multiplicity in G.2.6

The middle layer is the actual preimage of the L-fixed space in S/V_L.
Consequently T preserves it, even before the additional Chapter 15
Omega-center hypothesis collapses it to V_L. Relative indices then show
that an actual T-conjugacy between the two factor preimages forces equal
dimensions of their commutator images, hence equal natural multiplicities.

The factor conjugacy is an explicit additional premise here. It is not
deduced from the marked quadratic action, and this module does not claim
the unconditional common-multiplicity clause of G.2.6(5).

Source: Aschbacher–Smith, G.2.6, printed p.336/PDF p.347; the common
integer is also required in 15.3.54(4) and 15.3.56(2), pp.1146–1147.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair

namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

namespace Hypothesis
variable (d : Hypothesis D g)
include d

/-- T normalizes the actual two-core of I=LU. -/
theorem T_normalizes_core : D.T ≤ normalizer (D.S g : Set G) := by
  have hTI : D.T ≤ normalizer (D.I g : Set G) :=
    (show D.T ≤ D.LT from le_sup_right).trans
      (d.LT_normalizes_I_of_star d.star_I_eq_star_LU)
  exact hTI.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (D.I g)))

end Hypothesis

section ModuleData
variable [((S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (Quotient D g)]
variable {d : Hypothesis D g}

/-- No fixed vector above S₂ identifies S₂ intrinsically, without using
the later Chapter 15 central collapse. -/
theorem SourceModuleData.middle_eq_fixed_preimage (f : SourceModuleData d) :
    S₂ D g = commutatorPreimage (D.S g) D.L D.VL := by
  have hLI : D.L ≤ D.I g := d.I_eq_LU.symm ▸ le_sup_left
  have hNE : D.I g ≤ normalizer (S₂ D g : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (d.normal_layers.2.2.2.2.trans le_sup_left)
  have hno := Chapter15Collapse.fixed_preimage_le_of_section f.conjugation
    ((pCoreIn_le 2 (D.I g)).trans hNE) hLI (by
      intro v hv
      have hm : v ∈ fixedSpace (f.representation.comp (moduleProjection d.quotientSymmetricEquiv))
          (D.L.subgroupOf (D.I g)) := by
        intro l
        exact hv ⟨l, l.property⟩
      rwa [f.odd_fixed, Submodule.mem_bot] at hm)
  apply le_antisymm
  · exact le_commutatorPreimage d.normal_layers.2.1
      ((commutator_mono le_rfl hLI).trans d.normal_layers.2.2.2.2)
  · apply le_trans ?_ hno
    exact le_commutatorPreimage (commutatorPreimage_le _ _ _)
      ((commutator_commutatorPreimage_le _ _ _
        ((pCoreIn_le 2 (D.I g)).trans d.I_normalizes_VL)).trans le_sup_left)

omit [IsElementaryAbelian 2 (Quotient D g)] in
/-- The order of a literal quotient image is an ambient relative index.
In particular this does not require S₂ to be contained in that subgroup. -/
theorem quotientImage_card_relIndex (d : Hypothesis D g)
    (A : Subgroup G) (hA : A ≤ D.S g) :
    Nat.card (quotientImage D g A) = (S₂ D g).relIndex A := by
  change Nat.card ((A.subgroupOf (D.S g)).map
    (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)))) = _
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  rw [← relIndex_map_map_of_injective _ _ (D.S g).subtype_injective,
    map_subgroupOf_eq_of_le d.normal_layers.2.1, map_subgroupOf_eq_of_le hA]

/-- Equality of the two actual image orders detects common multiplicity. -/
theorem SourceModuleData.common_of_image_card (f : SourceModuleData d)
    (hc : Nat.card (quotientImage D g
        ⁅D.S g, factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor⁆) =
      Nat.card (quotientImage D g
        ⁅D.S g, factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor⁆)) :
    f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity := by
  apply f.commonMultiplicity_iff_finrank.mpr
  rw [f.left_image, f.right_image, binarySubgroup_card, binarySubgroup_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := f.decomposition.left.toSubmodule),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := f.decomposition.right.toSubmodule),
    Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc

end ModuleData

namespace Hypothesis
variable (d : Hypothesis D g)
include d

/-- The middle layer is intrinsic to S,L,V_L and is therefore T-invariant. -/
theorem T_normalizes_middle : D.T ≤ normalizer (S₂ D g : Set G) := by
  let := moduleSectionNormal d d.I_eq_LU
  let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
  obtain ⟨f⟩ := d.source_module_data
  rw [f.middle_eq_fixed_preimage]
  exact commutatorPreimage_normalized _ _ _ _
    ((pCoreIn_le 2 (D.I g)).trans d.I_normalizes_VL)
    d.T_normalizes_core d.base.T_normalizes_L (Chapter15Collapse.T_normalizes_natural d)

end Hypothesis

/-- A precise additional group-theoretic witness for the interchange route.
Right conjugation is the source convention. No vector-space map or
multiplicity equality is included in this condition. -/
def FactorExchange (d : Hypothesis D g) : Prop :=
  ∃ t ∈ D.T,
    conjugate (factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor) t =
      factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor

section ModuleData
variable [((S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (Quotient D g)]
variable {d : Hypothesis D g}

/-- Conjugation of the actual factors transports their commutator images
through the actual middle layer, proving equality of multiplicities. -/
theorem SourceModuleData.common_of_factorExchange (f : SourceModuleData d)
    (h : FactorExchange d) :
    f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity := by
  obtain ⟨t, ht, hfactor⟩ := h
  let c := (MulAut.conj t⁻¹).toMonoidHom
  have hS : (D.S g).map c = D.S g :=
    mem_normalizer_iff_map_conj_eq.mp (d.T_normalizes_core (D.T.inv_mem ht))
  have hE : (S₂ D g).map c = S₂ D g :=
    mem_normalizer_iff_map_conj_eq.mp (d.T_normalizes_middle (D.T.inv_mem ht))
  have hA (K : Subgroup (S₃ × S₃)) :
      ⁅D.S g, factorPreimage d.quotientSymmetricEquiv K⁆ ≤ D.S g :=
    le_normalizer_iff_commutator_le_left.mp
      ((factorPreimage_le _ K).trans (core_normalized D g))
  apply f.common_of_image_card
  rw [quotientImage_card_relIndex d _ (hA _), quotientImage_card_relIndex d _ (hA _)]
  have hc := relIndex_map_map_of_injective (f := c) (S₂ D g)
    ⁅D.S g, factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor⁆
    (MulAut.conj t⁻¹).injective
  change (factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor).map c =
    factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor at hfactor
  rw [map_commutator, hS, hE, hfactor] at hc
  exact hc.symm

/-- The factor-interchange route feeds the genuine residual-factor consumer. -/
def SourceModuleData.factorConclusion_of_factorExchange (f : SourceModuleData d)
    (h : FactorExchange d) :
    Chapter15Collapse.FactorModuleConclusion (D.I g) (D.S g) (S₂ D g) D.L
      (moduleProjection d.quotientSymmetricEquiv) f.representation :=
  f.factorConclusion (f.common_of_factorExchange h)

end ModuleData

/-- The decomposition is constructed from the source data. Only the actual
factor conjugacy remains an extra premise of this conditional route. -/
theorem Hypothesis.source_common_of_factorExchange (d : Hypothesis D g)
    (h : FactorExchange d) :
    letI := moduleSectionNormal d d.I_eq_LU
    letI := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
    ∃ f : SourceModuleData d,
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity := by
  let := moduleSectionNormal d d.I_eq_LU
  let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
  obtain ⟨f⟩ := d.source_module_data
  exact ⟨f, f.common_of_factorExchange h⟩

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
