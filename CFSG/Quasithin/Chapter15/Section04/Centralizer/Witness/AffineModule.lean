module

public import Theory.Representation.AffineNine.Model
public import Theory.Representation.AffineNine.CubicBound
public import Theory.Representation.AffineNine.Transport
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.UniformWeights
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeFive
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The affine-nine source consumer in 15.4.10

The source acts on `H⁺ = H/C_H(W)` and obtains the genuine affine-nine
model. The preceding local reduction supplies an isomorphism from that
quotient to the concrete semidirect-product model, while 15.4.2(4) supplies
the cubic-ratio bound at two. This module records the exact transport and
contradiction on the original normal-closure representation. The strict affine
representation estimate is proved in `Theory.Representation.AffineNine.CubicBound`,
with all weight and finite-orbit premises discharged for both actual models.
Faithfulness of the source representation follows from its exact centralizer
kernel. The final consumer applies the full earlier 15.4.2(4) implication with
its original reducedness, core, containment and unique-overgroup conditions.
Their source construction, and the marked affine isomorphism, remain with the
15.4.10 assembly owner.

Source: Aschbacher--Smith, combined manuscript, Lemma 15.4.10, printed p.1159.
-/

public section
open scoped ENNReal
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness

open Representation
open Representation.BinaryOffender

variable {D E V : Type*} [Group D] [Group E] [Finite D] [Finite E]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal 15.4.10 contradiction after transporting the source action
along the actual affine model isomorphism. `hsource` is the genuine
15.4.2(4) cubic-ratio bound on the original quotient action; `hstrict` is the
strict affine-nine estimate for its transported representation. -/
public theorem affineNine_source_contradiction
    (rho : Representation (ZMod 2) D V) (e : E ≃* D)
    (hsource : BinaryOffender.cubicRatio rho ≤ 2)
    (hstrict : ¬ BinaryOffender.cubicRatio (rho.comp e.toMonoidHom) ≤ 2) : False := by
  exact hstrict (BinaryOffender.cubicRatio_comp_equiv_le_two rho e hsource)

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness
open Representation Representation.BinaryOffender Representation.AffineNine Subgroup
open Theory.GroupTheory

variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Pull back the original faithful action through either actual affine model.
The strict estimate has no remaining weight or orbit premises. -/
theorem affineNine_cubicRatio_not_le_two_of_model
    (rho : Representation (ZMod 2) D V) (hfaith : Function.Injective rho)
    (hmodel : Nonempty (D ≃* Special) ∨ Nonempty (D ≃* Full)) :
    ¬ cubicRatio rho ≤ 2 := by
  intro hsource
  rcases hmodel with hs | hf
  · obtain ⟨e⟩ := hs
    exact special_cubicRatio_not_le_two (rho.comp e.symm.toMonoidHom)
      (hfaith.comp e.symm.injective) (cubicRatio_comp_equiv_le_two rho e.symm hsource)
  · obtain ⟨e⟩ := hf
    exact full_cubicRatio_not_le_two (rho.comp e.symm.toMonoidHom)
      (hfaith.comp e.symm.injective) (cubicRatio_comp_equiv_le_two rho e.symm hsource)

variable {G : Type*} [Group G] [Finite G]

/-- The literal action on W = ⟨Z^H⟩ by H/C_H(W) has strict cubic ratio
whenever the preceding source reduction supplies either natural affine model.
Faithfulness is proved from the centralizer quotient itself. -/
theorem affineNine_normalClosure_cubicRatio_not_le_two (H Z : Subgroup G)
    [IsElementaryAbelian 2 (normalClosure (Z.subgroupOf H : Set H))]
    (hmodel : let W := normalClosure (Z.subgroupOf H : Set H)
      let C := centralizer (W : Set H)
      Nonempty ((H ⧸ C) ≃* Special) ∨ Nonempty ((H ⧸ C) ≃* Full)) :
    let W := normalClosure (Z.subgroupOf H : Set H)
    let C := centralizer (W : Set H)
    ¬ cubicRatio (NormalElementaryQuotient.representation W
      (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
      (QuotientGroup.ker_mk' C)) ≤ 2 := by
  let W := normalClosure (Z.subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  exact affineNine_cubicRatio_not_le_two_of_model _
    (NormalElementaryQuotient.representation_injective W (QuotientGroup.mk' C)
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) hmodel

/-- Apply genuine 15.4.2(4) to the original normal-closure representation and
contradict its affine-nine estimate. The source owner supplies reducedness,
the core identity, uniqueness, and the marked affine model from its preceding
local reductions; the weight and orbit estimates are completely discharged. -/
theorem affineNine_source_1542_four_contradiction
    (T : Sylow 2 G) (h : MaximalPrimeSource.SourceHypotheses T)
    (h44 : MaximalPrimeFive.Earlier1542Four (G := G))
    (H Z M : Subgroup G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hM : IsMaximalTwoLocal M) (hHM : H ≤ M)
    (huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N → N = M)
    (hred : IsPReduced 2 (normalClosure (Z.subgroupOf H : Set H)))
    (hcore : (T : Subgroup G).subgroupOf H ⊓
      centralizer (normalClosure (Z.subgroupOf H : Set H) : Set H) =
      (centralizer (normalClosure (Z.subgroupOf H : Set H) : Set H)).pCoreIn 2)
    (hWM : (normalClosure (Z.subgroupOf H : Set H)).map H.subtype ≤ M.pCoreIn 2)
    (hmodel : let W := normalClosure (Z.subgroupOf H : Set H)
      let C := centralizer (W : Set H)
      Nonempty ((H ⧸ C) ≃* Special) ∨ Nonempty ((H ⧸ C) ≃* Full)) : False := by
  let W := normalClosure (Z.subgroupOf H : Set H)
  let : IsElementaryAbelian 2 W := hred.elementary
  exact affineNine_normalClosure_cubicRatio_not_le_two H Z hmodel
    (h44 T h H M hH hM hHM huniq W hred hcore hWM)
end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness
