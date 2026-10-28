module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Actions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceAction.NaturalPlane
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceAction.LocalSubgroups

/-!
# Earlier local identities and compatible source markings

These data retain the literal point core, line normalizer, residual and
conjugate spans from 13.5.4 and 13.7.3. The markings identify the actual
local quotient with S₃ and the actual seed quotient V/V₂ with its natural
module, intertwining conjugation. They contain no action on U₂/V₂,
no centrality of the G₂-core there, and no doubling conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4(1),(2),(6), 13.7.3(6), and 13.8.6, printed p.948.
-/

public section

open Subgroup Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
variable {G : Type*} [Group G]

/-- Exact earlier local conclusions used by the construction. The point core,
the line normalizer, K₂, and U₂ are their literal ambient constructions.
There are no representation-theoretic conclusions among these fields. -/
structure LocalData (H V V₁ V₂ V₃ I₂ L₂ : Subgroup G) where
  sylow : Sylow 2 G
  sylow_le_H : (sylow : Subgroup G) ≤ H
  H_le_G1 : H ≤ normalizer (V₁ : Set G)
  sylow_le_G2 : (sylow : Subgroup G) ≤ normalizer (V₂ : Set G)
  flag12 : V₁ ≤ V₂
  flag23 : V₂ ≤ V₃
  flag3V : V₃ ≤ V
  normalClosure : I₂ = conjugateSpanBy ((normalizer (V₁ : Set G)).pCoreIn 2)
    (normalizer (V₂ : Set G))
  residual : L₂ = (pResidual 2 I₂).map I₂.subtype
  product : I₂ = (normalizer (V₁ : Set G)).pCoreIn 2 ⊔ L₂
  centralizer : I₂ ⊓ Subgroup.centralizer (V₂ : Set G) = I₂.pCoreIn 2
  generation : V = conjugateSpanBy V₃ L₂
  point_core_action : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁

namespace LocalData
variable {H V V₁ V₂ V₃ I₂ L₂ : Subgroup G}
variable (d : LocalData H V V₁ V₂ V₃ I₂ L₂)
include d

theorem L2_le_I2 : L₂ ≤ I₂ := d.residual ▸ map_subtype_le _

theorem L2_normalizes_V : L₂ ≤ normalizer (V : Set G) := by
  rw [d.generation]
  exact le_normalizer_conjugateSpanBy _ _

theorem point_core_le_G2 [Finite G] :
    (normalizer (V₁ : Set G)).pCoreIn 2 ≤ normalizer (V₂ : Set G) := by
  have hT₁ := d.sylow_le_H.trans d.H_le_G1
  have h := pCoreIn_le_sylow (normalizer (V₁ : Set G)) (d.sylow.subtype hT₁)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT₁] at h
  exact h.trans d.sylow_le_G2

theorem point_core_commutator [Finite G] :
    ⁅Source.UH H V₃, (normalizer (V₁ : Set G)).pCoreIn 2⁆ ≤ V₁ :=
  (commutator_mono le_rfl
    (point_core_le_Hcore d.sylow H V₁ d.sylow_le_H d.H_le_G1)).trans d.point_core_action

theorem I2_le_G2 [Finite G] : I₂ ≤ normalizer (V₂ : Set G) := by
  rw [d.normalClosure]
  exact conjugateSpanBy_le_self d.point_core_le_G2

theorem normalizes_U2 [Finite G] : I₂ ≤ normalizer (Source.U2 H V V₂ : Set G) :=
  I2_normalizes_U2 H V V₁ V₂ V₃ I₂ L₂ _ (d.flag12.trans d.flag23)
    d.normalClosure d.residual d.product d.point_core_le_G2 d.generation
    d.point_core_commutator

end LocalData

variable (H V V₁ V₂ V₃ I₂ L₂ : Subgroup G)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

/-- The marking consists of genuine quotient and module isomorphisms, with
the images of the source subgroups and the actual conjugation formula.
It does not prescribe the resulting action on U₂/V₂. -/
structure CompatibleMarking (d : LocalData H V V₁ V₂ V₃ I₂ L₂) where
  localEquiv : (I₂ ⧸ pCore 2 I₂) ≃* InvertedCubicTensor.S₃
  cubic_image : (L₂.subgroupOf I₂).map
    (localEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I₂))) =
      zpowers InvertedCubicTensor.cubic
  inverter_image : (((normalizer (V₁ : Set G)).pCoreIn 2).subgroupOf I₂).map
    (localEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I₂))) =
      zpowers InvertedCubicTensor.inverter
  planeEquiv : Additive (SeedQuotient V V₂) ≃ₗ[F] NaturalPlane
  equivariant : ∀ (l : L₂) (b : V),
    planeEquiv (seedClass V V₂
      ⟨(l : G) * (b : G) * (l : G)⁻¹,
        (mem_normalizer_iff.mp (d.L2_normalizes_V l.property) b).mp b.property⟩) =
      BinaryPermutation.coreRepresentation (Fin 3)
        (localEquiv (QuotientGroup.mk' (pCore 2 I₂) ⟨l, d.L2_le_I2 l.property⟩))
        (planeEquiv (seedClass V V₂ b))

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
