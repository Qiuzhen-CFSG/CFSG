module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.Action
public import Theory.Representation.AlternatingFiveLinearTwoObstruction

/-!
# Distinguishing the rank-one and alternating-five module branches

A three-cycle fixes a nonzero vector in the binary A₅ permutation core,
whereas an order-three element of SL₂ in characteristic two fixes no
nonzero natural vector. Apply that checked model calculation to the literal
U_K/C_U_K(K) and the supplied NaturalSection. Thus the S₅ alternative of
E.2.3 cannot be identified with this moving section through faithful actor
and module maps. This includes the field-four case, where the abstract
residual groups are both A₅ and group orders alone do not distinguish them.

The E.2.3 factor comparison still has to construct those maps; the present
lemma does not assume or prove that the Thompson image is K⁺.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.2.3,
printed pp.216–217, and 13.6.18, p.931.
-/

@[expose] public section
open Subgroup Matrix
open scoped IsMulCommutative MatrixGroups
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection Replacement.Action
variable {G : Type*} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
local notation "ρ" => componentRepresentation K L T z v hL hz
local notation "D" => movingSpace K L T z v
local notation "σ" => sectionRepresentation K L T z v hL hz

omit [Finite G] [Finite F] [CharP F 2] in
/-- The prescribed natural coordinates intertwine the actual quotient action,
not merely an action on chosen representatives. -/
theorem naturalSection_intertwines (s : NaturalSection (F := F) ρ D)
    (a : plusImage K L T z v hL hz K) (w : D ⧸ (ρ).invariants.comap (D).subtype) :
    s.coordinates (σ a w) = (s.actor a).val *ᵥ s.coordinates w := by
  induction w using Submodule.Quotient.induction_on with
  | H w => exact s.equivariant a w

omit [Finite G] [Finite F] in
/-- Application to the literal moving section: a faithful alternating-five
permutation constituent is incompatible with its rank-one natural model. -/
theorem movingSection_not_alternatingFive
    (s : NaturalSection (F := F) ρ D)
    (f : alternatingGroup (Fin 5) →* plusImage K L T z v hL hz K)
    (hf : Function.Injective f)
    (e : BinaryPermutation.natural (Fin 5) →ₗ[ZMod 2]
      (D ⧸ (ρ).invariants.comap (D).subtype)) (he : Function.Injective e)
    (hact : ∀ a w, e (BinaryPermutation.naturalRepresentation (Fin 5) a.val w) =
      σ (f a) (e w)) : False := by
  apply BinaryPermutation.AlternatingFiveLinearTwo.no_equivariant_natural_injection
    (s.actor.toMonoidHom.comp f) (s.actor.injective.comp hf)
    (s.coordinates.toAddEquiv.toAddMonoidHom.comp e.toAddHom)
    (s.coordinates.injective.comp he)
  intro a w
  change s.coordinates (e (BinaryPermutation.naturalRepresentation (Fin 5) a.val w)) = _
  rw [hact]
  exact naturalSection_intertwines K L T z v hL hz s (f a) (e w)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
end
