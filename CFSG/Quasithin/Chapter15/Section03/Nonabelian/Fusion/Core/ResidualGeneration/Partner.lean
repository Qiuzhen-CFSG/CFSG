module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.Transport
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.ActorCalculation

/-!
# The marked-partner lift in 15.3.59

The earlier-source inputs retain the actual Sylow subgroup of H, the
literal partners and quotient maps, and both full module identifications.
The J-normalizer calculation proves normalization of XU. Its actor kernel
is U, so the marked actor commutator identity lifts X into K. The
order-eight clause of 15.3.56(6) then exhausts the order-eight residual
Sylow actor image.

`EarlierGeometry.partner_conclusions` discharges the actor identity through
the actual recognized and marked actions. Only the explicitly separate
residual-action conclusions U ≤ K and the residual Sylow actor order remain
inputs. The original conditional lift is preserved for other callers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56–59, printed pp.1147–1150.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G]

/-- Precisely the earlier local information used by the marked calculation.
The residual containment U ≤ K and residual Sylow actor order are supplied
separately by the residual-action calculation. The remaining commutator
identity is not a field of this record. -/
structure EarlierGeometry (T Z ZS V Y₁ : Subgroup G) (y t : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] where
  sylow : Sylow 2 (centralizerH Z)
  sylow_map : (sylow : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T
  X_le_T : partnerX Z ZS y ≤ T
  Z_le_ZS : Z ≤ ZS
  ZS_le_H : ZS ≤ centralizerH Z
  U_le_Q : closureU Z ZS ≤ coreQ Z
  X_inf_Q : partnerX Z ZS y ⊓ coreQ Z = intersectionE Z ZS y
  y_mem : y ∈ Y₁
  y_outside : y ∉ Stellmacher.twoCoreAmbient Y₁
  V₀_eq : lineV₀ Z Y₁ = Z ⊔ rightConjugate Z y
  V₀_le_U : lineV₀ Z Y₁ ≤ closureU Z ZS
  J_normalizer : normalizer (lineV₀ Z Y₁ : Set G) ≤ normalizer (pairI Z ZS y : Set G)
  E_normalizer : normalizer (lineV₀ Z Y₁ : Set G) ≤
    normalizer (intersectionE Z ZS y : Set G)
  J_core : pairP Z ZS y = intersectionF Z ZS y ⊔ partnerX Z ZS y
  actor_kernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)
  recognized : RecognizedAction T Z ZS V t
  marked : MarkedAction Z ZS (lineV₀ Z Y₁) y t
    (X_le_T.trans (sylow_map ▸ map_subtype_le (sylow : Subgroup (centralizerH Z))))
  actor_pair_card : Nat.card (actorImage Z
    (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t)) = 8

namespace EarlierGeometry
variable {T Z ZS V Y₁ : Subgroup G} {y t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- Containment in H follows from the actual supplied Sylow arrangement. -/
theorem T_le_H (d : EarlierGeometry T Z ZS V Y₁ y t) : T ≤ centralizerH Z :=
  d.sylow_map ▸ map_subtype_le (d.sylow : Subgroup (centralizerH Z))

/-- The marked line contains the denominator Z of the vector quotient. -/
theorem Z_le_V₀ (d : EarlierGeometry T Z ZS V Y₁ y t) : Z ≤ lineV₀ Z Y₁ := by
  rw [d.V₀_eq]
  exact le_sup_left

/-- Conditional lift and actor generation for a supplied actor identity.
`partner_conclusions` below discharges that identity from the markings. -/
theorem partner_conclusions_of_actor_commutator [Finite G]
    (d : EarlierGeometry T Z ZS V Y₁ y t)
    (hUK : closureU Z ZS ≤ residualK Z)
    (hRcard : Nat.card (actorImage Z (residualSylow T Z)) = 8)
    (himage : actorImage Z (partnerX Z ZS y) =
      ⁅actorImage Z (partnerX Z ZS y), actorImage Z (normalizerResidual Z (lineV₀ Z Y₁))⁆) :
    partnerX Z ZS y ≤ residualK Z ∧
      actorImage Z (residualSylow T Z) ≤ actorImage Z
        (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t) := by
  have hX := partnerX_le_residual_of_normalizer_actor_commutator Z ZS (lineV₀ Z Y₁) y
    (d.X_le_T.trans d.T_le_H) hUK d.U_le_Q d.X_inf_Q d.J_normalizer d.J_core himage
  exact ⟨hX, residualSylow_actor_generated T Z ZS y t d.T_le_H d.recognized.t_mem
    d.X_le_T hX hRcard d.actor_pair_card⟩

/-- The earlier full markings give the actor commutator identity for the literal
relative normalizer H ∩ N_G(V₀). Its two-residual lies in K and normalizes XU;
normalization of X itself is not required. -/
theorem actor_commutator [Finite G] (d : EarlierGeometry T Z ZS V Y₁ y t) :
    actorImage Z (partnerX Z ZS y) =
      ⁅actorImage Z (partnerX Z ZS y),
        actorImage Z (normalizerResidual Z (lineV₀ Z Y₁))⁆ :=
  marked_actor_commutator d.recognized (d.X_le_T.trans d.T_le_H) d.marked
    d.actor_kernel d.Z_le_V₀ d.V₀_le_U

/-- The marked-partner calculation in 15.3.59: X lies in K, and the actors of
X and Xᵗ generate the residual Sylow actor image. All marked-action obligations
are discharged; the two separate residual-action conclusions remain explicit. -/
theorem partner_conclusions [Finite G]
    (d : EarlierGeometry T Z ZS V Y₁ y t)
    (hUK : closureU Z ZS ≤ residualK Z)
    (hRcard : Nat.card (actorImage Z (residualSylow T Z)) = 8) :
    partnerX Z ZS y ≤ residualK Z ∧
      actorImage Z (residualSylow T Z) ≤ actorImage Z
        (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t) :=
  d.partner_conclusions_of_actor_commutator hUK hRcard d.actor_commutator

end EarlierGeometry
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
