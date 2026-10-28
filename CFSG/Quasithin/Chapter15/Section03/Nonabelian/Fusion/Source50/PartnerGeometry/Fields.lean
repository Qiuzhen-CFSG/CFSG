module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PowerInputs

/-!
# The source-56 output consumed by recognition assembly

This record records the conclusions still to be supplied by the source-56
geometry on its literal X=Fʸ. It is an output interface, not an additional
hypothesis of the final source theorem. The original earlier-source inputs
are assembled separately; their power-form fields are discharged here by
source55. The later Partner.EarlierGeometry uses the same chosen y and t.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition Recognition.NormalReduction
variable {G : Type*} [Group G] (T Z ZS V : Subgroup G) (s : ℕ)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

structure RecognitionFields where
  Y₁ : Subgroup G
  y : G
  t : G
  X_le_T : partnerX Z ZS y ≤ T
  t_mem_T : t ∈ T
  t_outside : t ∉ closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))
  fixed_line :
    letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    FixedPoints.subgroup
      ((partnerX Z ZS y ⊔ zpowers t).subgroupOf (centralizerH Z))
      (VectorQuotient Z ZS) = distinguishedLine Z ZS
  dimension : Module.finrank (ZMod 2) (Space Z ZS) = 2*(s+2)
  Vstar_le_Xstar : actorImage Z V ≤ actorImage Z (partnerX Z ZS y)
  elementary : IsElementaryAbelian 2 (actorImage Z (partnerX Z ZS y))
  card_actor : Nat.card (actorImage Z (partnerX Z ZS y)) = 2^(s+1)
  extraspecial_product : 0 < s → ∃ P : Subgroup (ActorQuotient Z),
    IsExtraspecial 2 P ∧ ∃ X : Subgroup P, IsElementaryAbelian 2 X ∧
      Nat.card X = 2 ^ (s + 1) ∧
      (center P).map P.subtype = actorImage Z V

namespace RecognitionFields
variable {T Z ZS V s}

/-- The source fixed-line actor lies in the original T. -/
theorem J_le_T (r : RecognitionFields T Z ZS V s) :
    ((partnerX Z ZS r.y ⊔ zpowers r.t).subgroupOf (centralizerH Z)) ≤
      T.subgroupOf (centralizerH Z) :=
  comap_mono (sup_le r.X_le_T (zpowers_le.mpr r.t_mem_T))

/-- Actual recognition and power consumers after the independent source
fields have been assembled on this same Sylow subgroup. -/
theorem action_power [Finite G] [IsElementaryAbelian 2 V]
    {M : Subgroup G} {C : GroupClass} {v : ActorQuotient Z}
    (r : RecognitionFields T Z ZS V s)
    (d : EarlierSourceInputs Z ZS V M C v s) (hT : (d.T : Subgroup G) = T)
    (hextra : IsExtraspecial 2 (closureU Z ZS))
    (hcenter : center (closureU Z ZS) = Z.subgroupOf (closureU Z ZS)) :
    ∃ a : EarlierActionInputs d, a.X = partnerX Z ZS r.y ∧ EarlierPowerInputs d a :=
  action_power_inputs d (partnerX Z ZS r.y) (hT.symm ▸ r.X_le_T)
    r.Vstar_le_Xstar r.elementary r.card_actor hextra hcenter

end RecognitionFields
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
