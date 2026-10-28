module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Source.Normalizers

/-!
# The original fusion conclusion of 14.7.68

The proved residual normalizer theorem recovers every conjugator returning
the original fixed-space preimage U₀ to the centralizer of z. Consequently
z has no other ambient conjugate in U₀, and N_G(U₀)=H. This part of 14.7.68
uses no fixed-component quotient classification or C.2.7 input: C_G(z)=H
is already part of the original source data.

The genuine earlier structure, faithful classification, A₅ module list,
14.7.10 and 14.7.31 remain their separately owned source inputs.
Source: Aschbacher–Smith 14.7.67(4) and 14.7.68(1), printed pp.1070–1071.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
  (baumann : LocalControl.Earlier14710.{u}) (weakClosure : Theorem14731.{u})
include structural faithful modules baumann weakClosure

/-- Source 14.7.68(1), without a fusion or fixed-centralizer premise. -/
theorem Data.fusion_z_of_known_simple_source :
    {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z} :=
  d.fusion_z_of_normalizer_K
    (d.normalizer_K_eq_H_of_known_simple_source structural faithful modules baumann weakClosure).1

/-- The normalizer of the literal fixed-space preimage. -/
theorem Data.normalizer_U₀_of_known_simple_source :
    normalizer (d.U₀ : Set G) = F.H :=
  d.normalizer_U₀_eq_of_normalizer_K
    (d.normalizer_K_eq_H_of_known_simple_source structural faithful modules baumann weakClosure).1

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
