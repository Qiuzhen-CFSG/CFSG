module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.ModuleContainment
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankThreeNaturalSix
/-!
# The natural-six branch after source residual generation

Use the selected component K=O²(I). Its ambient image is normal in I,
contains the original moved plane in its block module, and is acted on
by the literal second parabolic. The generation equation shows that
parabolic escapes M. This discharges the structural premises of the
natural-six rank-three calculation. Its compatible module and flag marks,
and the actual order-sixteen module case, remain explicit.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterC RankThreeNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))
include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

/-- The residual producer discharges placement, normalization and module containment
in the literal four-dimensional natural-six branch. -/
theorem source_parabolic_residual_naturalSix_rank_three
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (K : Subgroup I) (hKr : K = pResidual 2 I)
    (m : BlockModuleModel (K.map I.subtype) RankThreeNaturalSix.action)
    (hW : Nat.card (RankThreeNaturalSix.sourceModule (K.map I.subtype)) = 16)
    (hplane : ((localModule T M).subgroupOf (RankThreeNaturalSix.sourceModule (K.map I.subtype))).map
      (sourceCoordinatesOfCard (K.map I.subtype) m hW).toMonoidHom = canonicalPlane.toAddSubgroup.toSubgroup)
    (hpoint : ((centralInvolutions T).subgroupOf (RankThreeNaturalSix.sourceModule (K.map I.subtype))).map
      (sourceCoordinatesOfCard (K.map I.subtype) m hW).toMonoidHom = canonicalLine.toAddSubgroup.toSubgroup) :
    IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) I2) ∧
      Nat.card (conjugateSpanBy (localModule T M) I2) = 8 ∧
      primeRank 2 (conjugateSpanBy (localModule T M) I2) = 3 := by
  let C := K.map I.subtype
  have hI2I : I2 ≤ I := le_sup_right.trans hgen.le
  have hI2M : ¬ I2 ≤ M := by
    intro hh
    apply hI.1.2.2.2
    rw [←hgen]
    exact sup_le (sup_le (((map_subtype_le _).trans inf_le_left).trans
      (sourceResidual_le M Mc)) (inf_le_left.trans hM.1.2)) hh
  let : K.Normal := by rw [hKr]; infer_instance
  have hn : (C.subgroupOf I).Normal := by
    change ((K.map I.subtype).comap I.subtype).Normal
    rw [comap_map_eq_self_of_injective I.subtype_injective K]
    infer_instance
  have hmod := source_parabolic_span_le_component_module hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hrank I I2 hI hSI2 hI2H
    hquot2 hout hgen K hKr
  exact source_parabolic_naturalSix_rank_three hG T hempty hM hunique hmany hcard e H hH
    I I2 C (map_subtype_le _) hn hI2I hI2H hI2M m hW
    ((le_conjugateSpanBy _ _).trans hmod.2) hplane hpoint

end CFSG.Quasithin.Chapter14.Section06
