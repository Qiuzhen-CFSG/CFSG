module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralImage
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Preserving the original local quotient under a containing center

The faithful-signalizer identity puts Z(L) inside O₂(L). The literal map
from L into any marked I/Z(I) consequently has two-group kernel, and
induces an isomorphism of the intrinsic two-core quotients. Its equation
on original representatives is exported for the embedding comparisons.
No quotient model or irreducibility premise is needed.

Source: Aschbacher--Smith 10.2.9, printed pp.750--751. RankTwo.BinaryThree
uses this map in both exceptional rank-two comparisons.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The faithful local component has two-group center, without a model marking. -/
theorem center_le_twoCore : center L ≤ pCore 2 L := by
  rw [←D.faithful.1.2.2]
  exact (show center L ≤ fittingSubgroup L from
    le_sSup ⟨inferInstance, inferInstance⟩).trans (fitting_le_generalizedFitting L)

include D in
/-- Any central kernel on the original component is a two-group. -/
theorem central_kernel_isTwoGroup {H : Type*} [Group H]
    (f : L →* H) (hk : f.ker ≤ center L) : IsPGroup 2 f.ker :=
  pCore_isPGroup.to_le (hk.trans (center_le_twoCore D))

/-- The actual image of L in a marked containing central quotient. -/
@[expose] def markedLocalHom {I : Subgroup G} (hLI : L ≤ I)
    {H : Type*} [Group H] (e : (I ⧸ center I) ≃* H) :
    L →* (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I))) :=
  ((e.toMonoidHom.comp (QuotientGroup.mk' (center I))).subgroupMap (L.subgroupOf I)).comp
    (subgroupOfEquivOfLe hLI).symm.toMonoidHom

omit [Finite G] in
theorem markedLocalHom_surjective {I : Subgroup G} (hLI : L ≤ I)
    {H : Type*} [Group H] (e : (I ⧸ center I) ≃* H) :
    Function.Surjective (markedLocalHom hLI e) :=
  ((e.toMonoidHom.comp (QuotientGroup.mk' (center I))).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hLI).symm.surjective

omit [Finite G] in
theorem markedLocalHom_ker_le_center {I : Subgroup G} (hLI : L ≤ I)
    {H : Type*} [Group H] (e : (I ⧸ center I) ≃* H) :
    (markedLocalHom hLI e).ker ≤ center L := by
  intro l hl
  have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
  change e (QuotientGroup.mk' (center I) (inclusion hLI l)) = 1 at hh
  have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp (e.map_eq_one_iff.mp hh)
  apply mem_center_iff.mpr
  intro r
  exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI r)))

/-- The central image preserves the original two-core quotient via its literal map. -/
def markedCoreQuotientEquiv {I : Subgroup G} (hLI : L ≤ I)
    {H : Type*} [Group H] [Finite H] (e : (I ⧸ center I) ≃* H) :
    (L ⧸ pCore 2 L) ≃*
      (((L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))) ⧸
        pCore 2 ((L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I))))) :=
  (markedLocalHom hLI e).quotientPCoreEquivOfSurjective
    (markedLocalHom_surjective hLI e)
    (central_kernel_isTwoGroup D _ (markedLocalHom_ker_le_center hLI e))

theorem markedCoreQuotientEquiv_mk {I : Subgroup G} (hLI : L ≤ I)
    {H : Type*} [Group H] [Finite H] (e : (I ⧸ center I) ≃* H) (l : L) :
    markedCoreQuotientEquiv D hLI e (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' _ (markedLocalHom hLI e l) :=
  MonoidHom.quotientPCoreEquivOfSurjective_mk _ _ _ l

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
