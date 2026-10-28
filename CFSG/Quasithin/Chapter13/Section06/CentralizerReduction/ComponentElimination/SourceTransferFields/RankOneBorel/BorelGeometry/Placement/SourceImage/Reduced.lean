module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Preparation
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The reduced local rank-one action

`Preparation` identifies the kernel of the restricted action with the
centralizer of the internal copy of `W_K`, and proves that the kernel is a
two-group.  That calculation does not by itself make the action reduced:
the missing statement is precisely that the local two-core centralizes
`W_K`, as the equivalence `localReduced_iff_core_centralizes` records.

The source paragraph before 13.6.14 gives the reduced condition in the
larger actor `K₋L_vT_v`.  Restricting an `R₂` condition to `KT_v` requires a
comparison of two-cores.  The comparison below is valid when `KT_v` is
subnormal in the larger actor; this is the exact extra hypothesis needed for
that transfer.  No `L_v ≤ K` or local-map surjectivity is used.

Source: Aschbacher--Smith, combined manuscript, 13.6.14 and 13.6.18,
printed pp.929--931 (PDF pp.946--948), and B.2.11--14, pp.77--78.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/- The exact local interface: a two-core centralizer premise, rather than a
  two-group kernel premise, is what closes reducedness. -/
theorem localMap_range_twoCore_eq_bot_of_core_centralizes
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : Matrix.SpecialLinearGroup.RankOneResidual.NaturalSection (F := F)
      (componentRepresentation K L T z v hL hz) (movingSpace K L T z v))
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (hcore : pCore 2 (K ⊔ Tv T v : Subgroup G) ≤
      centralizer (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G))) :
    pCore 2 (localMap K L T z v hL hz).range = ⊥ := by
  exact (localReduced_iff_core_centralizes K L T z v hL hz hK hnorm hF hb s hW).mpr hcore

/- A literal B.2.11 witness in the actual local actor discharges the premise
  above.  The quotient is relative to `KT_v`, with the internal centralizer
  convention used by the restricted map. -/
theorem localMap_range_twoCore_eq_bot_of_local_reduced
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : Matrix.SpecialLinearGroup.RankOneResidual.NaturalSection (F := F)
      (componentRepresentation K L T z v hL hz) (movingSpace K L T z v))
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (hquot : letI := internalWK_normal K L T z v hL hz
      pCore 2 ((K ⊔ Tv T v : Subgroup G) ⧸
        centralizer (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G))) = ⊥) :
    pCore 2 (localMap K L T z v hL hz).range = ⊥ := by
  let hR : Theory.GroupTheory.IsPReduced 2
      (internalWK K L T z v hL hz) :=
    { normal := internalWK_normal K L T z v hL hz
      elementary := internalWK_elementary K L T z v hL hz
      quotient_pCore_eq_bot := hquot }
  apply localMap_range_twoCore_eq_bot_of_core_centralizes K L T z v hL hz
    hK hnorm hF hb s hW
  exact Subgroup.le_centralizer_iff.mp hR.le_centralizer_pCore

/- The source-valid restriction comparison.  `hR` is the genuine B.2.11
  condition in the larger actor `A`; `hsub` is what permits its two-core to
  control the two-core of `KT_v`.  In the printed argument this comparison
  must be discharged separately; it does not follow from a kernel being a
  two-group. -/
theorem localMap_range_twoCore_eq_bot_of_subnormal_reduced
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : Matrix.SpecialLinearGroup.RankOneResidual.NaturalSection (F := F)
      (componentRepresentation K L T z v hL hz) (movingSpace K L T z v))
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (A : Subgroup G) (hHA : K ⊔ Tv T v ≤ A)
    (hsub : ((K ⊔ Tv T v).subgroupOf A).IsSubnormal)
    (hR : Theory.GroupTheory.IsPReduced 2
      ((WK K L T z v).subgroupOf A)) :
    pCore 2 (localMap K L T z v hL hz).range = ⊥ := by
  apply localMap_range_twoCore_eq_bot_of_core_centralizes K L T z v hL hz
    hK hnorm hF hb s hW
  have hWA : WK K L T z v ≤ A := hW.trans hHA
  have hcoreA : (pCore 2 A).map A.subtype ≤
      centralizer (WK K L T z v : Set G) := by
    have hcA : pCore 2 A ≤
        centralizer ((WK K L T z v).subgroupOf A : Set A) :=
      Subgroup.le_centralizer_iff.mp hR.le_centralizer_pCore
    rintro _ ⟨a, ha, rfl⟩ w hw
    change (w : G) * (a : G) = (a : G) * (w : G)
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hcA ha)
      ⟨w, hWA hw⟩ hw)
  have hcoreMap := pCoreAmbient_mono_of_isSubnormalIn
    (K ⊔ Tv T v : Subgroup G) A 2 hHA hsub
  have hcoreH : (pCore 2 (K ⊔ Tv T v : Subgroup G)).map
      (K ⊔ Tv T v).subtype ≤ centralizer (WK K L T z v : Set G) :=
    hcoreMap.trans hcoreA
  intro x hx w hw
  have hx' := hcoreH (mem_map_of_mem (K ⊔ Tv T v).subtype hx)
  exact Subtype.ext (mem_centralizer_iff.mp hx' (w : G) hw)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
end
