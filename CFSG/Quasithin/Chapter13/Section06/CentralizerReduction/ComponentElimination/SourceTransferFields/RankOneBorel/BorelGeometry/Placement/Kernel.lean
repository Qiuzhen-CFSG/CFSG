module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.PCoreActionCardKernel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The two-kernel of the actual rank-one local action

Restrict the existing plus quotient to KT_v without identifying KT_v with
the larger actor K₋L_vT_v. Its kernel is exactly C_{KT_v}(W_K). The genuine
L₂ block identifies K/O₂(K) with SL₂ over its coefficient field. Transport
between equal-size fields and the natural-section actor show that this
quotient and K⁺ have the same order. Kernel-image counting on K and the
two-group quotient KT_v/K then make the entire action kernel a two-group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.6.18, printed p.931; block definitions C.1.7 and C.1.12, pp.123–124.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection
variable {G : Type*} [Group G]

theorem localActor_le (K L T : Subgroup G) (v : G) :
    K ⊔ Tv T v ≤ plusActor K L T v :=
  sup_le (K_le_plusActor K L T v) le_sup_right

/-- Restrict the literal plus map to KT_v; L_v is not assumed to lie in K. -/
def localMap (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (K ⊔ Tv T v : Subgroup G) →* Gplus K L T z v hL hz :=
  (plusMk K L T z v hL hz).comp (inclusion (localActor_le K L T v))

theorem localMap_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (localMap K L T z v hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf (K ⊔ Tv T v) := by
  rw [localMap, ← MonoidHom.comap_ker, plusMk_ker]
  rfl

theorem localMap_image (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (A : Subgroup G)
    (hA : A ≤ K ⊔ Tv T v) :
    (A.subgroupOf (K ⊔ Tv T v)).map (localMap K L T z v hL hz) =
      plusImage K L T z v hL hz A := by
  rw [localMap, ← map_map, plusImage]
  congr 1
  apply map_injective (plusActor K L T v).subtype_injective
  rw [map_map, subtype_comp_inclusion, map_subgroupOf_eq_of_le hA,
    map_subgroupOf_eq_of_le (hA.trans (localActor_le K L T v))]

variable [Finite G]

omit [Finite G] in
/-- The block definition and the natural-section actor have the same actual
core-quotient cardinality, even if their coefficient fields differ. -/
theorem coreQuotient_card (K : Subgroup G) {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock K n)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) :
    Nat.card (K ⧸ pCore 2 K) = Nat.card SL(2,F) := by
  obtain ⟨_, _, E, _, _, hE, _, hm⟩ := hb
  obtain ⟨e⟩ := hm.quotient_iso
  let : Fintype E := Fintype.ofFinite E
  let : Fintype F := Fintype.ofFinite F
  let i : E ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hE.trans hF.symm)
  exact Nat.card_congr (e.trans (Atlas.fieldEquivSL 2 i)).toEquiv

/-- Counting on K, followed by the two-group quotient KT_v/K, proves that
the entire restricted action kernel is a two-group. -/
theorem localMap_kernel_isPGroup (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v)) :
    IsPGroup 2 (localMap K L T z v hL hz).ker := by
  let H := K ⊔ Tv T v
  let C := K.subgroupOf H
  have hKH : K ≤ H := le_sup_left
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hnorm)
  have hsup : C ⊔ (Tv T v).subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hKH (show Tv T v ≤ H from le_sup_right)]
    exact subgroupOf_self _
  have hq : IsPGroup 2 (H ⧸ C) := isPGroup_quotient_of_sup_eq_top C _
    (Chapter1.isSylowIn_iff.mp hK.1.2.2.1).1.comap_subtype hsup
  apply MonoidHom.isPGroup_ker_of_card_image_eq_core_quotient
    (localMap K L T z v hL hz) C hq
  rw [localMap_image K L T z v hL hz K le_sup_left]
  let c : C ≃* K := subgroupOfEquivOfLe hKH
  let cq : C ⧸ pCore 2 C ≃* K ⧸ pCore 2 K :=
    QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  exact (Nat.card_congr s.actor.toEquiv).trans
    ((Nat.card_congr cq.toEquiv).trans (coreQuotient_card K hb hF)).symm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement

end
