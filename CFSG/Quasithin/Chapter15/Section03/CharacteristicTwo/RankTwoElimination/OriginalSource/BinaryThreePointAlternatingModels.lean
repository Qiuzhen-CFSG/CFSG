module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointJoinQuotient
public import Theory.SpecificGroups.Alternating.SevenThreeSection
public import Theory.GroupTheory.PCoreImageRestriction
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The actual binary-three placement in an alternating-seven carrier

The order-168 section in A₇ has trivial two-core and is self-normalizing.
Transport these facts through the actual containing subgroup, then through
the literal point-centralizer quotient. In the original group, the
component two-core is exactly its intersection with the point kernel.
In particular the original commutator core lies in that kernel.

These are placement equalities, not an alternating-carrier exclusion.
A₇ does contain a Sylow-normalized PSL₃(2), and A₈ contains the affine
binary-three parabolic. The further original opposed-core argument remains
necessary in the setting of Aschbacher--Smith 15.3.23, pp.1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The unchanged smaller subgroup in an A₇ carrier has trivial two-core,
order168, and no larger normalizer inside that carrier. -/
theorem binary_three_alternating_seven_placement
    {B K : Subgroup G} (hBK : B ≤ K)
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (a : K ≃* alternatingGroup (Fin 7)) :
    pCore 2 B = ⊥ ∧ Nat.card B = 168 ∧
      normalizer (B : Set G) ⊓ K = B := by
  let A := B.subgroupOf K
  let D := A.map a.toMonoidHom
  let b : A ≃* B := subgroupOfEquivOfLe hBK
  let c : A ≃* D := a.subgroupMap A
  let d : B ≃* D := b.symm.trans c
  let de : (D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.SL :=
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans e).trans
      Matrix.PSL3Two.equiv.symm
  have hd := alternatingGroup.SevenThreeSection.twoCore_eq_bot D de
  have hb : pCore 2 B = ⊥ := by
    apply map_injective (f := d.toMonoidHom) d.injective
    rw [pCore_map_iso 2 d,hd,Subgroup.map_bot]
  have hc : Nat.card B = 168 :=
    (Nat.card_congr d.toEquiv).trans (alternatingGroup.SevenThreeSection.card_eq D de)
  have hn : normalizer (A : Set K) = A := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_equiv_normalizer_eq]
    exact alternatingGroup.SevenThreeSection.normalizer_eq D de
  refine ⟨hb,hc,le_antisymm ?_ (le_inf B.le_normalizer hBK)⟩
  rintro x ⟨hx,hxK⟩
  have hxA : (⟨x,hxK⟩ : K) ∈ normalizer (A : Set K) := by
    rw [←subgroupOf_normalizer_eq hBK]
    exact hx
  rw [hn] at hxA
  exact hxA

/-- For the literal point quotient, the original component two-core is
exactly its intersection with the actual point-centralizer kernel. -/
theorem binary_three_alternating_seven_point_core
    (L C : Subgroup G) (hLC : L ≤ C)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,ZMod 2))
    (K : Subgroup (C ⧸ pCore 2 C))
    (hBK : (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ≤ K)
    (a : K ≃* alternatingGroup (Fin 7)) :
    L.pCoreIn 2 = L ⊓ C.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let A := L.subgroupOf C
  let b : A ≃* L := subgroupOfEquivOfLe hLC
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkA : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eA := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e
  let eB := ((q.subgroupMap A).pCoreQuotientEquiv
    (q.subgroupMap_surjective A) hkA).symm.trans eA
  have hbot := (binary_three_alternating_seven_placement hBK eB a).1
  have hpre := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 q A hk
  have hzero : (A.map q).pCoreIn 2 = ⊥ := by
    unfold pCoreIn
    rw [hbot,Subgroup.map_bot]
  rw [hzero,MonoidHom.comap_bot,QuotientGroup.ker_mk'] at hpre
  have hm := congrArg (Subgroup.map C.subtype) hpre
  change (A ⊓ pCore 2 C).map C.subtype = ((L.subgroupOf C).pCoreIn 2).map C.subtype at hm
  rw [map_inf _ _ _ C.subtype_injective,map_subgroupOf_eq_of_le hLC,
    pCoreIn_subgroupOf 2 L C hLC,
    map_subgroupOf_eq_of_le ((L.pCoreIn_le 2).trans hLC)] at hm
  exact hm.symm

/-- The original commutator core vanishes in the same point quotient in
the A₇ carrier case. Its opposite conjugate need not vanish there. -/
theorem binary_three_alternating_seven_commutator_core_le
    (L C : Subgroup G) (hLC : L ≤ C)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,ZMod 2))
    (K : Subgroup (C ⧸ pCore 2 C))
    (hBK : (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ≤ K)
    (a : K ≃* alternatingGroup (Fin 7)) :
    LinearThree.commutatorCore L ≤ C.pCoreIn 2 := by
  apply (LinearThree.commutatorCore_le L).trans
  rw [binary_three_alternating_seven_point_core L C hLC e K hBK a]
  exact inf_le_right

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
