module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.Intervals
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.ChiefSurvival

/-!
# Central complementary intervals in the 14.7.71 accounting

The three complementary strata below the two-core contribute no noncentral
binary chief factor.  The proof uses the actual two-residual of `H`, represented
inside `G` by `K F`, and the literal restriction section map.  If a binary chief
section in one of these strata were noncentral, residual restriction would keep
it noncentral, while the source commutator bounds make its restricted action
trivial.

The source bounds are respectively `[K,U₀] = 1`, `[K,C_H(U)] ≤ U`, and
`[K,O₂(H)] ≤ Q_K`.  No centrality or factor count is assumed.  Source:
Aschbacher--Smith, combined manuscript of 1 March 2004, proof of 14.7.71,
printed p.1075 (PDF p.1092).
-/

@[expose] public section
noncomputable section
open Subgroup NoncentralChiefRefinement
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

omit [Finite G] in
private theorem restricted_isCentral_of_pointwise
    (R : Subgroup F.H) (A B : NormalNode F.H)
    (hcomm : ∀ r : R, ∀ b : B.val,
      ⁅(r : F.H), (b : F.H)⁆ ∈ A.val) :
    IsCentral (restrictNormalNode R A) (restrictNormalNode R B) := by
  rw [isCentral_iff_action]
  intro r x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [sectionAction_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change ((r : R) * b * (r : R)⁻¹ / b : R) ∈ A.val.subgroupOf R
  change ((r : F.H) * (b : F.H) * (r : F.H)⁻¹ / (b : F.H)) ∈ A.val
  simpa only [commutatorElement_def, div_eq_mul_inv] using
    hcomm r ⟨b.val, b.property⟩

omit [Finite G] in
private theorem residual_identification :
    (K F).subgroupOf F.H = pResidual 2 F.H := by
  change Subgroup.comap F.H.subtype ((pResidual 2 F.H).map F.H.subtype) = _
  exact Subgroup.comap_map_eq_self_of_injective F.H.subtype_injective _

private theorem isCentral_of_residual_commutator
    (A B : NormalNode F.H) (hAB : A ⋖ B)
    (hp : IsPGroup 2 (Section A B))
    (hcomm : ∀ r : (K F).subgroupOf F.H, ∀ b : B.val,
      ⁅(r : F.H), (b : F.H)⁆ ∈ A.val) :
    IsCentral A B := by
  by_contra hnon
  have htwo : IsNoncentralTwo A B := ⟨hp, hnon⟩
  have hrestrict := isNoncentralTwo_restrict_pResidual A B hAB htwo
  rw [← residual_identification] at hrestrict
  exact hrestrict.2 (restricted_isCentral_of_pointwise _ _ _ hcomm)

omit [Finite G] in
private theorem core_commutator_le_qK :
    ⁅K F, F.H.pCoreIn 2⁆ ≤ QK F := by
  rw [commutator_comm]
  exact le_sup_left

theorem isCentral_of_fixedNode
    (A B : NormalNode F.H) (hAB : A ⋖ B)
    (hp : IsPGroup 2 (Section A B)) (hB : B ≤ fixedNode d) :
    IsCentral A B := by
  apply isCentral_of_residual_commutator A B hAB hp
  intro r b
  have hbU : ((b : F.H) : G) ∈ d.U₀ := by
    exact hB b.property
  have hcomm : ⁅((r : F.H) : G), ((b : F.H) : G)⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (mem_centralizer_iff.mp (d.K_centralizes_U₀ r.property) _ hbU).symm
  have hcommH : ⁅(r : F.H), (b : F.H)⁆ = 1 := by
    apply Subtype.ext
    exact hcomm
  rw [hcommH]
  exact A.val.one_mem

theorem isCentral_of_cNode
    (c : CriticalPath (L := L) F) (e : Earlier d c)
    (A B : NormalNode F.H) (hAB : A ⋖ B)
    (hp : IsPGroup 2 (Section A B))
    (hA : uNode d ≤ A) (hB : B ≤ cNode d) :
    IsCentral A B := by
  apply isCentral_of_residual_commutator A B hAB hp
  intro r b
  have hbC : ((b : F.H) : G) ∈ C F := by
    exact hB b.property
  have hu : ⁅((r : F.H) : G), ((b : F.H) : G)⁆ ∈ F.U := by
    exact centralizer_commutator d c e
      (commutator_mem_commutator r.property hbC)
  have huH : (⟨⁅((r : F.H) : G), ((b : F.H) : G)⁆,
      (d.conjugationSection.section_le hu)⟩ : F.H) ∈ (uNode d).val := hu
  have hA' := hA huH
  exact hA'

theorem isCentral_of_coreNode
    (c : CriticalPath (L := L) F) (e : Earlier d c)
    (b : QKDualCoordinates d)
    (A B : NormalNode F.H) (hAB : A ⋖ B)
    (hp : IsPGroup 2 (Section A B))
    (hA : qKNode d b ≤ A) (hB : B ≤ coreNode d) :
    IsCentral A B := by
  apply isCentral_of_residual_commutator A B hAB hp
  intro r x
  have hxQ : ((x : F.H) : G) ∈ F.H.pCoreIn 2 := by
    have hxCore := hB x.property
    rw [coreNode_val d] at hxCore
    exact hxCore
  have hq : ⁅((r : F.H) : G), ((x : F.H) : G)⁆ ∈ QK F :=
    core_commutator_le_qK (commutator_mem_commutator r.property hxQ)
  have hqH : (⟨⁅((r : F.H) : G), ((x : F.H) : G)⁆,
      (pCoreIn_le 2 F.H) (QK_le_QH d e.sectionCentralizer hq)⟩ : F.H) ∈
      (qKNode d b).val := by
    exact hq
  exact hA hqH

theorem ChiefSeries.noncentralTwoCount_eq_zero_of_fixedNode
    (s : ChiefSeries F.H) (hlast : s.last ≤ fixedNode d) :
    s.noncentralTwoCount = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  exact ⟨fun z => by
    rcases z with ⟨i, hi⟩
    exact hi.2 (isCentral_of_fixedNode d (s i.castSucc) (s i.succ)
      (s.step i) hi.1 ((s.le_last _).trans hlast))⟩

theorem ChiefSeries.noncentralTwoCount_eq_zero_of_cNode
    (c : CriticalPath (L := L) F) (e : Earlier d c)
    (s : ChiefSeries F.H) (hhead : uNode d ≤ s.head)
    (hlast : s.last ≤ cNode d) :
    s.noncentralTwoCount = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  exact ⟨fun z => by
    rcases z with ⟨i, hi⟩
    exact hi.2 (isCentral_of_cNode d c e (s i.castSucc) (s i.succ)
      (s.step i) hi.1 (hhead.trans (s.head_le _)) ((s.le_last _).trans hlast))⟩

theorem ChiefSeries.noncentralTwoCount_eq_zero_of_coreNode
    (c : CriticalPath (L := L) F) (e : Earlier d c)
    (b : QKDualCoordinates d)
    (s : ChiefSeries F.H) (hhead : qKNode d b ≤ s.head)
    (hlast : s.last ≤ coreNode d) :
    s.noncentralTwoCount = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  exact ⟨fun z => by
    rcases z with ⟨i, hi⟩
    exact hi.2 (isCentral_of_coreNode d c e b (s i.castSucc) (s i.succ)
      (s.step i) hi.1 (hhead.trans (s.head_le _)) ((s.le_last _).trans hlast))⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
