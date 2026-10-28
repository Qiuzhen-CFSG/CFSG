module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalSeed
public import Theory.Representation.PSL3Two.SmallInvariantSubgroups

/-!
# The marked natural eight has no proper nonzero invariant subgroup
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem natural_seed_invariant_dichotomy
    {L : Subgroup G} {T V : Subgroup G}
    (a : L →* Matrix.PSL3Two.SL) (ha : Function.Surjective a)
    (hs : HasSectionModel L V ⊥ a BinaryLinearThree.W)
    (hTV : T ≤ V) (hTL : L ≤ normalizer T) : T = ⊥ ∨ T = V := by
  obtain ⟨_,hLV,_,_,e,he⟩ := hs
  let : IsIrreducible BinaryLinearThree.W := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let p := e.toMonoidHom.comp (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf V))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : p.ker = (⊥ : Subgroup G).subgroupOf V := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let U : Subrepresentation BinaryLinearThree.W := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 ((T.subgroupOf V).map p).toAddSubgroup'
    apply_mem_toSubmodule g := by
      intro v hv
      obtain ⟨l,rfl⟩ := ha g
      change Multiplicative.ofAdd v ∈ (T.subgroupOf V).map p at hv
      obtain ⟨x,hx,hv⟩ := hv
      let y := V.normalizerMonoidHom (inclusion hLV l) x
      have hyT : (y : G) ∈ T := (mem_normalizer_iff.mp (hTL l.property) x).mp hx
      change Multiplicative.ofAdd (BinaryLinearThree.W (a l) v) ∈ (T.subgroupOf V).map p
      refine ⟨y,hyT,?_⟩
      apply Multiplicative.toAdd.injective
      have hh := he l x y rfl
      change (p y).toAdd = BinaryLinearThree.W (a l) (p x).toAdd at hh
      rw [hh,hv]
      rfl }
  rcases eq_bot_or_eq_top U with hbot | htop
  · left
    apply le_antisymm ?_ bot_le
    intro x hx
    have hv : (p ⟨x,hTV hx⟩).toAdd ∈ U := mem_map_of_mem p hx
    rw [hbot] at hv
    have hz : (⟨x,hTV hx⟩ : V) ∈ p.ker := hv
    rw [hk] at hz
    have hz' : ((⟨x,hTV hx⟩ : V) : G) ∈ (⊥ : Subgroup G) := hz
    exact hz'
  · right
    apply le_antisymm hTV
    intro v hv
    have hm : p ⟨v,hv⟩ ∈ (T.subgroupOf V).map p := by
      change p ⟨v,hv⟩ ∈ U
      rw [htop]
      trivial
    obtain ⟨x,hx,heq⟩ := hm
    have hz : (⟨v,hv⟩ : V) / x ∈ p.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_div,heq,div_self']
    rw [hk] at hz
    have hxT : (x : G) ∈ T := hx
    have hzBot : (((⟨v,hv⟩ : V) / x : V) : G) ∈ (⊥ : Subgroup G) := hz
    have hzT : (((⟨v,hv⟩ : V) / x : V) : G) ∈ T :=
      (bot_le : (⊥ : Subgroup G) ≤ T) hzBot
    have hh := T.mul_mem hzT hxT
    change (v:G) / (x : G) * (x : G) ∈ T at hh
    simpa only [div_mul_cancel] using hh

/-- Every nonzero original L-invariant subgroup of the marked natural eight is the whole natural eight. -/
theorem binary_three_source_natural_invariant_eq
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (T V : Subgroup G) (hTV : T ≤ V) (hTL : L ≤ normalizer T)
    (hne : T ≠ ⊥) (hV : V = ⁅coreCenter L,L⁆) : T = V := by
  obtain ⟨a,ha,_,hs⟩ := binary_three_original_natural_seed d L b t common hb
  rw [hV] at hTV
  rcases natural_seed_invariant_dichotomy a ha hs hTV hTL with h | h
  · exact False.elim (hne h)
  · exact h.trans hV.symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
