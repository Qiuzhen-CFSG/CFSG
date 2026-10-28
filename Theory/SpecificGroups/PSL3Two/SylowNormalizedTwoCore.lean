module
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.ElementaryAbelian.Injective

/-!
# Sylow-normalized two-subgroups of SL₃(2)

A nontrivial two-subgroup normalized by a full Sylow two-subgroup and a cubic
is the four-group radical of its normalizer. Its ambient centralizer is
contained in that radical.

Simplicity makes the normalizer proper, and the cubic makes it a non-two-group.
The Sylow-overgroup classification therefore identifies it with a parabolic.
The standard S₄ action identifies its only nontrivial normal two-subgroup
with its elementary abelian two-core of order four.

Source: the binary projective-plane local model in Aschbacher–Smith,
*The Classification of Quasithin Groups*, I.5.4 and I.5.7, printed pp. 420–421.
-/

public section
open Subgroup
namespace Matrix.PSL3Two.SylowNormalizedTwoCore

/-- The actual normalizer is S₄ and the indicated two-subgroup is its full core. -/
theorem normalizer_core (N : Subgroup SL) (S : Sylow 2 SL)
    (hN : IsPGroup 2 N) (hne : N ≠ ⊥)
    (hn : (S : Subgroup SL) ≤ normalizer (N : Set SL))
    (c : SL) (hc : c ∈ normalizer (N : Set SL)) (horder : orderOf c = 3) :
    ∃ _e : normalizer (N : Set SL) ≃* Equiv.Perm (Fin 4),
      N.subgroupOf (normalizer (N : Set SL)) = pCore 2 (normalizer (N : Set SL)) := by
  let H := normalizer (N : Set SL)
  have hH : H ≠ ⊤ := by
    let : IsSimpleGroup PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    let : IsSimpleGroup SL := equiv.isSimpleGroup
    intro ht
    have hnormal : N.Normal := normalizer_eq_top_iff.mp ht
    rcases hnormal.eq_bot_or_eq_top with hb | ht
    · exact hne hb
    · obtain ⟨n, hn⟩ := hN.exists_card_eq
      have h7 : 7 ∣ 2 ^ n := by
        rw [← hn, ht, card_top, card_SL]
        decide
      have := (show Nat.Prime 7 by decide).dvd_of_dvd_pow h7
      norm_num at this
  have hHtwo : ¬ IsPGroup 2 H := by
    intro htwo
    obtain ⟨n, hn⟩ := htwo.exists_card_eq
    have h3 := H.orderOf_dvd_natCard hc
    rw [horder, hn] at h3
    have := (show Nat.Prime 3 by decide).dvd_of_dvd_pow h3
    norm_num at this
  obtain ⟨e, _, he⟩ := exists_sylow_line_marking equiv S H hn hH hHtwo
  let eH : H ≃* Equiv.Perm (Fin 4) :=
    ((e.subgroupMap H).trans (MulEquiv.subgroupCongr he)).trans
      MarkedAutomorphisms.lineEquivSymmetric
  let B := N.subgroupOf H
  let : B.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hB : IsPGroup 2 B := hN.of_equiv (subgroupOfEquivOfLe N.le_normalizer).symm
  have hBcore : B ≤ pCore 2 H := le_sSup ⟨inferInstance, hB⟩
  refine ⟨eH, ?_⟩
  rcases ParabolicCoreModel.normal_le_core eH B hBcore with hb | hb
  · have hm := congrArg (Subgroup.map H.subtype) hb
    rw [map_subgroupOf_eq_of_le N.le_normalizer, Subgroup.map_bot] at hm
    exact (hne hm).elim
  · exact hb

/-- A Sylow-normalized nontrivial two-subgroup with a cubic normalizer is a four-group. -/
theorem recognize (N : Subgroup SL) (S : Sylow 2 SL)
    (hN : IsPGroup 2 N) (hne : N ≠ ⊥)
    (hn : (S : Subgroup SL) ≤ normalizer (N : Set SL))
    (c : SL) (hc : c ∈ normalizer (N : Set SL)) (horder : orderOf c = 3) :
    IsElementaryAbelian 2 N ∧ Nat.card N = 4 := by
  obtain ⟨eH, he⟩ := normalizer_core N S hN hne hn c hc horder
  let eN : N ≃* pCore 2 (normalizer (N : Set SL)) :=
    (subgroupOfEquivOfLe N.le_normalizer).symm.trans (MulEquiv.subgroupCongr he)
  let : IsElementaryAbelian 2 (pCore 2 (normalizer (N : Set SL))) :=
    (ParabolicCoreModel.core_data eH).1
  exact ⟨IsElementaryAbelian.of_injective eN.toMonoidHom eN.injective,
    (Nat.card_congr eN.toEquiv).trans (ParabolicCoreModel.core_data eH).2⟩

/-- The four-group is self-centralizing in the full binary special-linear group. -/
theorem centralizer_le (N : Subgroup SL) (S : Sylow 2 SL)
    (hN : IsPGroup 2 N) (hne : N ≠ ⊥)
    (hn : (S : Subgroup SL) ≤ normalizer (N : Set SL))
    (c : SL) (hc : c ∈ normalizer (N : Set SL)) (horder : orderOf c = 3) :
    centralizer (N : Set SL) ≤ N := by
  obtain ⟨eH, he⟩ := normalizer_core N S hN hne hn c hc horder
  intro x hx
  let y : normalizer (N : Set SL) := ⟨x, centralizer_le_normalizer _ hx⟩
  have hy : y ∈ centralizer (pCore 2 (normalizer (N : Set SL)) :
      Set (normalizer (N : Set SL))) := by
    rw [← he, mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx z hz
  have hyN := ParabolicCoreModel.core_selfCentralizing eH hy
  rw [← he] at hyN
  exact hyN

end Matrix.PSL3Two.SylowNormalizedTwoCore
