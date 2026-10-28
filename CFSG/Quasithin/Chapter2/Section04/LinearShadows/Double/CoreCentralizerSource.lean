module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.PairSource
public import CFSG.Quasithin.ChapterC.Section01.BlockCoreConjugation
public import Theory.GroupTheory.PerfectNormalizedIntersection
/-!
# Core centralization in the literal two-conjugate group

The actual two-core intersects the second block trivially: otherwise
irreducibility contains its natural module, whose preserved noncommuting
conjugate would then lie inside the same elementary core. The original
block stabilizer normalizes the block, so perfectness propagates this
trivial intersection to centralization of the full two-core. This supplies
the component-promotion premise directly.

Source: Aschbacher–Smith 2.4.7, printed p.541.
-/
public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Stellmacher Theory.GroupTheory
open ChapterC.Section05.ConjugateSource LinearDouble
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G}
variable {d : MinimalBlockSetup M} {n : ℕ}

/-- The second original module retains the same noncommutation mark. -/
theorem DoubleLinearSourceSetup.second_noncommuting_source
    (c : DoubleLinearSourceSetup d M₀ n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (a : SourceTorusData c) :
    ¬ (sourceModule c.second).map (MulAut.conj a.x⁻¹).toMonoidHom ≤
      centralizer (sourceModule c.second : Set G) := by
  let := c.field₁_field
  let := c.field₂_field
  have hex : ∃ t : M₀, (t : G)∈(d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G)=c.second := by
    obtain ⟨s,hs,he⟩ := c.exchange
    exact ⟨⟨s,hSM hs⟩,hs,he⟩
  rw [a.second_mark]
  exact RankOne.second_noncommuting (c.marked₁.fourModuleSourceInputs c.commutes
    c.marked₂.module_le M₀ ((d.S : Subgroup d.H).map d.H.subtype) c.x c.x_mem
    (c.original.R_normal c.x_mem) hi c.permutes hex c.noncommuting)

/-- The natural block centralizes the actual ambient two-core. The
irreducible natural module and its preserved noncommuting conjugate remove
the stronger core identity from the component-promotion input. -/
theorem DoubleLinearSourceSetup.adjusted_pair_core_centralizes
    (c : DoubleLinearSourceSetup d M₀ n) [Group.IsPerfect c.second]
    (T : Sylow 2 G) (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (a : SourceTorusData c) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let S₁ := M₀ ⊓ normalizer ((elementaryAbelianMaxJ S ⊓ d.block.map d.H.subtype : Subgroup G) : Set G)
    let K := c.second ⊔ c.second.map (MulAut.conj a.x⁻¹).toMonoidHom
    let X := K ⊔ S₁
    (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = S₁) →
      c.second ≤ centralizer (twoCore X : Set G) := by
  let := c.field₂_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let R₂ := R ⊓ c.second
  let B := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
  let S₁ := M₀ ⊓ normalizer ((R ⊓ d.block.map d.H.subtype : Subgroup G) : Set G)
  let K := c.second ⊔ c.second.map (MulAut.conj a.x⁻¹).toMonoidHom
  let X := K ⊔ S₁
  change (∃ P:Sylow 2 X,(P:Subgroup X).map X.subtype=S₁) → c.second≤centralizer (twoCore X:Set G)
  rintro ⟨P,hP⟩
  obtain ⟨_,_,hxS,_,hKS,hn,_⟩ := c.adjusted_pair_geometry T hST hSM hMT hi a
  change K⊓S₁≤B at hKS
  change (K.subgroupOf X).Normal at hn
  have hLX : c.second≤X := le_sup_left.trans le_sup_left
  have hQN : X≤normalizer (twoCore X:Set G) := le_normalizer_twoCore X
  have hQp : IsPGroup 2 (twoCore X) := isPGroup_pCoreIn 2 X
  have hQS : twoCore X≤S₁ := hP ▸ pCoreIn_le_sylow X P
  have hU : sourceModule c.second≤R₂ :=
    le_inf (c.marked₂.module_le.trans_eq (c.core_pair T hST hSM hMT hi).1) (map_subtype_le _)
  have hQinf := c.second_type.2.1.inf_eq_bot_of_noncommuting_conjugate (twoCore X) R₂
    hQp (hLX.trans hQN) a.geometry.centerless_second a.geometry.core_second
    hU inf_le_right a.x (hQN (show a.x∈X from (show S₁≤X from le_sup_right) hxS)) a.geometry.fixes_second_sylow
    (c.second_noncommuting_source hSM hi a)
  have hKN : X≤normalizer (K:Set G) := (normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn
  exact Subgroup.centralizes_of_normalized_intersection_bot (twoCore X) K c.second B (hLX.trans hQN)
    ((pCoreIn_le 2 X).trans hKN) le_sup_left hQinf
    ((le_inf inf_le_right (inf_le_left.trans hQS)).trans hKS) c.block_stabilizer_normalizes_second

end CFSG.Quasithin.Chapter2
