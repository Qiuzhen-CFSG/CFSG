module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.StabilizerSource
public import Theory.GroupTheory.IndexTwoConjugateSpan
/-!
# The generated component candidate and its Sylow intersection

The index-two block stabilizer fixes both original blocks. Thus the two
conjugates of the second block generate a normal subgroup of their join
with the larger stabilizer. The source noncommuting module prevents its
Sylow intersection from leaving the original block stabilizer.

The torus producer supplies the conjugator, factor containment and centrality
used here; no component or model conclusion is presumed.
Source: Aschbacher–Smith 2.4.7, printed pp.540–541.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] {M M₀ : Subgroup G}
variable {d : MinimalBlockSetup M} {n : ℕ}

/-- Fixing the first of the two distinct blocks fixes the second. -/
theorem DoubleLinearSourceSetup.block_stabilizer_normalizes_second
    (c : DoubleLinearSourceSetup d M₀ n) :
    ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      normalizer (d.block.map d.H.subtype : Set G) ≤ normalizer (c.second : Set G) := by
  rintro a ⟨ha,haL⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases c.permutes_second a ha with he | he
  · exact he
  · have hf := mem_normalizer_iff_map_conj_eq.mp haL
    have hinj := map_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective
    exact (c.second_ne (hinj (he.trans hf.symm))).elim

open ChapterC.Section05.ConjugateSource

/-- The literal two-block span is normal in the generated source group. -/
theorem DoubleLinearSourceSetup.generated_pair_normal
    (c : DoubleLinearSourceSetup d M₀ n) (S₁ : Subgroup G) (x : G)
    (hBS : (((d.S : Subgroup d.H).map d.H.subtype) ⊓
      normalizer (d.block.map d.H.subtype : Set G)) ≤ S₁)
    (hi : (((d.S : Subgroup d.H).map d.H.subtype) ⊓
      normalizer (d.block.map d.H.subtype : Set G)).relIndex S₁ = 2)
    (hx : x ∈ S₁) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let K := c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom
    (K.subgroupOf (K ⊔ S₁)).Normal := by
  dsimp only
  apply normal_subgroupOf_of_le_normalizer
  apply sup_le (c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom).le_normalizer
  exact index_two_normalizes_pair _ S₁ c.second hBS hi x hx
    (fun h => hxS h.1) c.block_stabilizer_normalizes_second

/-- The component's Sylow intersection lies in the original block
stabilizer. The conjugator and module inclusion are supplied by the actual
torus construction, which retains the source noncommutation mark. -/
theorem DoubleLinearSourceSetup.generated_pair_sylow_le_stabilizer
    (c : DoubleLinearSourceSetup d M₀ n) (S₁ R₁ : Subgroup G) (x : G)
    (hi : (((d.S : Subgroup d.H).map d.H.subtype) ⊓
      normalizer (d.block.map d.H.subtype : Set G)).relIndex S₁ = 2)
    (hx : x ∈ S₁) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hUR : sourceModule (d.block.map d.H.subtype) ≤ R₁)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map
      (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule (d.block.map d.H.subtype) : Set G))
    (hc : c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (R₁ : Set G)) :
    (c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom) ⊓ S₁ ≤
      ((d.S : Subgroup d.H).map d.H.subtype) ⊓ normalizer (d.block.map d.H.subtype : Set G) := by
  let := c.field₁_field
  let : IsElementaryAbelian 2 (sourceModule (d.block.map d.H.subtype)) := c.marked₁.elementary
  have hU : sourceModule (d.block.map d.H.subtype) ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact (le_inf inf_le_right (inf_le_left.trans hc)).trans
    (index_two_centralizer_le _ S₁ _ R₁ hi x hx (fun h => hxS h.1)
      (inf_le_right.trans (normalizer_le_normalizer_characteristic_image _ (ChapterC.blockU _)))
      hUR hU hnc)

end CFSG.Quasithin.Chapter2
