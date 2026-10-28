module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneChart
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Markers
public import Theory.Mathieu.M22.Properties.OuterHexadRadical
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
/-!
# The point radical in the original plane quotient

The image of E under the original cubic projection is a normal two-subgroup
of the full hexad stabilizer, hence lies in its order-sixteen pointwise kernel.
The cubic kernel contributes no extra two-elements beyond Q. The extraspecial
abelian bound gives |E ∩ Q| ≤ 128, and |E| = 2048 forces equality in both bounds.
Thus the quotient marking and its kernel are literal, not abstract E₁₆ labels.
These are the algebraic inputs to the disjoint-hexad orbit in (5.3)(2).

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (5.3)(2), p.600, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

theorem radical_le_plane : a.P.E ≤ centralizer z := by
  let := a.P.E_elementary
  intro v hv
  exact mem_centralizer_singleton_iff.mpr
    ((Commute.all (⟨z,a.marker_mem_E⟩ : a.P.E) ⟨v,hv⟩).map a.P.E.subtype).eq.symm

@[expose] noncomputable def radicalDesign : a.P.E →* m22DesignAut :=
  a.designProjection.comp (inclusion a.radical_le_plane)

theorem radicalDesign_apply (v : a.P.E) :
    a.radicalDesign v = a.designProjection ⟨v,a.radical_le_plane v.property⟩ := rfl

/-- The original cubic projection kills exactly E ∩ Q on the point radical. -/
theorem radicalDesign_ker : a.radicalDesign.ker = (ambientCore z).subgroupOf a.P.E := by
  let := a.P.E_elementary
  ext v
  change a.designProjection ⟨v,a.radical_le_plane v.property⟩ = 1 ↔ v.val ∈ ambientCore z
  rw [←m22DesignAutToAut_injective.eq_iff, a.designProjection_marking, map_one]
  change a.P.cubic.projection (QuotientGroup.mk' (core z) ⟨v,a.radical_le_plane v.property⟩) = 1 ↔ _
  constructor
  · intro hv
    let q : a.P.cubic.projection.ker := ⟨QuotientGroup.mk' (core z) ⟨v,a.radical_le_plane v.property⟩,hv⟩
    have hq2 : q^2=1 := by
      apply Subtype.ext
      change (QuotientGroup.mk' (core z) _)^2=1
      rw [←map_pow]
      have hv2 : (⟨v,a.radical_le_plane v.property⟩ : centralizer z)^2=1 := by
        apply Subtype.ext
        exact elemPow_eq_one_of_isElementaryAbelian v.val v.property
      rw [hv2,map_one]
    have hq3 : q^3=1 := by
      rw [←a.P.cubic.kernel_card]
      exact pow_card_eq_one'
    have hq : q=1 := by
      have ho := orderOf_dvd_of_pow_eq_one hq2
      have ho' := orderOf_dvd_of_pow_eq_one hq3
      apply orderOf_eq_one_iff.mp
      exact Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3) ho ho'
    have hvcore := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hq)
    exact ⟨⟨v,a.radical_le_plane v.property⟩,hvcore,rfl⟩
  · intro hv
    have hvcore : (⟨v,a.radical_le_plane v.property⟩ : centralizer z) ∈ core z := by
      rw [←ambientCore_subgroupOf]
      exact hv
    have he : QuotientGroup.mk' (core z) ⟨v,a.radical_le_plane v.property⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hvcore
    rw [he,map_one]

theorem radicalDesign_range_le : a.radicalDesign.range ≤
    (m22HexadPointwiseKernel a.P.hexad).map M22ValueBound.Concrete.inclusion := by
  let := a.P.E_elementary
  have hr : a.radicalDesign.range = (a.P.E.subgroupOf (centralizer z)).map a.designProjection := by
    ext g
    constructor
    · rintro ⟨v,rfl⟩
      exact ⟨⟨v,a.radical_le_plane v.property⟩,v.property,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨⟨v,hv⟩,rfl⟩
  have hin : (MulAction.stabilizer M22 a.P.hexad).map M22ValueBound.Concrete.inclusion ≤
      MulAction.stabilizer m22DesignAut a.P.hexad := by
    rintro g ⟨v,hv,rfl⟩
    exact hv
  rw [←M22OuterHexad.radical_eq a.P.hexad_mem _ hin le_rfl]
  apply le_pCoreIn_of_normalizes
  · rw [hr]
    exact ((IsElementaryAbelian.isPGroup 2 a.P.E).comap_subtype).map _
  · rintro g ⟨v,rfl⟩
    exact (a.point_plane_overlap ⟨v,a.radical_le_plane v.property⟩).mp (a.P.E_le v.property)
  · intro g hg
    obtain ⟨n,rfl⟩ := a.designProjection_surjective g
    have hn : (n : G) ∈ normalizer (a.P.E : Set G) := by
      rw [a.point_normalizer]
      exact (a.point_plane_overlap n).mpr hg
    rw [hr]
    apply le_normalizer_map a.designProjection
    refine ⟨n,?_,rfl⟩
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp hn v

theorem radicalDesign_ker_bound : Nat.card a.radicalDesign.ker ≤ 128 := by
  let := a.P.E_elementary
  let := IsExtraspecial.of_mulEquiv (coreEquivAmbient z) h.extraspecial
  let : IsMulCommutative (a.P.E.subgroupOf (ambientCore z)) :=
    a.P.E.comap_injective_isMulCommutative (ambientCore z).subtype_injective
  have hh := extraspecial_prime_abelian_card_sq_le_any (p := 2) (a.P.E.subgroupOf (ambientCore z))
  have hq : Nat.card (ambientCore z) = 2^13 :=
    (Nat.card_congr (coreEquivAmbient z).toEquiv).symm.trans h.core_card
  have he : Nat.card (a.P.E.subgroupOf (ambientCore z)) = Nat.card a.radicalDesign.ker := by
    rw [a.radicalDesign_ker]
    rw [←card_map_of_injective (ambientCore z).subtype_injective,
      ←card_map_of_injective a.P.E.subtype_injective,
      subgroupOf_map_subtype,subgroupOf_map_subtype,inf_comm]
  rw [hq,he] at hh
  nlinarith

/-- The image is the literal native pointwise hexad kernel. -/
theorem radicalDesign_range_eq : a.radicalDesign.range =
    (m22HexadPointwiseKernel a.P.hexad).map M22ValueBound.Concrete.inclusion := by
  have hc := a.radicalDesign.ker.card_mul_index
  rw [index_ker,a.P.E_card] at hc
  have hb := a.radicalDesign_ker_bound
  have hi := a.radicalDesign_range_le
  apply eq_of_le_of_card_ge hi
  rw [card_map_of_injective M22ValueBound.Concrete.inclusion_injective,
    m22HexadPointwiseKernel_card a.P.hexad_mem]
  nlinarith

/-- The original point radical meets the plane core in order 2⁷. -/
theorem radicalDesign_ker_card : Nat.card a.radicalDesign.ker = 128 := by
  have hc := a.radicalDesign.ker.card_mul_index
  rw [index_ker,a.P.E_card,a.radicalDesign_range_eq,
    card_map_of_injective M22ValueBound.Concrete.inclusion_injective,
    m22HexadPointwiseKernel_card a.P.hexad_mem] at hc
  omega
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
