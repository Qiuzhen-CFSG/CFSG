module
public import Theory.SpecificGroups.Classical.EvenRankTwoOddRank
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MarkSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoNormality
/-! # Original normality in the rank-two field-reduction branches
The literal model supplies odd-prime rank two, including a central two-cover.
The source Gamma group has odd-prime rank at most two; distinct conjugate
components would have rank at least four. Thus the original component is
normal. Applying the marked Sylow projection now gives z in K O₂(H) and
outside O₂(H), without adding normality to the field-reduction hypotheses.
Source: Aschbacher--Smith 2.5.7, first paragraph, printed p.554. -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z:G}
private theorem normal_from_rank (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hr:2≤primeRank p L) :
    (L.subgroupOf H).Normal := by
  have hZ : IsPGroup 2 (center L) := by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  let e : L.subgroupOf H ≃* L := subgroupOfEquivOfLe c.component_le
  apply source_component_normal_of_odd_rank hG.quasithin c.gamma (L.subgroupOf H)
    c.component (hZ.of_equiv (centerCongr e.symm)) p hp ho
  rwa [primeRank_equiv p e]

/-- The first reduction in 2.5.7, including the actual two-primary cover. -/
theorem MathieuSourceSetup.linear_nonbinary_component_normal
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L ⧸ center L ≃* PSL(3,F)) : (L.subgroupOf H).Normal := by
  obtain ⟨p,hp,ho,hr⟩ := Theory.SpecificGroups.Classical.EvenRankTwoOddRank.linear hn hF
  let : Fact p.Prime := ⟨hp⟩
  have hZ : IsPGroup 2 (center L) := by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  have hl : 2≤primeRank p L := by
    rw [← primeRank_quotient_eq_of_isTwoGroup p ho (center L) hZ,primeRank_equiv p e]
    exact hr
  exact normal_from_rank c hG sourceC hempty hp ho hl

/-- The derived symplectic source family has a single original component orbit. -/
theorem MathieuSourceSetup.derived_symplectic_component_normal
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hm:IsDerivedSymplecticFour L) : (L.subgroupOf H).Normal := by
  obtain ⟨F,_,_,n,hn,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply normal_from_rank c hG sourceC hempty Nat.prime_three (by decide)
  rw [primeRank_equiv 3 e]
  exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic

/-- The same conclusion for the literal projective symplectic quotient. -/
theorem MathieuSourceSetup.symplectic_component_normal
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hF:Nat.card F=2^n)
    (e:L ⧸ center L ≃* ClassicalGroup.PSp 2 F) : (L.subgroupOf H).Normal := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hZ : IsPGroup 2 (center L) := by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  apply normal_from_rank c hG sourceC hempty Nat.prime_three (by decide)
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (center L) hZ,primeRank_equiv 3 e]
  exact Theory.SpecificGroups.Classical.EvenRankTwoOddRank.symplectic

/-- The marked product used in the linear field-reduction branch has no
normality premise: its normality follows from the actual model rank. -/
theorem MathieuSourceSetup.linear_nonbinary_marked_product
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L ⧸ center L ≃* PSL(3,F)) : z∈L⊔twoCore H ∧ z∉twoCore H :=
  MathieuSourceSetup.mark_mem_component_sup_twoCore c hG sourceC hempty hgen
    (MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF e)

/-- The same marked product for the full derived symplectic source family. -/
theorem MathieuSourceSetup.derived_symplectic_marked_product
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hm:IsDerivedSymplecticFour L) : z∈L⊔twoCore H ∧ z∉twoCore H :=
  MathieuSourceSetup.mark_mem_component_sup_twoCore c hG sourceC hempty hgen
    (MathieuSourceSetup.derived_symplectic_component_normal c hG sourceC hempty hm)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
