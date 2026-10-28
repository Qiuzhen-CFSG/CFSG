module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.SL2Subgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.FactorPosition.Inverter
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.FactorPosition.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.FactorPosition.TorusAction
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.CharacteristicAbelianIndexTwoNorm

/-!
# Positioning the unitary cyclic factors

The source inverter t lies in N_S(B), has order four, and bases the supplied
SL₂ residual at t². If C_{S ∩ D}(B) is abelian and has index dividing two,
the noncentralizing inverter lies outside this subgroup and its square is
central in S ∩ D. The actual PSU₃ Sylow model has cyclic center. Its unique
central involution agrees with an involution of D ∩ Z(S), giving the required
ambient position without assuming invariance of the supplied SL₂ subgroup.

The final theorem discharges both local torus-action facts. Permutability
and the actual Sylow model give normalization of B by S ∩ D. The faithful
determinant-one degree-three representation then gives an abelian centralizer
of index dividing two in S ∩ D. This positions the cyclic factors without
an extra normalization or matrix-centralizer premise. Centralization of the
residual by the entire Sylow center remains a separate step in the canonical
residual assembly.

Source: Aschbacher--Smith, A.3.15(3), printed pp.50--51, and the proof of
1.3.4, printed pp.510--511 of refs/quasithin.pdf.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
variable {J : Type*} [Group J] [Finite J]

private theorem center_sylow_intersection_cyclic
    (D : Subgroup J) [D.Normal] (S : Sylow 2 J)
    {q : ℕ} [Fact q.Prime] (hq : Odd q) (hmodel : ClassicalGroup.IsPSU D 3 q) :
    IsCyclic (center ((S : Subgroup J) ⊓ D : Subgroup J)) := by
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal D
  let e : T ≃* ((S : Subgroup J) ⊓ D : Subgroup J) :=
    ((T : Subgroup D).equivMapOfInjective D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hT, subgroupOf_map_subtype]))
  let _ := isPSU_sylow_center_cyclic q hq hmodel T
  exact (centerCongr e).isCyclic.mp inferInstance

/-- A central involution of S ∩ D is central in S because its center is cyclic. -/
theorem central_involution_mem_ambient_center
    (D : Subgroup J) [D.Normal] (S : Sylow 2 J)
    {q : ℕ} [Fact q.Prime] (hq : Odd q) (hmodel : ClassicalGroup.IsPSU D 3 q)
    (z : D) (hz : orderOf z = 2) (hzS : (z : J) ∈ (S : Subgroup J))
    (hzc : (⟨z, hzS, z.property⟩ : ((S : Subgroup J) ⊓ D : Subgroup J)) ∈
      center ((S : Subgroup J) ⊓ D : Subgroup J)) :
    (z : J) ∈ centerImage (S : Subgroup J) := by
  obtain ⟨w, hw, hwS⟩ := exists_involution_mem_centerImage D S
    (isPSU_two_dvd_card q hq hmodel)
  obtain ⟨wS, hwSc, hwSv⟩ := hwS
  change (wS : J) = (w : J) at hwSv
  let T : Subgroup J := (S : Subgroup J) ⊓ D
  have hwT : (w : J) ∈ T := ⟨hwSv ▸ wS.property, w.property⟩
  have hwTc : (⟨w, hwT⟩ : T) ∈ center T := by
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    have he := congrArg (fun a : S => (a : J)) (mem_center_iff.mp hwSc ⟨t, t.property.1⟩)
    simpa only [Subgroup.coe_mul, hwSv] using he
  let _ := center_sylow_intersection_cyclic D S hq hmodel
  have he : (⟨⟨z, hzS, z.property⟩, hzc⟩ : center T) = ⟨⟨w, hwT⟩, hwTc⟩ := by
    apply IsCyclic.eq_of_orderOf_eq_two
    · simpa only [← orderOf_coe] using hz
    · simpa only [← orderOf_coe] using hw
  have hzw : (z : J) = w := congrArg (fun a : center T => ((a : T) : J)) he
  rw [hzw]
  exact ⟨wS, hwSc, hwSv⟩

/-- The cyclic factors have the required position once the local torus action
has an abelian kernel and index dividing two. These geometric premises are
explicit; they are not consequences asserted by this conditional assembly. -/
theorem caseThree_factor_position_of_torus_action
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q)
    (habel : IsMulCommutative
      ((centralizer (B : Set J)).subgroupOf ((S : Subgroup J) ⊓ D)))
    (hindex : ((centralizer (B : Set J)).subgroupOf
      ((S : Subgroup J) ⊓ D)).index ∣ 2) :
    ∃ z : D, orderOf z = 2 ∧ (z : J) ∈ centerImage (S : Subgroup J) ∧
      CyclicDecomposition B (involutionResidual D z) := by
  let _ : D.Normal := hA.normal
  obtain ⟨t, ht, htK, _, htnc, z, hzt, hz, hzS, _, hK⟩ :=
    caseThree_inverter_residual hA hC hn hlarge
  let T : Subgroup J := (S : Subgroup J) ⊓ D
  let A : Subgroup T := (centralizer (B : Set J)).subgroupOf T
  let tT : T := ⟨t, ht.1, hC.sl2_inside htK⟩
  have htA : tT ∉ A := htnc
  have hAindex : A.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hindex with he | he
    · have htop : A = ⊤ := index_eq_one.mp he
      exact (htA (htop ▸ mem_top tT)).elim
    · exact he
  let _ : IsMulCommutative A := habel
  have htcenter : tT ^ 2 ∈ center T :=
    sq_mem_center_of_not_mem_abelian_index_two A hAindex tT htA
  have hzcenter : (⟨z, hzS, z.property⟩ : T) ∈ center T := by
    have he : (⟨z, hzS, z.property⟩ : T) = tT ^ 2 := Subtype.ext hzt
    rwa [he]
  refine ⟨z, hz, central_involution_mem_ambient_center D S hC.odd_characteristic
    hC.model z hz hzS hzcenter, ?_⟩
  rw [← hK]
  exact hC.toCyclicDecomposition

/-- In the noncyclic unitary case, the cyclic factors are based at an involution
in the ambient Sylow center. The normalization and torus-action premises are
discharged from the original ambient and case-three hypotheses. -/
theorem caseThree_factor_position
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q) :
    ∃ z : D, orderOf z = 2 ∧ (z : J) ∈ centerImage (S : Subgroup J) ∧
      CyclicDecomposition B (involutionResidual D z) := by
  have hnorm := caseThree_sylow_intersection_le_normalizer hA hC hn hlarge
  obtain ⟨habel, hindex⟩ := caseThree_torus_action hA hC hn hlarge hnorm
  exact caseThree_factor_position_of_torus_action hA hC hn hlarge habel hindex

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
