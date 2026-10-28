module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.SL2Subgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.Inverter
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.SylowModel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.TorusAction
public import Theory.GroupTheory.CharacteristicAbelianIndexTwoNorm

/-!
# Positioning the linear cyclic factors

Let T = S ∩ D. The source inverter is in N_S(B) and does not centralize B.
If C_T(B) is abelian with index dividing two, that index is exactly two,
and the inverter's square is central in T. The square is nonidentity, so
one of its powers is the unique involution of the supplied SL₂ subgroup.
Cyclicness of Z(T) identifies this involution with the existing involution
of D ∩ Z(S). The residual identification then gives the cyclic decomposition
at this very ambient-central involution.

Normalization of B by T follows from BS = SB and the semidihedral-or-wreathed
Sylow model. The degree-three calculation then proves the two local action
facts for this normalizing two-subgroup. The final theorem discharges both
premises of the conditional assembly from `AmbientInput` and `CaseThree`.

The index-two and cyclic-center strategy is adapted from the parallel
`OddCartan.UnitaryPosition.FactorPosition` proof. Uniqueness of the SL₂
involution permits using a central power without a trace calculation.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, and the proof of
1.3.4, printed pp.510–511 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J] [Finite J]

private theorem linear_center_sylow_intersection_cyclic
    (D : Subgroup J) [D.Normal] (S : Sylow 2 J)
    {q : ℕ} [Fact q.Prime] (hq : Odd q) (hmodel : ClassicalGroup.IsPSL D 3 q) :
    IsCyclic (center ((S : Subgroup J) ⊓ D : Subgroup J)) := by
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal D
  let e : T ≃* ((S : Subgroup J) ⊓ D : Subgroup J) :=
    ((T : Subgroup D).equivMapOfInjective D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hT, subgroupOf_map_subtype]))
  let _ := isPSL_sylow_center_cyclic hq hmodel T
  exact (centerCongr e).isCyclic.mp inferInstance

/-- A central involution of the restricted Sylow lies in the whole ambient Sylow center. -/
theorem linear_central_involution_mem_ambient_center
    (D : Subgroup J) [D.Normal] (S : Sylow 2 J)
    {q : ℕ} [Fact q.Prime] (hq : Odd q) (hmodel : ClassicalGroup.IsPSL D 3 q)
    {z : J} (hzD : z ∈ D) (hz : orderOf z = 2) (hzS : z ∈ S)
    (hzc : (⟨z, hzS, hzD⟩ : ((S : Subgroup J) ⊓ D : Subgroup J)) ∈
      center ((S : Subgroup J) ⊓ D : Subgroup J)) :
    z ∈ centerImage (S : Subgroup J) := by
  have hD : 2 ∣ Nat.card D := by
    have hd := orderOf_dvd_natCard (⟨z, hzD⟩ : D)
    simpa only [← orderOf_coe, hz] using hd
  obtain ⟨w, hw, hwo⟩ := exists_involution_mem_centerImage D S hD
  obtain ⟨wS, hwSc, hwSv⟩ := hw.2
  change (wS : J) = w at hwSv
  let T : Subgroup J := (S : Subgroup J) ⊓ D
  have hwT : w ∈ T := ⟨hwSv ▸ wS.property, hw.1⟩
  have hwTc : (⟨w, hwT⟩ : T) ∈ center T := by
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    have he := congrArg (fun a : S => (a : J)) (mem_center_iff.mp hwSc ⟨t, t.property.1⟩)
    simpa only [Subgroup.coe_mul, hwSv] using he
  let _ := linear_center_sylow_intersection_cyclic D S hq hmodel
  have he : (⟨⟨z, hzS, hzD⟩, hzc⟩ : center T) = ⟨⟨w, hwT⟩, hwTc⟩ := by
    apply IsCyclic.eq_of_orderOf_eq_two
    · simpa only [← orderOf_coe] using hz
    · simpa only [← orderOf_coe] using hwo
  have hzw : z = w := congrArg (fun a : center T => ((a : T) : J)) he
  rw [hzw]
  exact hw.2

/-- Conditional assembly from the actual local torus action. -/
theorem CaseThree.linear_factorPosition_of_torus_action
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .linear .linear)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q)
    (habel : IsMulCommutative
      ((centralizer (B : Set J)).subgroupOf ((S : Subgroup J) ⊓ D)))
    (hindex : ((centralizer (B : Set J)).subgroupOf
      ((S : Subgroup J) ⊓ D)).index ∣ 2) :
    ∃ z ∈ D ⊓ centerImage (S : Subgroup J), orderOf z = 2 ∧
      CyclicDecomposition B (involutionResidual D z) := by
  let _ : D.Normal := hA.normal
  obtain ⟨t, ht, htK, hi⟩ := hC.exists_normalizing_inverter
  have htnc := hC.toCyclicDecomposition.inverter_not_centralizing hA.p_group hA.odd hn hi
  have ht2 := hC.inverter_sq_ne_one hA.p_group hA.odd hn htK hi
  obtain ⟨e⟩ := hC.sl2
  obtain ⟨z, hzc, hz⟩ := sl2_exists_central_involution K q hC.odd_characteristic e
  have hzD : (z : J) ∈ D := hC.sl2_inside z.property
  have hzj : orderOf (z : J) = 2 := by simpa only [← orderOf_coe] using hz
  have hzS := hC.sl2_central_involution_mem_sylow hA.p_group hA.odd hn z hz
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
  have hT : IsPGroup 2 T :=
    S.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have htT2 : tT ^ 2 ≠ 1 := fun he => ht2 (congrArg Subtype.val he)
  let n := orderOf (tT ^ 2) / 2
  have hwo : orderOf ((tT ^ 2) ^ n) = 2 := orderOf_pow_orderOf_div
    (orderOf_pos (tT ^ 2)).ne' (hT.dvd_orderOf htT2)
  let w : K := ⟨(t ^ 2) ^ n, K.pow_mem (K.pow_mem htK 2) n⟩
  have hw : orderOf w = 2 := (Subgroup.orderOf_coe w).symm.trans
    ((Subgroup.orderOf_coe ((tT ^ 2) ^ n)).trans hwo)
  have hzw : z = w := e.injective (sl2_involutions_equal q hC.odd_characteristic
    (e z) (e w) ((e.orderOf_eq z).trans hz) ((e.orderOf_eq w).trans hw))
  have hzcenter : (⟨z, hzS, hzD⟩ : T) ∈ center T := by
    have he : (⟨z, hzS, hzD⟩ : T) = (tT ^ 2) ^ n :=
      Subtype.ext (congrArg (fun a : K => (a : J)) hzw)
    rw [he]
    exact (center T).pow_mem htcenter n
  refine ⟨z, ⟨hzD, linear_central_involution_mem_ambient_center D S
    hC.odd_characteristic hC.model hzD hzj hzS hzcenter⟩, hzj, ?_⟩
  rw [← sl2_eq_involutionResidual D K hC.sl2_inside q hC.odd_characteristic
    hlarge hC.model e z hzc hz]
  exact hC.toCyclicDecomposition

/-- The linear cyclic factors are based at an involution in the ambient Sylow center. -/
theorem CaseThree.linear_factorPosition
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .linear .linear)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q) :
    ∃ z ∈ D ⊓ centerImage (S : Subgroup J), orderOf z = 2 ∧
      CyclicDecomposition B (involutionResidual D z) := by
  have hnorm := hC.linear_sylow_inf_le_normalizer hA hn hlarge
  obtain ⟨habel, hindex⟩ := hC.linear_torus_action hA hn hlarge hnorm
  exact hC.linear_factorPosition_of_torus_action hA hn hlarge habel hindex

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
