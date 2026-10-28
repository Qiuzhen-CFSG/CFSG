module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.PairNormalization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.ProjectiveTori
public import Theory.SpecificGroups.SU3.IsotropicLineSylowNormalizers
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.PrimeCommutator
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.PrimeCommutator.NinthRoots

/-!
# No Borel contains the noncyclic odd source residual

If an odd subgroup R=[R,t] lies in a Sylow two-normalizer, either t lies
there as well, forcing the commutator into its Sylow two-group, or R lies
in the cyclic intersection of two distinct Borels. Both contradict
noncyclicity. Isotropic-line stabilizers are actual Sylow normalizers, so
this discharges the geometric no-Borel condition in SU₃ and PSU₃.

The carrier applications exclude primes other than three and the paired
order-nine witnesses, with no additional Borel or frame premise.
Source: GLS IV, Chapter 2, Proposition 16.5, terminal odd-residual argument;
Chapter 4, Lemmas 3.2(c–d) and 3.11.
-/

noncomputable section
namespace BenderSuzuki.ZD.NativeSource16
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
open UnitaryThree.OddTorusNormalizer

private theorem not_le_sylow_normalizer_of_full_commutator
    {G : Type*} [Group G] [Finite G] (R : Subgroup G)
    (hodd : Odd (Nat.card R)) (hnoncyclic : ¬ IsCyclic R)
    (t : G) (ht : IsInvolution t) (htR : t∈normalizer R)
    (hcomm : ⁅R,zpowers t⁆=R) (P : Sylow 2 G)
    (hpair : t∉normalizer (P : Set G) →
      IsCyclic (twoPoint (normalizer (P : Set G)) t)) :
    ¬ R≤normalizer (P : Set G) := by
  intro hRN
  by_cases htN : t∈normalizer (P : Set G)
  · have htp : t∈(P : Subgroup G) := by
      have hh : t∈zpowers t ⊓ normalizer (P : Set G) := ⟨mem_zpowers t,htN⟩
      rw [(isPGroup_zpowers_of_involution ht).inf_normalizer_sylow P] at hh
      exact hh.2
    have hRP : R≤(P : Subgroup G) := by
      rw [← hcomm]
      exact (commutator_mono le_rfl (zpowers_le.mpr htp)).trans
        (le_normalizer_iff_commutator_le_right.mp hRN)
    have hp : IsPGroup 2 R := P.isPGroup'.of_injective
      (inclusion hRP) (inclusion_injective hRP)
    rcases hp.card_eq_or_dvd with hc | hc
    · have hbot : R=⊥ := card_eq_one.mp hc
      subst R
      exact hnoncyclic inferInstance
    · exact hodd.not_two_dvd_nat hc
  · let : IsCyclic (twoPoint (normalizer (P : Set G)) t) := hpair htN
    apply hnoncyclic
    apply isCyclic_of_le (show R≤twoPoint (normalizer (P : Set G)) t from ?_)
    intro x hx
    refine ⟨hRN hx, ?_⟩
    refine ⟨t*x*t⁻¹,hRN ((mem_normalizer_iff.mp htR x).mp hx),?_⟩
    change t⁻¹*(t*x*t⁻¹)*(t⁻¹)⁻¹=x
    simp only [inv_inv,inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one]

variable {E : Type*} [Field E] [Finite E]

/-- The genuine noncyclic odd commutator has no isotropic fixed line in SU₃. -/
public theorem special_noBorel_of_full_commutator
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (R : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card R))
    (hnoncyclic : ¬ IsCyclic R) (t : J.specialSubgroup) (ht : orderOf t=2)
    (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R) : SpecialNoBorel J R := by
  have hti : IsInvolution t := ⟨by intro he; simp [he] at ht, ht ▸ pow_orderOf_eq_one t⟩
  intro l hl hRl
  obtain ⟨P,hP⟩ := IsotropicSylow.special_stabilizer J hn hc hf l hl
  exact not_le_sylow_normalizer_of_full_commutator R hodd hnoncyclic t hti htR hcomm P
    (fun ho => (unitary_special_twoPoint_torus J hn hc hf hJ P t hti ho).1) (hP ▸ hRl)

/-- The same no-Borel conclusion in the literal projective unitary carrier. -/
public theorem projective_noBorel_of_full_commutator
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card R))
    (hnoncyclic : ¬ IsCyclic R) (t : ProjectiveSpecialUnitaryMatrixGroup J)
    (ht : orderOf t=2) (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R) :
    ProjectiveNoBorel J R := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hti : IsInvolution t := ⟨by intro he; simp [he] at ht, ht ▸ pow_orderOf_eq_one t⟩
  intro l hl hRl
  obtain ⟨P,hP⟩ := IsotropicSylow.projective_stabilizer J hn hc hf l hl
  exact not_le_sylow_normalizer_of_full_commutator R hodd hnoncyclic t hti htR hcomm P
    (fun ho => (unitary_projective_twoPoint_torus J hn hc hf hJ P t hti ho).1) (hP ▸ hRl)

/-- Away from three, the actual special-unitary full p-commutator is cyclic. -/
public theorem special_pSubgroup_full_commutator_isCyclic
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (R : Subgroup J.specialSubgroup) {p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (hp3 : p≠3) (hR : IsPGroup p R)
    (t : J.specialSubgroup) (ht : orderOf t=2)
    (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R) : IsCyclic R := by
  by_cases hcyc : IsCyclic R
  · exact hcyc
  have hodd : Odd (Nat.card R) := by
    obtain ⟨k,hk⟩ := hR.exists_card_eq
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  exact special_pSubgroup_commutator_isCyclic J hn hc hf R hp2 hp3 hR t ht htR
    (special_noBorel_of_full_commutator J hn hc hf hJ R hodd hcyc t ht htR hcomm) hcomm

/-- The projective carrier version has no geometric placement premise. -/
public theorem projective_pSubgroup_full_commutator_isCyclic
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    {p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hp3 : p≠3) (hR : IsPGroup p R)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t=2)
    (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R) : IsCyclic R := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  by_cases hcyc : IsCyclic R
  · exact hcyc
  have hodd : Odd (Nat.card R) := by
    obtain ⟨k,hk⟩ := hR.exists_card_eq
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  exact projective_pSubgroup_commutator_isCyclic J hn hc hf R hp2 hp3 hR t ht htR
    (projective_noBorel_of_full_commutator J hn hc hf hJ R hodd hcyc t ht htR hcomm) hcomm

/-- The source's opposite order-nine witnesses contradict a noncyclic
special-unitary full commutator; no no-Borel hypothesis remains. -/
public theorem special_full_commutator_false_of_opposite_order_nine
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (R : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card R))
    (hnoncyclic : ¬ IsCyclic R) (t : J.specialSubgroup) (ht : orderOf t=2)
    (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R)
    (x y : J.specialSubgroup) (hxR : x∈R) (hyR : y∈R)
    (hx : orderOf x=9) (hy : orderOf y=9)
    (htx : t*x*t⁻¹=x⁻¹) (hty : t*y*t⁻¹=y⁻¹)
    (a : J.specialSubgroup →* J.specialSubgroup) (hax : a x=x) (hay : a y=y⁻¹) : False := by
  exact special_false_of_opposite_order_nine J hn hc hf R hodd t ht htR
    (special_noBorel_of_full_commutator J hn hc hf hJ R hodd hnoncyclic t ht htR hcomm)
    x y hxR hyR hx hy htx hty a hax hay

/-- The same completed carrier contradiction for PSU₃. -/
public theorem projective_full_commutator_false_of_opposite_order_nine
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card R))
    (hnoncyclic : ¬ IsCyclic R) (t : ProjectiveSpecialUnitaryMatrixGroup J)
    (ht : orderOf t=2) (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R)
    (x y : ProjectiveSpecialUnitaryMatrixGroup J) (hxR : x∈R) (hyR : y∈R)
    (hx : orderOf x=9) (hy : orderOf y=9)
    (htx : t*x*t⁻¹=x⁻¹) (hty : t*y*t⁻¹=y⁻¹)
    (a : ProjectiveSpecialUnitaryMatrixGroup J →* ProjectiveSpecialUnitaryMatrixGroup J)
    (hax : a x=x) (hay : a y=y⁻¹) : False := by
  exact projective_false_of_opposite_order_nine J hn hc hf R hodd t ht htR
    (projective_noBorel_of_full_commutator J hn hc hf hJ R hodd hnoncyclic t ht htR hcomm)
    x y hxR hyR hx hy htx hty a hax hay

end BenderSuzuki.ZD.NativeSource16
