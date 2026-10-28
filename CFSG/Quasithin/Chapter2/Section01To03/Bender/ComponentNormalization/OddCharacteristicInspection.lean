module

public import Theory.GroupTheory.MarkedInnerStrongClosure
public import Theory.SpecificGroups.OddCharacteristic.InvolutionFusion
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization
public import GorensteinWalter.LinearThreeEquiv
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The inner odd-characteristic row in the Bender component inspection

The original z acts nontrivially on L because source 1.1.5 supplies L not≤M
and the selected witness has C_G(z)≤M. Its inner implementer therefore has
order two. Strong closure of the original U makes all component conjugates
of that implementer in S∩L commute, even when U is not contained in L.
The proved dihedral and semidihedral configurations contradict this for
PSL₂(p), p≥7, and PSL₃(3). Perfectness excludes PSL₂(3); the adjacent-power
prime alternative therefore leaves exactly PSL₂(5), the legitimate A5 case.

The source owner retains the actual row selection, marked innerness,
L not≤M, and preceding Sylow placement. No additional fusion or
classification premise is present in the specialized consumers.

Source: Aschbacher--Smith 1.1.5(3)(e), pp.501--503, and the inspection in
Proposition 2.2.2, printed pp.519--520 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

private theorem false_of_inner_component_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    {K : Type*} [Group K] (e : L ≃* K) (hcK : center K = ⊥)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹)
    (hclass : ∀ a b : K, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hpair : ∀ P : Sylow 2 K,
      ∃ a b : P, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬Commute a b) : False := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let S' : Subgroup G := (S : Subgroup H).map H.subtype
  have hU : IsStronglyClosedSet (w.U : Set G) S' ⊤ :=
    ⟨hUS, fun x hx g hg hgs => w.strongly_closed.2 x hx g hg (hST hgs)⟩
  obtain ⟨P0, hP0⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) hL.2.1
  let e0 : (L.subgroupOf H) ≃* K := (subgroupOfEquivOfLe hL.1).trans e
  let P := P0.mapSurjective (f := e0.toMonoidHom) e0.surjective
  let f : K →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hPS : (P : Subgroup K).map f ≤ S' := by
    rintro _ ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    change (e.symm (e ((subgroupOfEquivOfLe hL.1) x)) : G) ∈ S'
    rw [e.symm_apply_apply]
    have hxS : (x : H) ∈ (S : Subgroup H) := by
      change x ∈ (S : Subgroup H).subgroupOf (L.subgroupOf H)
      rw [← hP0]
      exact hx
    exact mem_map_of_mem H.subtype hxS
  obtain ⟨t, ht⟩ := hinner
  have htn : e t ≠ 1 := by
    intro he
    have ht1 : t = 1 := e.injective (he.trans (map_one e).symm)
    apply hLM
    intro x hx
    apply w.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hh := ht ⟨x, hx⟩
    rw [ht1] at hh
    simp only [one_mul, inv_one, mul_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  apply MarkedInnerStrongClosure.false_of_involution_fusion S' w.U hU f hf hcK P hPS
    w.z w.z_mem (w.z_order ▸ pow_orderOf_eq_one w.z)
    (fun s hs => w.z_central s (hST hs)) (e t) htn
    (fun x => ?_) hclass (hpair P)
  change (e.symm (e t * x * (e t)⁻¹) : G) = w.z * (e.symm x : G) * w.z⁻¹
  simpa only [map_mul, map_inv, e.symm_apply_apply] using ht (e.symm x)

/-- The marked inner PSL₃(3) component in source row (e) is impossible. -/
theorem LocalControlWitness.false_of_inner_psl3_three_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : L ≃* Matrix.PSL3Three.PSL)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply false_of_inner_component_model w H S hUS hST L hL hLM
    (e.trans Matrix.PSL3Three.equiv.symm) Matrix.PSL3Three.center_eq_bot hinner
    (fun a b ha hb => Matrix.SL3.involutions_isConj (ZMod 3) a b ha hb (by decide))
    OddCharacteristicInvolutionFusion.sl3_three_pair

/-- The marked inner PSL₂(p) case with p≥7 is impossible. The four-group
Sylow of PSL₂(5) is not covered by this exclusion. -/
theorem LocalControlWitness.false_of_inner_psl2_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    {p k : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) (e : L ≃* PSL(2, ZMod p))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  exact false_of_inner_component_model w H S hUS hST L hL hLM e
    (GorensteinWalter.psl2_center_eq_bot (ZMod p)) hinner
    (fun a b ha hb => Theory.PSL2.involutions_isConj a b ha hb)
    (OddCharacteristicInvolutionFusion.psl2_pair hp7 hpk)

/-- The prime-field part of source row (e) reduces to exactly PSL₂(5).
Oddness and the adjacent-power equation are the Fermat/Mersenne arithmetic. -/
theorem LocalControlWitness.prime_eq_five_of_inner_psl2_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    {p k : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) (e : L ≃* PSL(2, ZMod p))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : p = 5 := by
  have hp7 : p < 7 := by
    by_contra! hh
    exact w.false_of_inner_psl2_component H S hUS hST L hL hLM hh hpk e hinner
  have hp2 := (Fact.out : p.Prime).two_le
  have hpne2 : p ≠ 2 := by
    intro h
    subst p
    exact hpodd.not_two_dvd_nat (dvd_refl 2)
  have hpne3 : p ≠ 3 := by
    intro h
    subst p
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let eA := e.trans GorensteinWalter.psl2_three_equiv_alternatingGroup
    have hsolv : Group.IsSolvable L :=
      Group.isSolvable_of_surjective (f := eA.symm.toMonoidHom) eA.symm.surjective
    let : IsQuasisimple L := hL.quasisimple
    let : Nontrivial L := (nontrivial_iff_ne_bot L).mpr hL.ne_bot
    exact Group.IsPerfect.not_isSolvable L hsolv
  obtain ⟨j, hj⟩ := hpodd
  omega

end CFSG.Quasithin.Chapter2.BenderFusion
