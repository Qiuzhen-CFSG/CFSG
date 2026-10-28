module

public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
public import Theory.GroupTheory.InvolutionCentralizerFourRecognition
public import Theory.GroupTheory.SpecificGroups.DihedralAut
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.Join
public import CFSG.Quasithin.Chapter1.Section01

/-!
# Algebraic reductions in the exceptional A₈ branch

A component containing an A₆ subgroup is relatively normal in a quasithin
ambient group: a distinct conjugate would give commuting A₆ copies. A group
of characteristic two has no components, giving the outside-overgroup step
from the precise centralizer consequence of source 1.1.3(2).

For the two-group reduction, Suzuki's involution-centralizer theorem and a
fourth-power identity exclude every dihedral model larger than D₈ and every
semidihedral model. The fourth-power identity still has to come from the
compatible symmetric-group extension. Finally, the characteristic rotations
of D₈ give the required cyclic four and its central involution.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 2.5.26,
printed pp.568–569. These are conditional algebraic steps; they do not assert
that the symmetric-group extension or its fourth-power input has been proved.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction
variable {G : Type*} [Group G] [Finite G]

/-- A component containing A₆ is normal in the given quasithin group. -/
theorem component_containing_a6_normal (hG : IsQuasithin G)
    (K L : Subgroup G) (eK : K ≃* alternatingGroup (Fin 6))
    (hKL : K ≤ L) (hL : Theory.GroupTheory.IsComponent G L) : L.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra he
  have hc := hL.commutator_eq_bot_of_ne (hL.map_conj g) (Ne.symm he)
  have hKK : ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
    bot_unique ((commutator_mono hKL (map_mono hKL)).trans hc.le)
  exact alternatingGroup.not_commuting_a6_of_quasithin hG K
    (K.map (MulAut.conj g).toMonoidHom) eK
    (((MulAut.conj g).subgroupMap K).symm.trans eK)
    (commutator_eq_bot_iff_le_centralizer.mp hKK)

/-- Relative normality in the involution centralizer, not in the whole group. -/
theorem centralizer_normalizes_component_containing_a6
    (hG : IsQuasithin G) (K L : Subgroup G) (i : G)
    (eK : K ≃* alternatingGroup (Fin 6)) (hKL : K ≤ L)
    (hLi : L ≤ centralizer {i})
    (hL : Theory.GroupTheory.IsComponent (centralizer ({i} : Set G))
      (L.subgroupOf (centralizer {i}))) : centralizer ({i} : Set G) ≤ normalizer L := by
  apply (normal_subgroupOf_iff_le_normalizer hLi).mp
  exact component_containing_a6_normal (hG.subgroup _) _ _
    ((subgroupOfEquivOfLe (hKL.trans hLi)).trans eK)
    (subgroupOf_mono _ hKL) hL

/-- The normal two-core dichotomy excludes a component in characteristic two. -/
theorem no_component_of_characteristicTwo
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (L : Subgroup G) (hL : Theory.GroupTheory.IsComponent G L) : False := by
  have hle : L ≤ pCore 2 G := by
    rcases hL.normal_dichotomy (pCore 2 G) with hle | hc
    · exact hle
    · exact (commutator_eq_bot_iff_le_centralizer.mp hc).trans hchar
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hp : IsPGroup 2 L := (pCore_isPGroup (p := 2) (G := G)).of_injective
    (inclusion hle) (inclusion_injective hle)
  let : Group.IsNilpotent L := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable L inferInstance

/-- The centralizer consequence of 1.1.3(2) excludes containment of the overgroup. -/
theorem overgroup_not_le_of_component_centralizer
    (L I M : Subgroup G) (i : G) (hi : i ∈ I) (hi2 : orderOf i = 2)
    (hLI : L ≤ I) (hLi : L ≤ centralizer {i})
    (hL : Theory.GroupTheory.IsComponent (centralizer ({i} : Set G))
      (L.subgroupOf (centralizer {i})))
    (hn : centralizer ({i} : Set G) ≤ normalizer (L : Set G))
    (h113 : ∀ j : G, j ∈ M → orderOf j = 2 →
      M ⊓ centralizer ({j} : Set G) ∈ CFSG.Quasithin.Chapter1.He G) : ¬ I ≤ M := by
  intro hIM
  let C := M ⊓ centralizer ({i} : Set G)
  have hLC : L ≤ C := le_inf (hLI.trans hIM) hLi
  have hnL : (L.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (inf_le_right.trans hn)
  let := hnL
  let := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLi)
  have hc : Theory.GroupTheory.IsComponent C (L.subgroupOf C) :=
    ⟨Normal.isSubnormal inferInstance,
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLC).symm⟩
  exact no_component_of_characteristicTwo
    (CFSG.Quasithin.Chapter1.mem_He_iff.mp (h113 i (hIM hi) hi2)) _ hc

/-- An exponent-four two-group with a noncentral involution centralizer of order four is D₈. -/
theorem dihedral_of_centralizer_four_of_fourth_power
    (hp : IsPGroup 2 G) (i : G) (hi : orderOf i = 2)
    (hiZ : i ∉ center G) (hC : Nat.card (centralizer ({i} : Set G)) = 4)
    (hfour : ∀ a : G, a ^ 4 = 1) : Nonempty (G ≃* DihedralGroup 4) := by
  have hlarge : 4 < Nat.card G := by
    have hc := card_le_card_group (centralizer ({i} : Set G))
    have hne : Nat.card (centralizer ({i} : Set G)) ≠ Nat.card G := by
      intro hh
      have ht := (centralizer ({i} : Set G)).eq_top_of_card_eq hh
      apply hiZ
      rw [mem_center_iff]
      intro g
      exact mem_centralizer_singleton_iff.mp (ht ▸ mem_top g)
    omega
  rcases exists_dihedral_or_semidihedral_of_involution_centralizer_card_four hp i hi hiZ hC
      with ⟨m, ⟨e⟩⟩ | ⟨n, hn, hcard, a, b, ha, hb, hconj, hgen⟩
  · have hm : m ∣ 4 := by
      have hh := congrArg e (hfour (e.symm (DihedralGroup.r 1)))
      have hd : orderOf (DihedralGroup.r 1 : DihedralGroup m) ∣ 4 :=
        orderOf_dvd_of_pow_eq_one (by simpa using hh)
      simpa only [DihedralGroup.orderOf_r_one] using hd
    have hc := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    have hm4 : m = 4 := by
      have hmle := Nat.le_of_dvd (by decide : 0 < 4) hm
      interval_cases m <;> omega
    subst m
    exact ⟨e⟩
  · have hd : 2 ^ (n - 1) ∣ 4 := ha ▸ orderOf_dvd_of_pow_eq_one (hfour a)
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hge : 8 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ n - 1)
    omega

/-- The source centralizer identity and nontrivial Frattini subgroup supply noncentrality. -/
theorem dihedral_of_involution_centralizer
    (hp : IsPGroup 2 G) (i t : G) (hi : orderOf i = 2) (ht : orderOf t = 2)
    (hit : i ≠ t) (htZ : t ∈ center G)
    (hC : centralizer ({i} : Set G) = zpowers i ⊔ zpowers t)
    (hphi : frattini G ≠ ⊥) (hfour : ∀ a : G, a ^ 4 = 1) :
    Nonempty (G ≃* DihedralGroup 4) := by
  classical
  have hi2 : i ^ 2 = 1 := hi ▸ pow_orderOf_eq_one i
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htc : t ∈ centralizer (zpowers i : Set G) := fun a _ => mem_center_iff.mp htZ a
  have hout : t ∉ zpowers i := by
    intro hm
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hm)
    have hn := Finset.mem_range.mp hn
    rw [hi] at hn
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · have ht1 : t = 1 := by simpa using he.symm
      simp [ht1] at ht
    · exact hit (by simpa using he)
  have hc4 : Nat.card (centralizer ({i} : Set G)) = 4 := by
    rw [hC, card_sup_zpowers_of_normalizing_involution _ t ht2 hout
      (centralizer_le_normalizer _ htc), Nat.card_zpowers, hi]
  have hiZ : i ∉ center G := by
    intro hiz
    have htop : zpowers i ⊔ zpowers t = ⊤ := by
      rw [← hC]
      apply top_unique
      intro a _
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hiz a)
    let : IsElementaryAbelian 2 (zpowers i) := IsElementaryAbelian.zpowers_of_pow_eq_one hi2
    let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
    have he := IsElementaryAbelian.sup_of_le_centralizer (p := 2) (zpowers_le.mpr htc)
    have hpows : ∀ a : G, a ^ 2 = 1 := by
      intro a
      let := he
      exact elemPow_eq_one_of_isElementaryAbelian a (htop ▸ mem_top a)
    let : IsElementaryAbelian 2 G := {
      toIsMulCommutative := ⟨⟨fun a b => by
        have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpows a)
        have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpows b)
        have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpows (a * b))
        simpa only [mul_inv_rev, ha, hb] using hab.symm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpows }
    let : Fact (IsPGroup 2 G) := ⟨hp⟩
    exact hphi ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mpr inferInstance)
  exact dihedral_of_centralizer_four_of_fourth_power hp i hi hiZ hc4 hfour

omit [Finite G] in
/-- The characteristic cyclic four has square t and is preserved by the normalizer of D. -/
theorem cyclicFour_of_dihedral (D : Subgroup G) (e : D ≃* DihedralGroup 4)
    (t : G) (ht : t ∈ D) (ht2 : orderOf t = 2)
    (htZ : (⟨t, ht⟩ : D) ∈ center D) :
    ∃ V : Subgroup G, ∃ v : G, V ≤ D ∧ V = zpowers v ∧ orderOf v = 4 ∧
      v ^ 2 = t ∧ normalizer (D : Set G) ≤ normalizer (V : Set G) := by
  let R := zpowers (DihedralGroup.r 1 : DihedralGroup 4)
  let A := R.map e.symm.toMonoidHom
  let V := A.map D.subtype
  let v : G := e.symm (DihedralGroup.r 1)
  have hchar : A.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro f y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hh := characteristic_iff_le_comap.mp
      (DihedralGroup.rotations_characteristic (by decide : 2 < 4))
      ((e.symm.trans f).trans e) hz
    exact ⟨e (f (e.symm z)), hh, e.symm_apply_apply _⟩
  let := hchar
  have hV : V = zpowers v := by
    simp only [V, A, R, MonoidHom.map_zpowers]
    rfl
  have hv : orderOf v = 4 := by
    change orderOf ((e.symm (DihedralGroup.r 1) : D) : G) = 4
    rw [orderOf_coe, e.symm.orderOf_eq, DihedralGroup.orderOf_r_one]
  have het : e ⟨t, ht⟩ = DihedralGroup.r 2 := by
    have hz := (centerCongr e ⟨⟨t, ht⟩, htZ⟩).property
    change e ⟨t, ht⟩ ∈ center (DihedralGroup 4) at hz
    have ho : orderOf (e ⟨t, ht⟩) = 2 := by rw [e.orderOf_eq]; simpa using ht2
    have hc : ∀ a : DihedralGroup 4, (∀ b, b * a = a * b) →
        a ≠ 1 → a = DihedralGroup.r 2 := by decide +kernel
    exact hc _ (mem_center_iff.mp hz) (by intro he; simp [he] at ho)
  refine ⟨V, v, map_subtype_le _, hV, hv, ?_, ?_⟩
  · have hh : (e.symm (DihedralGroup.r 1)) ^ 2 = (⟨t, ht⟩ : D) := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, het]
      rfl
    exact congrArg Subtype.val hh
  · exact normalizer_le_normalizer_characteristic_image D A
end CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction
