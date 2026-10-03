module

public import ABG.Recognition.ThreeMathieuFixedSpaces
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Theory.GroupTheory.SelfCentralizingFiveNormalizer
public import ABG.ChapterII.Section1.OrderFourQuaternion
public import ABG.ChapterII.Section1.SemidihedralEquiv

/-!
# Wong's local subgroup configuration and fixed dimensions

Schur–Zassenhaus and the faithful normalizer action on the five-subgroup
produce a cyclic four-complement. Order-four conjugacy in a containing
semidihedral Sylow subgroup puts this complement in a conjugate quaternion
subgroup, with an actual equivalence to the quaternion model.

The first character of the shared catalog has sums 40, 24, and 16 on the
Sylow-five normalizer, a quaternion eight-subgroup, and a cyclic four-subgroup.
Averaging gives fixed dimensions two, three, and four. A common four-subgroup
then forces the join of the first two subgroups to be proper.

Source: Wong (1964), Theorem 6(a), pp.107–108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open scoped BigOperators
noncomputable section

/-- Every cyclic four-subgroup is contained in a quaternion eight-subgroup. -/
private theorem exists_quaternion_over_cyclic_four
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (F : Subgroup G) [IsCyclic F] (hF : Nat.card F = 4) :
    ∃ Q : Subgroup G, F ≤ Q ∧ Nonempty (Q ≃* QuaternionGroup 2) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFtwo : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by simpa using hF)
  obtain ⟨T, hFT⟩ := hFtwo.exists_le_sylow
  have hT : Stellmacher.IsSemidihedralGroup T := semidihedral_equiv (S.equiv T) hS
  obtain ⟨U, hU, _⟩ := QuasiDihedral.quaternion_subgroups hT
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic F)
  have hx4 : orderOf x = 4 := (orderOf_eq_card_of_zpowers_eq_top hx).trans hF
  let xT : T := ⟨x, hFT x.property⟩
  have hxT : orderOf xT = 4 := by
    rw [← Subgroup.orderOf_coe, Subgroup.orderOf_coe x]
    exact hx4
  obtain ⟨y, hxy⟩ := QuasiDihedral.order_four_conjugate_into_quaternion hT U hU xT hxT
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let f : T →* G := (T : Subgroup G).subtype.comp (MulAut.conj g⁻¹).toMonoidHom
  have hf : Function.Injective f :=
    (T : Subgroup G).subtype_injective.comp (MulAut.conj g⁻¹).injective
  let Q := U.map f
  have hxQ : (x : G) ∈ Q := by
    apply Subgroup.mem_map.mpr
    refine ⟨y, y.property, ?_⟩
    change ((g⁻¹ * (y : T) * (g⁻¹)⁻¹ : T) : G) = (x : G)
    rw [← hg]
    simp [mul_assoc, xT]
  have hgen : Subgroup.zpowers (x : G) = F := by
    have hh := congrArg (Subgroup.map F.subtype) hx
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.subtype_apply] using hh
  obtain ⟨eU⟩ := hU
  exact ⟨Q, hgen ▸ Subgroup.zpowers_le.mpr hxQ,
    ⟨(U.equivMapOfInjective f hf).symm.trans eU⟩⟩

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)

include S hS

/-- On any subgroup of exponent dividing four, only the identity has character
value different from two. -/
public theorem ThreeGlobalDegreeData.first_character_sum_exponent_four
    (hG : Nat.card G = 7920) (H : Subgroup G) [Fintype H]
    (hexp : ∀ x : H, orderOf x ∣ 4) :
    ∑ x : H, c.decomposition.χ 0 (x : G) = 2 * (Nat.card H : ℂ) + 8 := by
  classical
  have hval (x : H) : c.decomposition.χ 0 (x : G) =
      2 + if x = 1 then 8 else 0 := by
    by_cases hx : x = 1
    · subst x
      norm_num [c.first_character_identity hG]
    · have ho := hexp x
      have hone : orderOf x ≠ 1 := fun hh => hx (orderOf_eq_one_iff.mp hh)
      have hord : orderOf (x : G) = 2 ∨ orderOf (x : G) = 4 := by
        rw [Subgroup.orderOf_coe]
        have hb : orderOf x ≤ 4 := Nat.le_of_dvd (by decide) ho
        interval_cases hh : orderOf x <;> simp_all
      rw [c.first_character_order_two_or_four S hS x hord, if_neg hx, add_zero]
  simp_rw [hval]
  simp [Finset.sum_add_distrib, Nat.card_eq_fintype_card, mul_comm]

/-- The character sum on a four-subgroup is sixteen. -/
public theorem ThreeGlobalDegreeData.first_character_sum_four
    (hG : Nat.card G = 7920) (F : Subgroup G) [Fintype F]
    (hF : Nat.card F = 4) :
    ∑ x : F, c.decomposition.χ 0 (x : G) = 16 := by
  have h := c.first_character_sum_exponent_four S hS hG F
    (fun x => hF ▸ orderOf_dvd_natCard x)
  rw [hF] at h
  norm_num at h
  exact h

/-- The quaternion model gives both order eight and character sum twenty-four. -/
public theorem ThreeGlobalDegreeData.first_character_sum_quaternion
    (hG : Nat.card G = 7920) (Q : Subgroup G) [Fintype Q]
    (e : Q ≃* QuaternionGroup 2) :
    Nat.card Q = 8 ∧ ∑ x : Q, c.decomposition.χ 0 (x : G) = 24 := by
  have hQ : Nat.card Q = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  refine ⟨hQ, ?_⟩
  have h := c.first_character_sum_exponent_four S hS hG Q (fun x => by
    rw [← e.orderOf_eq x]
    have hd := Monoid.order_dvd_exponent (e x)
    simpa [QuaternionGroup.exponent] using hd)
  rw [hQ] at h
  norm_num at h
  exact h

omit S hS [Finite G] [IsSimpleGroup G] in
/-- All order-five elements in the normalizer already belong to the Sylow
five-subgroup. This uses the Sylow property, not an assumed element census. -/
private theorem mem_five_of_order_five (P : Sylow 5 G)
    (x : Subgroup.normalizer ((P : Subgroup G) : Set G)) (hx : orderOf (x : G) = 5) :
    (x : G) ∈ (P : Subgroup G) := by
  let H := Subgroup.zpowers (x : G)
  have hH : IsPGroup 5 H := IsPGroup.of_card (n := 1) (by
    simpa [H, Nat.card_zpowers] using hx)
  have hle : H ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr x.property
  have hHP : H ≤ (P : Subgroup G) := by
    have hh := hH.inf_normalizer_sylow P
    change H ⊓ Subgroup.normalizer ((P : Subgroup G) : Set G) = H ⊓ (P : Subgroup G) at hh
    rw [inf_eq_left.mpr hle] at hh
    exact inf_eq_left.mp hh.symm
  exact hHP (Subgroup.mem_zpowers (x : G))

/-- The character sum over the order-twenty normalizer is forty. -/
public theorem ThreeGlobalDegreeData.first_character_sum_five_normalizer
    (hG : Nat.card G = 7920) (P : Sylow 5 G)
    [Fintype (Subgroup.normalizer ((P : Subgroup G) : Set G))] :
    ∑ x : Subgroup.normalizer ((P : Subgroup G) : Set G),
      c.decomposition.χ 0 (x : G) = 40 := by
  classical
  let N := Subgroup.normalizer ((P : Subgroup G) : Set G)
  let PN := (P : Subgroup G).subgroupOf N
  let : Fintype PN := Fintype.ofFinite PN
  have hN : Nat.card N = 20 := c.mathieu_sylow_five_normalizer_card S hS hG P
  have hP : Nat.card P = 5 := mathieu_sylow_five_card hG P
  have hPN : Nat.card PN = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show (P : Subgroup G) ≤ N from Subgroup.le_normalizer)).toEquiv]
    exact hP
  have hval (x : N) : c.decomposition.χ 0 (x : G) =
      2 + (if x = 1 then 10 else 0) - (if x ∈ PN then 2 else 0) := by
    by_cases hx : x = 1
    · subst x
      norm_num [c.first_character_identity hG]
    · have hxG : (x : G) ≠ 1 := by simpa using hx
      have ho1 : orderOf (x : G) ≠ 1 := by simpa using hxG
      by_cases hxP : x ∈ PN
      · have horder : orderOf (x : G) = 5 := by
          have hxP' : (x : G) ∈ (P : Subgroup G) := hxP
          have hd := orderOf_dvd_natCard (⟨(x : G), hxP'⟩ : (P : Subgroup G))
          rw [← Subgroup.orderOf_coe, hP] at hd
          exact (Nat.dvd_prime (by decide)).mp hd |>.resolve_left ho1
        rw [c.first_character_order_five S hS hG x horder, if_neg hx, if_pos hxP]
        norm_num
      · have hd : orderOf (x : G) ∣ 20 := by
          rw [Subgroup.orderOf_coe]
          exact hN ▸ orderOf_dvd_natCard x
        have he := c.mathieu_order_exhaustion S hS hG (x : G)
        have hfive : orderOf (x : G) ≠ 5 := fun hh => hxP (mem_five_of_order_five P x hh)
        have hord : orderOf (x : G) = 2 ∨ orderOf (x : G) = 4 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with h | h | h | h | h | h | h | h <;>
            first | exact Or.inl h | exact Or.inr h | contradiction | (norm_num [h] at hd)
        rw [c.first_character_order_two_or_four S hS x hord, if_neg hx, if_neg hxP]
        ring
  have hsumPN : (∑ x : N, if x ∈ PN then (2 : ℂ) else 0) = 10 := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := fun x : N => x ∈ PN) (F := (inferInstance : Fintype PN)) _ (by simp)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card, hPN]
    norm_num
  simp_rw [hval]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsumPN]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hn : Fintype.card N = 20 := (Nat.card_eq_fintype_card.symm.trans hN)
  change (Fintype.card N : ℂ) * 2 + 10 - 10 = 40
  rw [hn]
  norm_num

/-- Wong's local configuration, with the original first character and an
actual quaternion model. The three fixed dimensions force a proper join. -/
public theorem ThreeGlobalDegreeData.exists_mathieu_local_configuration
    (hG : Nat.card G = 7920) (P : Sylow 5 G) :
    let N := Subgroup.normalizer ((P : Subgroup G) : Set G)
    ∃ (F Q : Subgroup G) (_e : Q ≃* QuaternionGroup 2)
      (ρ : Representation ℂ G (Fin 10 → ℂ)),
      IsCyclic F ∧ Nat.card F = 4 ∧ F ≤ N ∧
      (P : Subgroup G) ⊓ F = ⊥ ∧ (P : Subgroup G) ⊔ F = N ∧
      F ≤ Q ∧ Nat.card Q = 8 ∧
      c.decomposition.χ 0 = ρ.character ∧
      Module.finrank ℂ (Representation.invariants (ρ.comp N.subtype)) = 2 ∧
      Module.finrank ℂ (Representation.invariants (ρ.comp Q.subtype)) = 3 ∧
      Module.finrank ℂ (Representation.invariants (ρ.comp F.subtype)) = 4 ∧
      Q ⊔ N ≠ ⊤ := by
  classical
  let N := Subgroup.normalizer ((P : Subgroup G) : Set G)
  have hN : Nat.card N = 20 := c.mathieu_sylow_five_normalizer_card S hS hG P
  obtain ⟨F, hFcyc, hF, hFN, hPF, hgen⟩ :=
    (P : Subgroup G).exists_cyclic_four_complement_of_card_twenty
      (mathieu_sylow_five_card hG P)
      (c.mathieu_sylow_five_self_centralizing S hS hG P) hN
  let : IsCyclic F := hFcyc
  obtain ⟨Q, hFQ, ⟨e⟩⟩ := exists_quaternion_over_cyclic_four S hS F hF
  obtain ⟨ρ, _, hχ⟩ := c.exists_first_mathieu_representation hG
  let : Fintype N := Fintype.ofFinite N
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Q := Fintype.ofFinite Q
  obtain ⟨hQ, hsumQ⟩ := c.first_character_sum_quaternion S hS hG Q e
  have hdimN : Module.finrank ℂ (Representation.invariants (ρ.comp N.subtype)) = 2 := by
    apply c.first_mathieu_fixed_dimension ρ hχ N 2
    rw [c.first_character_sum_five_normalizer S hS hG P, hN]
    norm_num
  have hdimQ : Module.finrank ℂ (Representation.invariants (ρ.comp Q.subtype)) = 3 := by
    apply c.first_mathieu_fixed_dimension ρ hχ Q 3
    rw [hsumQ, hQ]
    norm_num
  have hdimF : Module.finrank ℂ (Representation.invariants (ρ.comp F.subtype)) = 4 := by
    apply c.first_mathieu_fixed_dimension ρ hχ F 4
    rw [c.first_character_sum_four S hS hG F hF, hF]
    norm_num
  exact ⟨F, Q, e, ρ, hFcyc, hF, hFN, hPF, hgen, hFQ, hQ, hχ,
    hdimN, hdimQ, hdimF,
    c.mathieu_sup_ne_top_of_fixed_dimensions ρ hχ Q N F hFQ hFN hdimQ hdimN hdimF⟩

end
end ABG
