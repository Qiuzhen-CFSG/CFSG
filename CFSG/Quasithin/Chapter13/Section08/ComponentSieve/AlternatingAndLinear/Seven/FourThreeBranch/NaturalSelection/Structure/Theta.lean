module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The relative stabilizer and local rank from theta

The order-three lifts supplied by 13.8.13 and the theta identity put both
(0 1 2) and (0 1 3) in the image of L₁. Since H ∩ M normalizes theta, its
image conjugates these cycles into the four-plus-three stabilizer. Their
overlapping supports force preservation of the four-point block, proving
the previously missing reverse containment in the relative stabilizer.

The disjoint cycles (0 1 2) and (4 5 6) give an elementary nine in the same
image. Lifting through the actual two-group kernel constructs an elementary
nine in L₁ itself. The partition order bounds its three-rank above by two;
the earlier ordinary-A₆ local calculation then selects the actual covered
quotient. Neither reverse containment nor a rank-two witness is an input.

Source: Aschbacher–Smith, 13.7.3(9), 13.7.5, 13.8.13 and 13.8.24,
printed pp.936, 938, 950–951 and 958 (1 March 2004 manuscript).
-/

public section
open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
open LocalGeometry PairsBranch.LocalRank

private def cycle013 : S7 := swap 0 1 * swap 1 3

private theorem cycle013_isThreeCycle : Equiv.Perm.IsThreeCycle cycle013 := by
  rw [← card_support_eq_three_iff]
  decide +kernel

private theorem block_mem_iff (g : S7) (hg : g ∈ fourThreeStabilizer) (i : Fin 7) :
    (g i).val < 4 ↔ i.val < 4 := by
  have h := (mem_fourThreeStabilizer_iff g).mp hg
  have hi := (mem_fourThreeStabilizer_iff g⁻¹).mp (fourThreeStabilizer.inv_mem hg)
  rw [fourBlock_eq] at h hi
  exact ⟨fun hx => by simpa using hi hx, fun hx => h hx⟩

private theorem mem_fourThree_of_conjugate_cycles (s : S7)
    (h012 : s * cycle012 * s⁻¹ ∈ fourThreeStabilizer)
    (h013 : s * cycle013 * s⁻¹ ∈ fourThreeStabilizer) :
    s ∈ fourThreeStabilizer := by
  have h01 : (s 1).val < 4 ↔ (s 0).val < 4 := by
    simpa [cycle012, Perm.mul_apply, swap_apply_def] using block_mem_iff _ h012 (s 0)
  have h12 : (s 2).val < 4 ↔ (s 1).val < 4 := by
    simpa [cycle012, Perm.mul_apply, swap_apply_def] using block_mem_iff _ h012 (s 1)
  have h13 : (s 3).val < 4 ↔ (s 1).val < 4 := by
    simpa [cycle013, Perm.mul_apply, swap_apply_def] using block_mem_iff _ h013 (s 1)
  have hd (i j : Fin 7) (hij : i ≠ j) : (s i).val ≠ (s j).val := by
    intro he
    exact hij (s.injective (Fin.ext he))
  have h01' := hd 0 1 (by decide)
  have h02' := hd 0 2 (by decide)
  have h03' := hd 0 3 (by decide)
  have h12' := hd 1 2 (by decide)
  have h13' := hd 1 3 (by decide)
  have h23' := hd 2 3 (by decide)
  have h0 : (s 0).val < 4 := by omega
  rw [mem_fourThreeStabilizer_iff, fourBlock_eq]
  intro i hi
  have hi' : i.val < 4 := hi
  fin_cases i
  · exact h0
  · exact h01.mpr h0
  · exact h12.mpr (h01.mpr h0)
  · exact h13.mpr (h01.mpr h0)
  · norm_num at hi'
  · norm_num at hi'
  · norm_num at hi'

private theorem theta_normalized {G : Type*} [Group G] (J : Subgroup G) :
    J ≤ normalizer (closure {x : G | x ∈ J ∧ orderOf x = 3} : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  apply Subgroup.subset_closure
  refine ⟨J.mul_mem (J.mul_mem hg hx.1) (J.inv_mem hg), ?_⟩
  exact (MulAut.conj g).orderOf_eq x |>.trans hx.2

variable {G : Type*} [Group G] [Finite G]

/-- The theta identity and solvable-overgroup implication identify the actual
relative stabilizer, without assuming its reverse containment. -/
theorem relativeStabilizer_eq_inter_of_theta
    (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ) :
    relativeStabilizer H φ = H ⊓ M := by
  apply relativeStabilizer_eq_inter H L₁ T G₁ M hbase hHG h13 φ hφ hP
  rintro _ ⟨g, hg, rfl⟩
  let q : H →* Source.Hstar H := QuotientGroup.mk' (pCore 2 H)
  let f := φ.comp q
  have hn : g.val ∈ normalizer (L₁ : Set G) := by
    rw [htheta]
    exact theta_normalized (H ⊓ M) hg
  have hc (c : S7) (hcP : c ∈ fourThreeStabilizer)
      (hc3 : Equiv.Perm.IsThreeCycle c) : f g * c * (f g)⁻¹ ∈ fourThreeStabilizer := by
    obtain ⟨a, ⟨x, hx, rfl⟩, hxc⟩ := even_order_three_mem_local_image H L₁ T G₁ M
      hbase hHG htheta h13 φ hφ hAlt hP c hcP hc3.mem_alternatingGroup hc3.orderOf
    have hcL : (g * x * g⁻¹).val ∈ L₁ := (mem_normalizer_iff.mp hn x.val).mp hx
    have hcstar : q (g * x * g⁻¹) ∈ Source.starImage H (L₁ ⊔ T) :=
      ⟨g * x * g⁻¹, (show L₁ ≤ L₁ ⊔ T from le_sup_left) hcL, rfl⟩
    have := hP hcstar
    change f (g * x * g⁻¹) ∈ fourThreeStabilizer at this
    simpa only [map_mul, map_inv, show f x = c from hxc] using this
  exact mem_fourThree_of_conjugate_cycles (f g)
    (hc cycle012 (by decide +kernel) cycle012_isThreeCycle)
    (hc cycle013 (by decide +kernel) cycle013_isThreeCycle)

private theorem cubicNine_data :
    IsElementaryAbelian 3 (zpowers cycle012 ⊔ zpowers cycle456 : Subgroup S7) ∧
      Nat.card (zpowers cycle012 ⊔ zpowers cycle456 : Subgroup S7) = 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsElementaryAbelian 3 (zpowers cycle012) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one
      (cycle012_isThreeCycle.orderOf ▸ pow_orderOf_eq_one cycle012)
  have hnot : cycle456 ∉ zpowers cycle012 := by
    have hfix : zpowers cycle012 ≤ fixingSubgroup S7 ({4} : Set (Fin 7)) := by
      apply zpowers_le.mpr
      apply (mem_fixingSubgroup_iff S7).mpr
      intro i hi
      have hi : i = 4 := hi
      subst i
      decide +kernel
    intro h
    have := (mem_fixingSubgroup_iff S7).mp (hfix h) 4 (by simp)
    exact (by decide +kernel : cycle456 4 ≠ 4) this
  have hdis := disjoint_zpowers_of_prime_order_not_mem (zpowers cycle012)
    cycle456 cycle456_isThreeCycle.orderOf hnot
  have hcentral : zpowers cycle012 ≤ centralizer ({cycle456} : Set S7) := by
    apply zpowers_le.mpr
    rw [mem_centralizer_singleton_iff]
    decide +kernel
  exact IsElementaryAbelian.fixed_join_card (n := 1) (zpowers cycle012) cycle456
    cycle456_isThreeCycle.orderOf hdis hcentral
    (by rw [Nat.card_zpowers, cycle012_isThreeCycle.orderOf]; norm_num)

/-- The two disjoint cubic cycles lift to an actual elementary nine in L₁.
The lifting kernel is the intersection with O₂(H), not O₂(L₁). -/
theorem local_elementaryNine_of_theta
    (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ) :
    ∃ E : Subgroup L₁, IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLH : L₁ ≤ H := le_sup_left.trans hbase
  let q := starRestriction H L₁ hLH
  let f := φ.comp q
  have hr : f.range = (Source.starImage H L₁).map φ := by
    rw [MonoidHom.range_comp, starRestriction_range]
  have hc (c : S7) (hcP : c ∈ fourThreeStabilizer)
      (hc3 : Equiv.Perm.IsThreeCycle c) : c ∈ f.range := by
    rw [hr]
    exact even_order_three_mem_local_image H L₁ T G₁ M hbase hHG htheta h13
      φ hφ hAlt hP c hcP hc3.mem_alternatingGroup hc3.orderOf
  let D : Subgroup S7 := zpowers cycle012 ⊔ zpowers cycle456
  have hD : D ≤ f.range := sup_le
    (zpowers_le.mpr (hc cycle012 (by decide +kernel) cycle012_isThreeCycle))
    (zpowers_le.mpr (hc cycle456 (by decide +kernel) cycle456_isThreeCycle))
  let : IsElementaryAbelian 3 D := cubicNine_data.1
  let E := D.subgroupOf f.range
  let e : E ≃* D := subgroupOfEquivOfLe hD
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.subgroupOf hD
  have hker : f.rangeRestrict.ker = q.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    ext x
    change φ (q x) = 1 ↔ q x = 1
    rw [← φ.map_one, hφ.eq_iff]
  have htwo : IsPGroup 2 f.rangeRestrict.ker := by
    rw [hker]
    exact starRestriction_ker_isTwoGroup H L₁ hLH
  have hcop : Nat.Coprime 3 (Nat.card f.rangeRestrict.ker) := by
    obtain ⟨n, hn⟩ := htwo.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨F, hF, _, hcard⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    f.rangeRestrict f.rangeRestrict_surjective hcop E
  exact ⟨F, hF, hcard.trans ((Nat.card_congr e.toEquiv).trans cubicNine_data.2)⟩

/-- The rank-two and covered-A₆ deductions use theta and the actual earlier
quotient alternatives, with no elementary-nine or rank-two premise. -/
theorem rank_and_covered_quotient_of_theta
    (H L₁ T G₁ M L : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (hP : Source.starImage H (L₁ ⊔ T) ≤ fourThreeStabilizer.comap φ)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3) :
    primeRank 3 L₁ = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  obtain ⟨E, hE, hcard⟩ := local_elementaryNine_of_theta H L₁ T G₁ M
    hbase hHG htheta h13 φ hφ hAlt hP
  have hr := primeRank_three_eq_two_of_fourThree H L₁ T (le_sup_left.trans hbase)
    φ hφ hP E hE hcard
  exact ⟨hr, ⟨quotient_equiv_hexEven_of_threeRank_two L L₁ hmodels ha6 hr⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
