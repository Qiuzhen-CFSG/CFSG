module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.LinearOdd
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups.ElementLift

/-!
# Cubic actors in the original natural SL₃ automizer

The action kernel meets the normal component in its two-core. Quotienting
by that intersection gives commuting disjoint normal images. The component
has three-rank at least two in even degree, so strong quasithinness forces
the remaining action kernel to have order prime to three. Coprime lifting
then transfers the exact earlier order-three containment to the automizer.
Combined with LinearOdd this proves the bound for every odd prime.

The only remaining SL₃ premise is the literal final clause of 11.0.4,
owned by qt-d-1222-natural-preliminary-source; its discharge stays with
qt-d-1222-natural-weak-closure-source. No automizer containment, numerical
bound, or same-order lifting assumption is imposed.
Source: Aschbacher--Smith, 11.0.4 and 11.2.2(2), printed pp.760,768.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer

private theorem coprime_three_of_normal_intersection
    {H : Type*} [Group H] [Finite H] (K C : Subgroup H) [K.Normal] [C.Normal]
    (hi : IsPGroup 2 (K ⊓ C : Subgroup H))
    (hrK : 2 ≤ primeRank 3 K) (hrH : primeRank 3 H ≤ 2) :
    Nat.Coprime 3 (Nat.card C) := by
  let R := K ⊓ C
  let q := QuotientGroup.mk' R
  let A := K.map q
  let B := C.map q
  let : A.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  let : B.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  have hq : IsPGroup 2 q.ker := by rwa [QuotientGroup.ker_mk']
  have hd : Disjoint A B := by
    apply disjoint_iff.mpr
    apply _root_.eq_bot_iff.mpr
    rintro x ⟨⟨k,hk,rfl⟩,hx⟩
    have hkC : k ∈ C := by
      have hh : k ∈ (C.map q).comap q := hx
      rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr inf_le_right] at hh
    exact (QuotientGroup.eq_one_iff k).mpr ⟨hk,hkC⟩
  have hc : A ≤ centralizer (B : Set (H ⧸ R)) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  have hr := primeRank_subgroup_le 3 (A ⊔ B)
  rw [primeRank_sup_eq_add_of_disjoint_commuting A B hd hc,
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hq,
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hq] at hr
  have hu := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) R hi).trans hrH
  have hzero : primeRank 3 C = 0 := by omega
  exact Nat.prime_three.coprime_iff_not_dvd.mpr
    (PrimeRank.eq_zero_iff_not_dvd_card.mp hzero)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private theorem layerAction_kernel (c : Coordinates D S.field) :
    (layerAction D).ker = pCore 2 L := by
  have he : (layerAction D).ker = c.quotientMap.ker := by
    ext l
    exact layerAction_eq_one_iff D S c l
  rw [he]
  ext l
  change c.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ _
  rw [c.groupEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff l

private theorem three_dvd_of_even {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k,hk⟩ := hn
  have hm : 2 ^ n % 3 = 1 := by
    rw [hk, ← two_mul, pow_mul]
    norm_num [Nat.pow_mod]
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  omega

/-- In even degree the literal action kernel has order prime to three. -/
theorem sl3_even_action_kernel_coprime
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hn : Even S.field.degree) :
    Nat.Coprime 3 (Nat.card V.normalizerMonoidHom.rangeRestrict.ker) := by
  let N := normalizer (V : Set G)
  let K := L.subgroupOf N
  let f := V.normalizerMonoidHom.rangeRestrict
  let C := f.ker
  let : K.Normal := normal_subgroupOf_of_le_normalizer (seed_normalizer_le D S)
  let e : K ≃* L := subgroupOfEquivOfLe D.normalizes
  have hker := layerAction_kernel D S (Coordinates.sl3 m)
  have htwo : IsPGroup 2 (layerAction D).ker := hker ▸ pCore_isPGroup
  have hi : IsPGroup 2 (K ⊓ C : Subgroup N) := by
    let j : (K ⊓ C : Subgroup N) →* (layerAction D).ker := {
      toFun x := ⟨⟨x.val.val,x.property.1⟩,by
        apply Subtype.ext
        exact x.property.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : (layerAction D).ker => (z.val : G)) h))
    exact htwo.of_injective j hj
  have hL : 2 ≤ primeRank 3 L := by
    have hbound := Matrix.PSL3.SplitPrimeRank.special_rank S.field.Carrier
      (S.field.card_eq ▸ three_dvd_of_even hn)
    change 2 ≤ primeRank 3 (Coordinates.sl3 m).ModelGroup at hbound
    rw [← primeRank_congr 3 (layerEquiv D S (Coordinates.sl3 m))] at hbound
    have hc : Nat.Coprime 3 (Nat.card (layerAction D).ker) := by
      obtain ⟨k,hk⟩ := htwo.exists_card_eq
      rw [hk]
      exact (by decide : Nat.Coprime 3 2).pow_right k
    rw [← primeRank_eq_of_surjective_of_coprime 3 (layerAction D)
      (layerAction_surjective D) hc] at hbound
    exact hbound
  have hrK : 2 ≤ primeRank 3 K := by rwa [primeRank_congr 3 e]
  have hrN : primeRank 3 N ≤ 2 :=
    (primeRank_mono 3 (seed_normalizer_le D S)).trans
      ((Preliminary.normalizer_sqtk D S).stronglyQuasithin 3 (by decide) (by decide))
  exact coprime_three_of_normal_intersection K C hi hrK hrN

/-- Cubic actors lift through the proved prime-to-three action kernel. -/
theorem sl3_cubic_mem_layer_of_source
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hn : Even S.field.degree)
    (hthree : ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    {a : Automizer V} (ha : orderOf a = 3) : a ∈ inducedAutomizer V L := by
  let f := V.normalizerMonoidHom.rangeRestrict
  obtain ⟨x,hx,hxp⟩ := exists_prime_exponent_lift f
    V.normalizerMonoidHom.rangeRestrict_surjective
    (sl3_even_action_kernel_coprime D S m hn) a (ha ▸ pow_orderOf_eq_one a)
  have hx1 : x ≠ 1 := by
    intro he
    have ha1 : a = 1 := hx.symm.trans (he ▸ f.map_one)
    simp only [ha1,orderOf_one] at ha
    omega
  have ho : orderOf x = 3 := orderOf_eq_prime hxp hx1
  have hxL : (x : G) ∈ L := hthree x
    (seed_normalizer_le D S x.property) ((Subgroup.orderOf_coe x).trans ho)
  exact ⟨x,hxL,hx⟩

/-- The full SL₃ odd-prime bound, with only the exact earlier 11.0.4 cubic
clause explicit. Its producer is qt-d-1222-natural-preliminary-source. -/
theorem sl3_odd_prime_lower_of_cubic_source
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hthree : Even S.field.degree →
      ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V, orderOf a = p →
      2 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp ho a ha
  rcases Nat.even_or_odd S.field.degree with hn | hn
  · by_cases hp3 : p = 3
    · rw [hp3] at ha
      exact sl3_inner_odd_prime_lower D S m 3 (by decide) (by decide) a ha
        (sl3_cubic_mem_layer_of_source D S m hn (hthree hn) ha)
    · have htwo := hp.two_le
      have hp2 : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
      exact sl3_odd_prime_lower_of_gt_three D S m p hp (by omega) a ha
  · exact sl3_odd_prime_lower_of_odd_degree D S m hn p hp ho a ha

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
