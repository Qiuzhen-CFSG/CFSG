module

public import Theory.GroupTheory.PGroup.CyclicFourSectionDerived
public import Theory.GroupTheory.SaturatedCentralizerDerivedFusion
public import Theory.GroupTheory.CoreInvolutionFusion
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Join

/-!
# Elementary centralizers of order sixteen

Let `z` be a central involution of a Sylow two-subgroup `S`, and let `t`
be an ambient conjugate outside a normal elementary four `W` containing `z`.
Suppose the proper centralizer `E = C_S(t)` has order sixteen, contains `W`,
and is maximal among two-subgroups in the common ambient centralizer.
If the other two involutions of `W` are not conjugate to `z`, while the
involutions in the coset `W t` are conjugate to `t`, then `E` is elementary.

The elementary eight `W⟨t⟩` has index two in `E`. Commutators with `W`
lie in `⟨z⟩`, and a cyclic supplement together with the central element `t`
is abelian. Thus a nonabelian `E` has characteristic derived line `⟨z⟩`,
contradicting saturated fusion. If `E` is abelian but not elementary,
every involution belongs to `W⟨t⟩`: another involution would generate an
elementary sixteen. Its ambient normalizer therefore permutes precisely
the two involutions separated from `z`, and fixes their product `z`.
The saturated normalizer criterion again contradicts fusion.

Source: Janko–Thompson, *On finite simple groups whose Sylow 2-subgroups
have no normal elementary subgroups of order 8*, Math. Z. 113
(1970), §4 case (b)(ii), printed p.391, PDF page 7 of
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
Only the stated local separation and coset fusion are needed; no global
cover of involution conjugacy classes is assumed.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

private theorem commuting_join
    {P : Type*} [Group P] (K W : Subgroup P)
    [IsMulCommutative K] [IsMulCommutative W]
    (hcomm : K ≤ centralizer (W : Set P)) : IsMulCommutative (K ⊔ W : Subgroup P) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le K.le_centralizer (le_centralizer_iff.mp hcomm))
  · exact le_centralizer_iff.mpr (sup_le hcomm W.le_centralizer)

private theorem derived_join_le
    {P : Type*} [Group P] (K W Z : Subgroup P)
    [IsMulCommutative K] [IsMulCommutative W] [Z.Normal]
    (hcomm : ⁅K, W⁆ ≤ Z) : ⁅K ⊔ W, K ⊔ W⁆ ≤ Z := by
  let q := QuotientGroup.mk' Z
  have hcomm' : ⁅K.map q, W.map q⁆ = ⊥ := by
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hcomm)
  let : IsMulCommutative (K.map q) := map_isMulCommutative K q
  let : IsMulCommutative (W.map q) := map_isMulCommutative W q
  let : IsMulCommutative (K.map q ⊔ W.map q : Subgroup (P ⧸ Z)) :=
    commuting_join _ _ (commutator_eq_bot_iff_le_centralizer.mp hcomm')
  have hmap : (⁅K ⊔ W, K ⊔ W⁆).map q = ⊥ := by
    rw [map_commutator, map_sup]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  have hle := (map_eq_bot_iff _).mp hmap
  simpa only [q, QuotientGroup.ker_mk'] using hle

private theorem sixteen_derived_le
    {P : Type*} [Group P] [Finite P]
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z t : P) (hz : orderOf z = 2) (hzc : z ∈ center P) (hzW : z ∈ W)
    (ht : orderOf t = 2) (htW : t ∉ W)
    (hWE : W ≤ centralizer ({t} : Set P))
    (hcard : Nat.card (centralizer ({t} : Set P)) = 16) :
    ⁅centralizer ({t} : Set P), centralizer ({t} : Set P)⁆ ≤ zpowers z := by
  let E := centralizer ({t} : Set P)
  let A := W ⊔ zpowers t
  have htE : t ∈ E := mem_centralizer_singleton_iff.mpr rfl
  have hAE : A ≤ E := sup_le hWE (zpowers_le.mpr htE)
  have hA : Nat.card A = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution W t
      (by simpa [ht] using pow_orderOf_eq_one t) htW (le_normalizer_of_normal (mem_top t)), hW]
  have hi : A.relIndex E = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup P) A E bot_le hAE
    simp only [relIndex_bot_left, hA, show Nat.card E = 16 from hcard] at hh
    omega
  obtain ⟨x, hxE, _, hcases⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hi
  let K := zpowers x ⊔ zpowers t
  have hKE : K ≤ E := sup_le (zpowers_le.mpr hxE) (zpowers_le.mpr htE)
  have hK : IsMulCommutative K := by
    apply commuting_join
    rw [zpowers_eq_closure t, centralizer_closure]
    exact zpowers_le.mpr hxE
  let : IsMulCommutative K := hK
  have hgen : K ⊔ W = E := by
    apply le_antisymm (sup_le hKE hWE)
    have hAgen : A ≤ K ⊔ W := sup_le le_sup_right (le_sup_right.trans le_sup_left)
    have hxgen : x ∈ K ⊔ W := (le_sup_left : K ≤ K ⊔ W) ((le_sup_left : zpowers x ≤ K) (mem_zpowers x))
    intro y hy
    rcases hcases y hy with hyx | hyA
    · have hh := (K ⊔ W).mul_mem (hAgen hyx) ((K ⊔ W).inv_mem hxgen)
      simpa only [mul_inv_cancel_right] using hh
    · exact hAgen hyA
  have hZc : zpowers z ≤ center P := zpowers_le.mpr hzc
  let : (zpowers z).Normal := ⟨fun n hn g => by
    rw [(mem_center_iff.mp (hZc hn) g), mul_inv_cancel_right]
    exact hn⟩
  change ⁅E, E⁆ ≤ zpowers z
  rw [← hgen]
  exact derived_join_le K W (zpowers z) ((commutator_mono le_top le_rfl).trans
    (normal_four_commutator_le_central_involution W hW z hz hzc hzW))

private theorem involution_mem_eight
    {P : Type*} [Group P] [Finite P]
    (A E : Subgroup P) [IsElementaryAbelian 2 A] [IsMulCommutative E]
    (hAE : A ≤ E) (hA : Nat.card A = 8) (hE : Nat.card E = 16)
    (hne : ¬ IsElementaryAbelian 2 E)
    (x : P) (hxE : x ∈ E) (hx2 : x ^ 2 = 1) : x ∈ A := by
  by_contra hxA
  have hxC : x ∈ centralizer (A : Set P) := fun a ha => setLike_mul_comm (hAE ha) hxE
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  let : IsElementaryAbelian 2 (A ⊔ zpowers x : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hxC)
  have heq : A ⊔ zpowers x = E := by
    apply eq_of_le_of_card_ge (sup_le hAE (zpowers_le.mpr hxE))
    rw [card_sup_zpowers_of_normalizing_involution A x hx2 hxA
      (centralizer_le_normalizer _ hxC), hA, hE]
  exact hne (heq ▸ inferInstanceAs (IsElementaryAbelian 2 (A ⊔ zpowers x : Subgroup P)))

private theorem four_pair
    {P : Type*} [Group P] [Finite P]
    (W : Subgroup P) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z : P) (hz : orderOf z = 2) (hzW : z ∈ W) :
    ∃ a : P, a ∈ W ∧ a ≠ 1 ∧ a ≠ z ∧
      ∀ w ∈ W, w = 1 ∨ w = z ∨ w = a ∨ w = z * a := by
  have hZW : zpowers z < W := by
    refine lt_of_le_of_ne (zpowers_le.mpr hzW) ?_
    intro heq
    have hh := congrArg (fun U : Subgroup P => Nat.card U) heq
    rw [Nat.card_zpowers, hz, hW] at hh
    omega
  obtain ⟨a, haW, haZ⟩ := SetLike.exists_of_lt hZW
  have ha1 : a ≠ 1 := fun hh => haZ (hh ▸ (zpowers z).one_mem)
  have haz : a ≠ z := fun hh => haZ (hh ▸ mem_zpowers z)
  have ha : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a haW) ha1
  have hza : Commute z a := setLike_mul_comm hzW haW
  let : IsKleinFour (closure ({z, a} : Set P)) :=
    isKleinFour_closure_pair_of_orderOf z a hz ha (Ne.symm haz) hza
  have heq : closure ({z, a} : Set P) = W := by
    apply eq_of_le_of_card_ge
    · apply (closure_le _).mpr
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl <;> assumption
    · rw [hW, IsKleinFour.card_four]
  refine ⟨a, haW, ha1, haz, fun w hw => ?_⟩
  apply (mem_closure_pair_iff z a (by simpa [pow_two, hz] using pow_orderOf_eq_one z)
    (by simpa [pow_two, ha] using pow_orderOf_eq_one a) hza w).mp
  rwa [heq]

private theorem mem_join_involution_cases
    {P : Type*} [Group P] [Finite P]
    (W : Subgroup P) [W.Normal] (t : P) (ht : orderOf t = 2)
    (u : P) (hu : u ∈ W ⊔ zpowers t) : u ∈ W ∨ u * t⁻¹ ∈ W := by
  classical
  obtain ⟨w, hw, v, hv, rfl⟩ := mem_sup_of_normal_left.mp hu
  rw [mem_zpowers_iff_mem_range_orderOf, ht] at hv
  obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hv
  have hi2 := Finset.mem_range.mp hi
  interval_cases i
  · have hv1 : v = 1 := by simpa using hiv.symm
    simpa [hv1] using Or.inl hw
  · have hvt : v = t := by simpa using hiv.symm
    exact Or.inr (by simpa [hvt] using hw)

private theorem abelian_sixteen_normalizer
    {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z t : S) (hz : orderOf z = 2) (hzW : z ∈ W)
    (ht : orderOf t = 2) (htW : t ∉ W) (hconj : IsConj (z : G) (t : G))
    (hWE : W ≤ centralizer ({t} : Set S))
    (hcard : Nat.card (centralizer ({t} : Set S)) = 16)
    (hsep : ∀ w : S, w ∈ W → w ≠ 1 → w ≠ z → ¬ IsConj (z : G) (w : G))
    (hcoset : ∀ u : S, orderOf u = 2 → u * t⁻¹ ∈ W → IsConj (t : G) (u : G))
    (hab : IsMulCommutative (centralizer ({t} : Set S)))
    (hne : ¬ IsElementaryAbelian 2 (centralizer ({t} : Set S))) :
    normalizer ((centralizer ({t} : Set S)).map S.subtype : Set G) ≤
      centralizer ({(z : G)} : Set G) := by
  classical
  let E := centralizer ({t} : Set S)
  let A := W ⊔ zpowers t
  let : IsMulCommutative E := hab
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have htE : t ∈ E := mem_centralizer_singleton_iff.mpr rfl
  have hAE : A ≤ E := sup_le hWE (zpowers_le.mpr htE)
  have htC : t ∈ centralizer (W : Set S) :=
    fun w hw => mem_centralizer_singleton_iff.mp (hWE hw)
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr htC)
  have hA : Nat.card A = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution W t ht2 htW
      (le_normalizer_of_normal (mem_top t)), hW]
  obtain ⟨a, haW, ha1, haz, hlist⟩ := four_pair W hW z hz hzW
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a haW
  have hz2 : z ^ 2 = 1 := by simpa [hz] using pow_orderOf_eq_one z
  have hzaW : z * a ∈ W := W.mul_mem hzW haW
  have hza1 : z * a ≠ 1 := by
    intro hh
    have hh' : z * a = z * z := hh.trans (by simpa [pow_two] using hz2.symm)
    exact haz (mul_left_cancel hh')
  have hzaz : z * a ≠ z := by
    intro hh
    exact ha1 (mul_left_cancel (hh.trans (mul_one z).symm))
  have hzaa : z * a ≠ a := by
    intro hh
    have hz1 := mul_right_cancel (hh.trans (one_mul a).symm)
    simp [hz1] at hz
  have hza2 : (z * a) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hzaW
  have haorder : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hzaorder : orderOf (z * a) = 2 := orderOf_eq_prime hza2 hza1
  have hpair (u : S) (huE : u ∈ E) (hu2 : orderOf u = 2)
      (huf : ¬ IsConj (z : G) (u : G)) : u = a ∨ u = z * a := by
    have huA : u ∈ A := involution_mem_eight A E hAE hA hcard hne u huE
      (by simpa [hu2] using pow_orderOf_eq_one u)
    rcases mem_join_involution_cases W t ht u huA with huW | huT
    · rcases hlist u huW with rfl | rfl | hh | hh
      · simp at hu2
      · exact (huf (IsConj.refl _)).elim
      · exact Or.inl hh
      · exact Or.inr hh
    · exact (huf (hconj.trans (hcoset u hu2 huT))).elim
  intro g hg
  let f : G ≃* G := MulAut.conj g
  have hmove (u : S) (huE : u ∈ E) (hu2 : orderOf u = 2)
      (huf : ¬ IsConj (z : G) (u : G)) :
      f (u : G) = (a : G) ∨ f (u : G) = ((z * a : S) : G) := by
    have hfu : f (u : G) ∈ E.map S.subtype :=
      (hg (u : G)).mp (mem_map_of_mem S.subtype huE)
    obtain ⟨v, hvE, hv⟩ := mem_map.mp hfu
    change (v : G) = f (u : G) at hv
    have hv2 : orderOf v = 2 := by
      rw [← orderOf_coe v, hv, f.orderOf_eq, orderOf_coe, hu2]
    have hvf : ¬ IsConj (z : G) (v : G) := by
      intro h
      apply huf
      have hc : IsConj (u : G) (v : G) := isConj_iff.mpr ⟨g, hv.symm⟩
      exact h.trans hc.symm
    rcases hpair v hvE hv2 hvf with rfl | rfl
    · exact Or.inl hv.symm
    · exact Or.inr hv.symm
  have hfa := hmove a (hWE haW) haorder (hsep a haW ha1 haz)
  have hfza := hmove (z * a) (hWE hzaW) hzaorder (hsep (z * a) hzaW hza1 hzaz)
  have hprod : (a : G) * ((z * a : S) : G) = (z : G) := by
    exact congrArg (fun s : S => (s : G)) (show a * (z * a) = z by
      rw [← mul_assoc, setLike_mul_comm haW hzW, mul_assoc, ← pow_two, ha2, mul_one])
  have hprod' : ((z * a : S) : G) * (a : G) = (z : G) := by
    exact congrArg (fun s : S => (s : G)) (show (z * a) * a = z by
      rw [mul_assoc, ← pow_two, ha2, mul_one])
  have hdistinct : (a : G) ≠ ((z * a : S) : G) :=
    fun h => hzaa (Subtype.val_injective h).symm
  have hfixed : f (z : G) = (z : G) := by
    rw [← hprod, map_mul]
    rcases hfa with hfa | hfa <;> rcases hfza with hfza | hfza
    · exact (hdistinct (f.injective (hfa.trans hfza.symm))).elim
    · rw [hfa, hfza]
    · rw [hfa, hfza, hprod', hprod]
    · exact (hdistinct (f.injective (hfa.trans hfza.symm))).elim
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfixed)

end Subgroup

namespace Sylow

/-- A saturated proper Sylow centralizer of order sixteen is elementary when a
normal four separates the central involution from its other two involutions
and all involutions in the outside coset fuse to the centralizing involution. -/
public theorem isElementaryAbelian_centralizer_of_saturated_sixteen
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S) (hzW : z ∈ W)
    (ht : orderOf t = 2) (htW : t ∉ W) (hconj : IsConj (z : G) (t : G))
    (hWE : W ≤ centralizer ({t} : Set S))
    (hcard : Nat.card (centralizer ({t} : Set S)) = 16)
    (hproper : centralizer ({t} : Set S) ≠ ⊤)
    (hsep : ∀ w : S, w ∈ W → w ≠ 1 → w ≠ z → ¬ IsConj (z : G) (w : G))
    (hcoset : ∀ u : S, orderOf u = 2 → u * t⁻¹ ∈ W → IsConj (t : G) (u : G))
    (hsat : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(z : G), (t : G)} : Set G) →
      V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype) :
    IsElementaryAbelian 2 (centralizer ({t} : Set S)) := by
  classical
  let E := centralizer ({t} : Set S)
  by_cases hab : IsMulCommutative E
  · by_contra hne
    exact not_isConj_of_saturated_centralizer_normalizer S z t hzc hproper hsat
      (abelian_sixteen_normalizer (S : Subgroup G) W hW z t hz hzW ht htW
        hconj hWE hcard hsep hcoset hab hne) hconj
  · have hbound : ⁅E, E⁆ ≤ zpowers z :=
      sixteen_derived_le W hW z t hz hzc hzW ht htW hWE hcard
    have hline : (_root_.commutator E).map E.subtype = zpowers z := by
      rw [map_subtype_commutator]
      apply eq_of_le_of_card_ge hbound
      have hne : ⁅E, E⁆ ≠ ⊥ := fun hh => hab (commutator_self_eq_bot_iff.mp hh)
      have hc : Nat.card (⁅E, E⁆ : Subgroup S) ≠ 1 := fun hh => hne (card_eq_one.mp hh)
      have hp : 0 < Nat.card (⁅E, E⁆ : Subgroup S) := Nat.card_pos
      rw [Nat.card_zpowers, hz]
      omega
    exact (S.not_isConj_of_saturated_centralizer_derived_line z t hz hzc hproper
      hline hsat hconj).elim

end Sylow
