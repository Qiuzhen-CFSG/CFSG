module

public import Theory.GroupTheory.IsolatedFourTwoGroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PGroup.Omega
public import Theory.Frattini.PGroupMap

/-!
# Central involution fusion and elementary weak-core normalizers

Let `S` be a finite two-subgroup containing an elementary eight. Suppose `M`
contains the normalizer of every elementary subgroup `E ≤ S` of order at least
four whose centralizer in `S` contains an elementary eight. If `D ≤ S` is
centric in `S` and an element of `N_G(D)` moves an involution of `Z(S)`, then
`N_G(D) ≤ M`.

Take `E = Ω₁(Z(D))`, with both subgroup embeddings explicit. It is characteristic
in `D`, contains the central involution, and has order at least four because that
involution is moved. If its centralizer contains no elementary eight, `E` is an
isolated four. Every involution of `Φ(D)` then lies in `E`; functoriality of the
Frattini subgroup and the isolated-four bound on `E ∩ Φ(S)` force it to be the
given central involution. If `Φ(D)` is nontrivial, this unique involution is
fixed by every automorphism of `D`. Otherwise `D` is elementary, so `D = E`,
contrary to the strict enlargement of an isolated four by its centralizer.

Source: Gorenstein–Lyons–Solomon, volume 4, Chapter 2, Lemma 18.7, after (18H),
printed p.94 (PDF p.111); `refs/KGroup/GLS4/Chapter2.tex`. The proof uses uniqueness
of the involution in `Φ(D)`, without asserting the stronger printed shortcut
`Φ(D) ≤ ⟨z⟩`. It requires no global connectivity or fusion-existence theorem.
-/

namespace Subgroup
open scoped IsMulCommutative

private theorem card_le_four_of_no_eight {P : Type*} [Group P] [Finite P]
    (V : Subgroup P) [IsElementaryAbelian 2 V] (h : ¬ 8 ≤ Nat.card V) :
    Nat.card V ≤ 4 := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hn3 : n < 3 := by
    by_contra! hn3
    exact h (hn ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn3)
  interval_cases n <;> simp_all

private theorem eq_involution_of_mem_zpowers {P : Type*} [Group P] [Finite P]
    (z x : P) (hz : orderOf z = 2) (hx : orderOf x = 2)
    (h : x ∈ zpowers z) : x = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz] at h
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
  have hn2 := Finset.mem_range.mp hn
  interval_cases n <;> simp_all

private theorem fixed_of_isolated_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A V D : Subgroup P) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hiso : ∀ W : Subgroup P, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V : Set P) → W = V)
    (hVD : V ≤ D) (hDC : D ≤ centralizer (V : Set P))
    (hcentric : centralizer (D : Set P) ≤ D)
    (z : P) (hz : orderOf z = 2) (hzV : z ∈ V) (hzZ : z ∈ center P)
    (f : MulAut D) : (f ⟨z, hVD hzV⟩ : P) = z := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : Fact (IsPGroup 2 D) := ⟨hP.to_subgroup D⟩
  have hunique : ∀ x : D, x ∈ frattini D → orderOf x = 2 → (x : P) = z := by
    intro x hx hxo
    have hxP : orderOf (x : P) = 2 := by simpa using hxo
    have hxV := involution_mem_of_maximal_elementary_four V
      (maximal_elementary_of_isolated_four V hV hiso) (x : P)
      (by simpa [hxP] using pow_orderOf_eq_one (x : P)) (hDC x.property)
    have hxPhi : (x : P) ∈ frattini P :=
      frattini_map_le_of_isPGroup (p := 2) D.subtype (mem_map_of_mem D.subtype hx)
    exact eq_involution_of_mem_zpowers z x hz hxP
      (inf_frattini_le_zpowers_of_isolated_four_of_rank_three hP A V hA hV hiso
        z hzV hz hzZ ⟨hxV, hxPhi⟩)
  by_cases hphi : frattini D = ⊥
  · let : IsElementaryAbelian 2 D :=
      (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
    have hDV := maximal_elementary_of_isolated_four V hV hiso D inferInstance hVD
    have hDeq : D = V := le_antisymm hDV hVD
    have hlt := lt_centralizer_of_isolated_four_of_rank_three hP A V hA hV hiso
    exact (hlt.not_ge (hDeq ▸ hcentric)).elim
  · obtain ⟨x, hx, hx1⟩ := (frattini D).bot_or_exists_ne_one.resolve_left hphi
    let t : D := x ^ (orderOf x / 2)
    have ht : orderOf t = 2 :=
      orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos x))
        ((hP.to_subgroup D).dvd_orderOf hx1)
    have htPhi : t ∈ frattini D := (frattini D).pow_mem hx _
    have htz : (t : P) = z := hunique t htPhi ht
    have hft := hunique (f t)
      (characteristic_iff_le_comap.mp (inferInstance : (frattini D).Characteristic) f htPhi)
      ((f.orderOf_eq t).trans ht)
    have hteq : t = ⟨z, hVD hzV⟩ := Subtype.ext htz
    simpa only [hteq] using hft

private theorem exists_eight_centralizing_of_moving
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A V D : Subgroup P) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : 4 ≤ Nat.card V)
    (hVD : V ≤ D) (hDC : D ≤ centralizer (V : Set P))
    (hcentric : centralizer (D : Set P) ≤ D)
    (z : P) (hz : orderOf z = 2) (hzV : z ∈ V) (hzZ : z ∈ center P)
    (f : MulAut D) (hmove : (f ⟨z, hVD hzV⟩ : P) ≠ z) :
    ∃ B : Subgroup P, IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B ∧
      B ≤ centralizer (V : Set P) := by
  classical
  by_contra! hno
  have hV4 : Nat.card V = 4 := by
    have hb := card_le_four_of_no_eight V
      (fun h8 => hno V inferInstance h8 V.le_centralizer)
    omega
  have hiso : ∀ W : Subgroup P, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V : Set P) → W = V := by
    intro W hWe hW hWC
    let : IsElementaryAbelian 2 W := hWe
    let : IsElementaryAbelian 2 (V ⊔ W : Subgroup P) :=
      IsElementaryAbelian.sup_of_le_centralizer hWC
    have hsupC : V ⊔ W ≤ centralizer (V : Set P) := sup_le V.le_centralizer hWC
    have hb := card_le_four_of_no_eight (V ⊔ W)
      (fun h8 => hno (V ⊔ W) inferInstance h8 hsupC)
    have hsupV : V = V ⊔ W := eq_of_le_of_card_ge le_sup_left (by omega)
    apply eq_of_le_of_card_ge
    · rw [hsupV]
      exact le_sup_right
    · omega
  exact hmove (fixed_of_isolated_four hP A V D hA hV4 hiso hVD hDC hcentric
    z hz hzV hzZ f)

/-- A centric subgroup moving a central involution has its normalizer in any
subgroup controlling the elementary normalizers with rank-three centralizer. -/
public theorem normalizer_le_of_moving_central_involution
    {G : Type*} [Group G] [Finite G]
    (S M A D : Subgroup G) (hS : IsPGroup 2 S) (_hSM : S ≤ M)
    [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (hM : ∀ E B : Subgroup G, IsElementaryAbelian 2 E → 4 ≤ Nat.card E → E ≤ S →
      IsElementaryAbelian 2 B → 8 ≤ Nat.card B →
      B ≤ S ⊓ centralizer (E : Set G) → normalizer (E : Set G) ≤ M)
    (z : G) (hz : orderOf z = 2) (hzZ : z ∈ (center S).map S.subtype)
    (hDS : D ≤ S) (hcentric : S ⊓ centralizer (D : Set G) ≤ D)
    (g : G) (hg : g ∈ normalizer (D : Set G)) (hmove : g * z * g⁻¹ ≠ z) :
    normalizer (D : Set G) ≤ M := by
  classical
  have hzS : z ∈ S := map_subtype_le _ hzZ
  have hzcomm : ∀ s : G, s ∈ S → s * z = z * s := by
    obtain ⟨t, ht, htval⟩ := hzZ
    intro s hs
    rw [← htval]
    exact congrArg Subtype.val (mem_center_iff.mp ht ⟨s, hs⟩)
  have hzD : z ∈ D := hcentric ⟨hzS, fun d hd => hzcomm d (hDS hd)⟩
  let zD : D := ⟨z, hzD⟩
  have hzZD : zD ∈ center D := mem_center_iff.mpr (fun d =>
    Subtype.ext (hzcomm d (hDS d.property)))
  let W := omega₁ (center D) (p := 2)
  let ED : Subgroup D := W.map (center D).subtype
  let E : Subgroup G := ED.map D.subtype
  let : W.Characteristic := omega₁_characteristic _
  let : ED.Characteristic := inferInstance
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 ED := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hED : E ≤ D := map_subtype_le _
  have hES : E ≤ S := hED.trans hDS
  have hzE : z ∈ E := by
    apply mem_map_of_mem D.subtype (x := zD)
    apply mem_map_of_mem (center D).subtype (x := ⟨zD, hzZD⟩)
    apply subset_closure
    change (⟨zD, hzZD⟩ : center D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    apply Subtype.ext
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z
  have hEC : E ≤ centralizer (D : Set G) := by
    rintro x ⟨d, hd, rfl⟩ y hy
    have hdZ : d ∈ center D := map_subtype_le _ hd
    exact congrArg Subtype.val (mem_center_iff.mp hdZ ⟨y, hy⟩)
  have hDC : D ≤ centralizer (E : Set G) := le_centralizer_iff.mp hEC
  have hnorm : normalizer (D : Set G) ≤ normalizer (E : Set G) :=
    normalizer_le_normalizer_characteristic_image D ED
  have hE4 : 4 ≤ Nat.card E := by
    by_contra! hsmall
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    have hn2 : n < 2 := by
      by_contra! hlarge
      have hb := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlarge
      omega
    have hcard : Nat.card E ≤ 2 := by interval_cases n <;> simp_all
    have hline : E = zpowers z := (eq_of_le_of_card_ge (zpowers_le.mpr hzE)
      (by rw [Nat.card_zpowers, hz]; exact hcard)).symm
    have hgfix : g ∈ centralizer ({z} : Set G) := by
      rw [← normalizer_zpowers_eq_centralizer_of_order_two z hz, ← hline]
      exact hnorm hg
    exact hmove (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgfix))
  let AS := A.subgroupOf S
  let VS := E.subgroupOf S
  let DS := D.subgroupOf S
  let : IsElementaryAbelian 2 AS := IsElementaryAbelian.subgroupOf hAS
  let : IsElementaryAbelian 2 VS := IsElementaryAbelian.subgroupOf hES
  have hA8S : 8 ≤ Nat.card AS := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv]
  have hV4S : 4 ≤ Nat.card VS := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv]
  have hVD : VS ≤ DS := fun _ hx => hED hx
  have hDCS : DS ≤ centralizer (VS : Set S) := by
    intro d hd e he
    exact Subtype.ext (hDC hd e he)
  have hcentricS : centralizer (DS : Set S) ≤ DS := by
    intro x hx
    exact hcentric ⟨x.property, fun d hd =>
      congrArg Subtype.val (hx ⟨d, hDS hd⟩ hd)⟩
  let zS : S := ⟨z, hzS⟩
  have hzZS : zS ∈ center S := mem_center_iff.mpr (fun s =>
    Subtype.ext (hzcomm s s.property))
  let e : DS ≃* D := subgroupOfEquivOfLe hDS
  let f : MulAut D := D.normalizerMonoidHom ⟨g, hg⟩
  let fS : MulAut DS := e.trans (f.trans e.symm)
  have hmoveS : (fS ⟨zS, hVD hzE⟩ : S) ≠ zS := by
    intro heq
    apply hmove
    exact congrArg (fun x : S => (x : G)) heq
  obtain ⟨B, hBe, hB8, hBC⟩ := exists_eight_centralizing_of_moving hS AS VS DS
    hA8S hV4S hVD hDCS hcentricS zS (by simpa [zS] using hz) hzE hzZS fS hmoveS
  let : IsElementaryAbelian 2 B := hBe
  apply hnorm.trans
  apply hM E (B.map S.subtype) inferInstance hE4 hES (IsElementaryAbelian.map _)
  · simpa only [card_map_of_injective S.subtype_injective] using hB8
  · refine le_inf (map_subtype_le _) ?_
    rintro b ⟨bS, hbS, rfl⟩ x hx
    exact congrArg Subtype.val (hBC hbS ⟨x, hES hx⟩ hx)

end Subgroup
