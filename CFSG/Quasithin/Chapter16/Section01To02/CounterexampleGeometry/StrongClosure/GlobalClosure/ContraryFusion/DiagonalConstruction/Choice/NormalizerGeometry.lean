module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalControl
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionBounds
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Algebra
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Choice.Four
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Choice.GeometryInput

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
private theorem isPGroup_zpowers_of_pow_two {x : G} {n : ℕ}
    (hx : x ^ (2 ^ n) = 1) : IsPGroup 2 (zpowers x) := by
  have hd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  apply IsPGroup.of_card (n := k)
  simp only [Nat.card_zpowers, he]

private theorem into_sylow {H E : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) (hE : IsPGroup 2 E) (hEH : E ≤ H) :
    ∃ k ∈ H, conjugate E k ≤ (S : Subgroup G) := by
  have hp : IsPGroup 2 (E.subgroupOf H) :=
    hE.of_equiv (subgroupOfEquivOfLe hEH).symm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H Q (S.subtype hSH)
  refine ⟨(k : G)⁻¹, H.inv_mem k.property, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hy : MulAut.conj k (⟨x, hEH hx⟩ : H) ∈ S.subtype hSH := by
    rw [← hk]
    change MulAut.conj k (⟨x, hEH hx⟩ : H) ∈
      (Q : Subgroup H).map (MulAut.conj k).toMonoidHom
    exact mem_map_of_mem _ (hQ hx)
  change (k : G) * x * (k : G)⁻¹ ∈ S at hy
  change (k : G) * x * (k : G)⁻¹ ∈ (S : Subgroup G) at hy
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, inv_inv] using hy

omit [Finite G] in
private theorem rebased_mem_conjugate {H : Subgroup G} {g r v q : G}
    (hq : q ∈ H) (hr : r = g⁻¹ * q) (hv : r⁻¹ * v * r ∈ H) :
    v ∈ conjugate H g := by
  apply mem_map.mpr
  refine ⟨g * v * g⁻¹, ?_, ?_⟩
  · rw [show g * v * g⁻¹ = q * (r⁻¹ * v * r) * q⁻¹ by rw [hr]; group]
    exact H.mul_mem (H.mul_mem hq hv) (H.inv_mem hq)
  · simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using
      (show g⁻¹ * (g * v * g⁻¹) * g = v by group)

private theorem square_normalizes (l : LocalControl S A₁ A₂) {x : G}
    (hx : x ∈ S) : x ^ 2 ∈ normalizer (A₁ : Set G) := by
  apply (mem_normalizer_iff_conjugate_eq _ _).mpr
  rw [pow_two, ← conjugate_conjugate]
  rcases l.permutes_pair x hx with hn | hs
  · rw [hn.1, hn.1]
  · rw [hs.1, hs.2]

omit [Finite G] in
private theorem commuting_pair_isPGroup {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : Commute a b) :
    IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup G) := by
  have hp (x : G) (hx : orderOf x = 2) : IsPGroup 2 (zpowers x) := by
    apply isPGroup_zpowers_of_pow_two (n := 1)
    simpa only [pow_one] using (hx ▸ pow_orderOf_eq_one x)
  apply (hp a ha).to_sup_of_normal_left' (hp b hb)
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  apply zpowers_le.mpr
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact (hab.zpow_left n).eq

omit [Finite G] in
private theorem sup_isPGroup_of_commute {a b : G}
    (ha : IsPGroup 2 (zpowers a)) (hb : IsPGroup 2 (zpowers b))
    (hab : Commute a b) : IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup G) := by
  apply ha.to_sup_of_normal_left' hb
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  apply zpowers_le.mpr
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact (hab.zpow_left n).eq

omit [Finite G] in
private theorem commuting_three_isPGroup {a b c : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hc : orderOf c = 2)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) :
    IsPGroup 2 ((zpowers a ⊔ zpowers b) ⊔ zpowers c : Subgroup G) := by
  have habp := commuting_pair_isPGroup ha hb hab
  have hcp : IsPGroup 2 (zpowers c) := by
    apply isPGroup_zpowers_of_pow_two (n := 1)
    simpa only [pow_one] using (hc ▸ pow_orderOf_eq_one c)
  apply habp.to_sup_of_normal_left' hcp
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  apply le_centralizer_iff.mpr
  apply sup_le
  · apply zpowers_le.mpr
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact (hac.zpow_right n).eq.symm
  · apply zpowers_le.mpr
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact (hbc.zpow_right n).eq.symm

omit [Finite G] in
private theorem rebased_diagonal_contradiction
    (h : Hypotheses S A₁ A₂)
    {g v t r q x : G} (ht2 : orderOf t = 2) (hv2 : orderOf v = 2)
    (hvHg : v ∉ conjugate (intersectionGenerated A₁ A₂) g)
    (hq : q ∈ intersectionGenerated A₁ A₂) (hr : r = g⁻¹ * q)
    (htrS : r⁻¹ * t * r ∈ S)
    (htr : r⁻¹ * t * r ∈ (A₁ : Set G) ∪ A₂)
    (hxr : r⁻¹ * x * r ∈ S)
    (hxnorm : r⁻¹ * x * r ∈ normalizer (A₁ : Set G) ∧
      r⁻¹ * x * r ∈ normalizer (A₂ : Set G))
    (hx : x = v * (t⁻¹ * v * t)) : False := by
  have hv1 : v⁻¹ = v := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hv2).1
  have ht1 : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1
  have hid : v⁻¹ * t * v = x * t := by
    have htsq : t * t = 1 := by
      simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1
    rw [hv1, hx, ht1]
    rw [show v * (t * v * t) * t = v * t * v * (t * t) by group, htsq]
    simp
  let t' := r⁻¹ * t * r
  let v' := r⁻¹ * v * r
  let x' := r⁻¹ * x * r
  have ht'2 : orderOf t' = 2 := by
    simpa only [t', MulAut.conj_apply, inv_inv] using
      (MulAut.conj r⁻¹).orderOf_eq t |>.trans ht2
  have ht'ne : t' ≠ 1 := by
    intro he
    have : orderOf t' = 1 := orderOf_eq_one_iff.mpr he
    omega
  have hv'1 : v'⁻¹ = v' := by
    dsimp [v']
    rw [show (r⁻¹ * v * r)⁻¹ = r⁻¹ * v⁻¹ * r by group, hv1]
  have hconj : v'⁻¹ * t' * v' = x' * t' := by
    have hh := congrArg (MulAut.conj r⁻¹) hid
    have hh' : (r⁻¹ * v * r) * (r⁻¹ * t * r) * (r⁻¹ * v * r) =
        (r⁻¹ * x * r) * (r⁻¹ * t * r) := by
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulAut.conj_apply, inv_inv, map_mul, hv1] using hh
    simpa only [t', v', x', hv'1] using hh'
  have htvS : v'⁻¹ * t' * v' ∈ (S : Subgroup G) := by
    rw [hconj]
    exact (S : Subgroup G).mul_mem hxr htrS
  have htvNorm1 (htr : t' ∈ A₁) :
      v'⁻¹ * t' * v' ∈ normalizer (A₁ : Set G) := by
    rw [hconj]
    exact (normalizer (A₁ : Set G)).mul_mem hxnorm.1 (A₁.le_normalizer htr)
  have htvNorm2 (htr : t' ∈ A₂) :
      v'⁻¹ * t' * v' ∈ normalizer (A₂ : Set G) := by
    rw [hconj]
    exact (normalizer (A₂ : Set G)).mul_mem hxnorm.2 (A₂.le_normalizer htr)
  have htr' : v'⁻¹ * t' * v' ∈ (A₁ : Set G) ∪ A₂ := by
    rcases htr with htr | htr
    · exact h.closed_in_left_normalizer.2 t' (Or.inl htr) v'
        (mem_top _) ⟨htvS, htvNorm1 htr⟩
    · exact h.closed_in_right_normalizer.2 t' (Or.inr htr) v'
        (mem_top _) ⟨htvS, htvNorm2 htr⟩
  have hv'H := transporter_mem_intersectionGenerated htr ht'ne htr'
  exact hvHg (rebased_mem_conjugate hq hr (by simpa [v'] using hv'H))

private theorem place_rebased (l : LocalControl S A₁ A₂)
    (h : Hypotheses S A₁ A₂) {E : Subgroup G} {g : G}
    (hE : IsPGroup 2 E) (hEH : conjugate E g⁻¹ ≤ intersectionGenerated A₁ A₂) :
    ∃ q ∈ intersectionGenerated A₁ A₂, ∃ r : G, r = g⁻¹ * q ∧
      conjugate E r ≤ (S : Subgroup G) := by
  have hEp : IsPGroup 2 (conjugate E g⁻¹) := hE.map _
  obtain ⟨q, hq, hQ⟩ := into_sylow (l.sylow_le_generated h) hEp hEH
  refine ⟨q, hq, g⁻¹ * q, rfl, ?_⟩
  have hQ' := hQ
  rw [conjugate_conjugate] at hQ'
  simpa only [mul_assoc] using hQ'

omit [Finite G] in
private theorem diagonal_x_sq
    (h : Hypotheses S A₁ A₂) {t v : G}
    (hs : conjugate A₁ t = A₂) (hv : v ∈ A₁) (hv2 : orderOf v = 2) :
    (v * (t⁻¹ * v * t)) ^ 2 = 1 := by
  have hc := DiagonalConstruction.factors_commute h hv
    (DiagonalConstruction.conjugate_mem hs hv)
  have hv1 : v ^ 2 = 1 := (orderOf_eq_prime_iff.mp hv2).1
  calc
    (v * (t⁻¹ * v * t)) ^ 2 = v ^ 2 * (t⁻¹ * v * t) ^ 2 := hc.mul_pow 2
    _ = 1 := by
      have hvt2 : (t⁻¹ * v * t) ^ 2 = 1 := by
        rw [pow_two]
        calc
          (t⁻¹ * v * t) * (t⁻¹ * v * t) = t⁻¹ * v * (t * t⁻¹) * v * t := by group
          _ = t⁻¹ * v * v * t := by simp
          _ = t⁻¹ * (v ^ 2) * t := by simp only [pow_two, mul_assoc]
          _ = 1 := by rw [hv1]; simp
      simp [hv1, hvt2]

omit [Finite G] in
private theorem transport_factor_geometry {A : Subgroup G} {d t r : G}
    (ht : r⁻¹ * t * r ∈ A)
    (hd : r⁻¹ * d * r ∈ normalizer (A : Set G)) :
    t ∈ conjugate A r⁻¹ ∧ d ∈ normalizer (conjugate A r⁻¹ : Set G) := by
  constructor
  · apply mem_map.mpr
    refine ⟨r⁻¹ * t * r, ht, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv]
    group
  · apply (mem_normalizer_iff_conjugate_eq _ _).mpr
    have hd' := (mem_normalizer_iff_conjugate_eq _ _).mp hd
    rw [conjugate_conjugate]
    have he := congrArg (fun B : Subgroup G => conjugate B r⁻¹) hd'
    rw [conjugate_conjugate] at he
    have harg : r⁻¹ * d = (r⁻¹ * d * r) * r⁻¹ := by group
    rw [harg]
    exact he

set_option maxHeartbeats 800000 in
theorem MinimalCounterexample.diagonalNormalizerGeometry_of_intersection_card_two
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (htS : g⁻¹ * a * g ∈ S)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) :
    DiagonalNormalizerGeometry A₁ A₂ g (g⁻¹ * a * g) := by
  let t := g⁻¹ * a * g
  have ha1 : a ≠ 1 := by
    intro he
    simp [he] at ha2
  have ht2 : orderOf t = 2 := by
    simpa only [t, MulAut.conj_apply, inv_inv] using
      (MulAut.conj g⁻¹).orderOf_eq a |>.trans ha2
  have hs := l.swap_of_outside_transporter m.setup ha ha1 hg htS
  have hcent := DiagonalConstruction.contrary_centralizer_le_conjugate
    (g := g) m.setup ha ha1
  have htransport {E : Subgroup G} (hEC : E ≤ centralizer ({t} : Set G))
      (hEP : IsPGroup 2 E) :
      ∃ q ∈ intersectionGenerated A₁ A₂, ∃ r : G, r = g⁻¹ * q ∧
        conjugate E r ≤ (S : Subgroup G) := by
    have hEH : conjugate E g⁻¹ ≤ intersectionGenerated A₁ A₂ := by
      rintro _ ⟨x, hx, rfl⟩
      apply m.setup.centralizer_le_generated ha ha1
      apply mem_centralizer_singleton_iff.mpr
      have hh := mem_centralizer_singleton_iff.mp (hEC hx)
      have hh' := congrArg (fun z : G => g * z * g⁻¹) hh
      simpa [t, mul_assoc] using hh'
    exact place_rebased l m.setup hEP hEH
  constructor
  · intro v hv hv2 hvout hvHg w hwC hw2
    let x := v * (t⁻¹ * v * t)
    have hx2 : x ^ 2 = 1 := by
      exact diagonal_x_sq m.setup hs.1 hv hv2
    have hxc : Commute x t := by
      apply mem_centralizer_singleton_iff.mp
      exact DiagonalConstruction.diagonal_range_centralizes m.setup hs.1 ht2
        ⟨⟨v, hv⟩, rfl⟩
    have hw4 : w ^ 4 = 1 := by
      calc
        w ^ 4 = w ^ (2 * 2) := by norm_num
        _ = (w ^ 2) ^ 2 := by rw [pow_mul]
        _ = 1 := by rw [hw2, hx2]
    let E := zpowers t ⊔ zpowers w
    have hEP : IsPGroup 2 E := by
      apply sup_isPGroup_of_commute
      · exact isPGroup_zpowers_of_pow_two (n := 1) (by
          simpa only [pow_one] using (ht2 ▸ pow_orderOf_eq_one t))
      · exact isPGroup_zpowers_of_pow_two (n := 2) (by
          simpa only [show 2 ^ 2 = 4 by norm_num] using hw4)
      · exact (mem_centralizer_singleton_iff.mp hwC).symm
    have hEC : E ≤ centralizer ({t} : Set G) := by
      apply sup_le
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
      · exact zpowers_le.mpr hwC
    obtain ⟨q, hq, r, hr, hEr⟩ := htransport hEC hEP
    have ht'r : r⁻¹ * t * r ∈ S := hEr (mem_map.mpr ⟨t,
      (le_sup_left : zpowers t ≤ E) (mem_zpowers t), by simp⟩)
    have hwr : r⁻¹ * w * r ∈ S := hEr (mem_map.mpr ⟨w,
      (le_sup_right : zpowers w ≤ E) (mem_zpowers w), by simp⟩)
    have hxr : r⁻¹ * x * r ∈ S := by
      have hw2' : w ^ 2 = v * (t⁻¹ * v * t) := by simpa [t] using hw2
      have hxw : x = w ^ 2 := by simpa [x] using hw2'.symm
      have hpow : r⁻¹ * w ^ 2 * r = (r⁻¹ * w * r) ^ 2 := by
        simp only [pow_two]
        group
      rw [hxw]
      rw [hpow]
      exact (S : Subgroup G).pow_mem hwr 2
    have hxnorm : r⁻¹ * x * r ∈ normalizer (A₁ : Set G) ∧
        r⁻¹ * x * r ∈ normalizer (A₂ : Set G) := by
      have hn1 := square_normalizes l hwr
      have hn2 : r⁻¹ * x * r ∈ normalizer (A₂ : Set G) := by
        apply (mem_normalizer_iff_conjugate_eq _ _).mpr
        have hw2' : w ^ 2 = v * (t⁻¹ * v * t) := by simpa [t] using hw2
        have hxw : x = w ^ 2 := by simpa [x] using hw2'.symm
        have hpow : r⁻¹ * w ^ 2 * r = (r⁻¹ * w * r) ^ 2 := by
          simp only [pow_two]
          group
        rw [hxw, hpow, pow_two, ← conjugate_conjugate]
        rcases l.permutes_pair (r⁻¹ * w * r) hwr with hn | hs'
        · rw [hn.2, hn.2]
        · rw [hs'.2, hs'.1]
      have hw2' : w ^ 2 = v * (t⁻¹ * v * t) := by simpa [t] using hw2
      have hxw : x = w ^ 2 := by simpa [x] using hw2'.symm
      have hpow : r⁻¹ * w ^ 2 * r = (r⁻¹ * w * r) ^ 2 := by
        simp only [pow_two]
        group
      have hxrw : r⁻¹ * x * r = (r⁻¹ * w * r) ^ 2 := by rw [hxw, hpow]
      exact ⟨by simpa [hxrw] using hn1, hn2⟩
    have htrU : r⁻¹ * t * r ∈ (A₁ : Set G) ∪ A₂ := by
      have hqS : q⁻¹ * a * q ∈ S := by
        simpa [hr, t, mul_assoc] using ht'r
      have hqU := m.setup.closed_in_generated.2 a ha q hq
          ⟨(intersectionGenerated A₁ A₂).mul_mem
              ((intersectionGenerated A₁ A₂).mul_mem
                ((intersectionGenerated A₁ A₂).inv_mem hq)
                (m.setup.union_subset_generated ha)) hq,
            hqS⟩
      simpa [hr, t, mul_assoc] using hqU
    exact rebased_diagonal_contradiction m.setup ht2 hv2 hvHg hq hr ht'r htrU
      hxr hxnorm (by rfl)
  · intro v hv hv2 hvout hvHg u hu hy2 hfour
    let x := v * (t⁻¹ * v * t)
    have hx2 : orderOf x = 2 :=
      DiagonalConstruction.diagonal_involution m.setup hs hcap hv hv2 hvout
    have hxc : Commute x t := by
      apply mem_centralizer_singleton_iff.mp
      exact DiagonalConstruction.diagonal_range_centralizes m.setup hs.1 ht2
        ⟨⟨v, hv⟩, rfl⟩
    let y := u * (t⁻¹ * u * t)
    have hyc : Commute y t := by
      apply mem_centralizer_singleton_iff.mp
      exact DiagonalConstruction.diagonal_range_centralizes m.setup hs.1 ht2
        ⟨⟨u, hu⟩, rfl⟩
    let E := (zpowers t ⊔ zpowers x) ⊔ zpowers y
    have hEP : IsPGroup 2 E := by
      apply commuting_three_isPGroup
      · exact ht2
      · exact hx2
      · exact hy2
      · exact hxc.symm
      · exact hyc.symm
      · let := hfour
        exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
          (⟨x, subset_closure (by simp)⟩ : closure ({x, y} : Set G))
          (⟨y, subset_closure (by simp)⟩ : closure ({x, y} : Set G)))
    have hEC : E ≤ centralizer ({t} : Set G) := by
      apply sup_le
      · apply sup_le
        · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
        · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxc.eq)
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyc.eq)
    obtain ⟨q, hq, r, hr, hEr⟩ := htransport hEC hEP
    have htE : t ∈ E := by
      apply (show zpowers t ⊔ zpowers x ≤ E from le_sup_left)
      exact (le_sup_left : zpowers t ≤ zpowers t ⊔ zpowers x) (mem_zpowers t)
    have hxE : x ∈ E := by
      apply (show zpowers t ⊔ zpowers x ≤ E from le_sup_left)
      exact (le_sup_right : zpowers x ≤ zpowers t ⊔ zpowers x) (mem_zpowers x)
    have hyE : y ∈ E := by
      apply (show zpowers y ≤ E from le_sup_right)
      exact mem_zpowers y
    have ht'r : r⁻¹ * t * r ∈ S := hEr (mem_map.mpr ⟨t, htE, by simp⟩)
    have hxr : r⁻¹ * x * r ∈ S := hEr (mem_map.mpr ⟨x, hxE, by simp⟩)
    have hyr : r⁻¹ * y * r ∈ S := hEr (mem_map.mpr ⟨y, hyE, by simp⟩)
    have htrU : r⁻¹ * t * r ∈ (A₁ : Set G) ∪ A₂ := by
      have hqS : q⁻¹ * a * q ∈ S := by
        simpa [hr, t, mul_assoc] using ht'r
      have hqU := m.setup.closed_in_generated.2 a ha q hq
          ⟨(intersectionGenerated A₁ A₂).mul_mem
              ((intersectionGenerated A₁ A₂).mul_mem
                ((intersectionGenerated A₁ A₂).inv_mem hq)
                (m.setup.union_subset_generated ha)) hq,
            hqS⟩
      simpa [hr, t, mul_assoc] using hqU
    have hrout : r⁻¹ ∉ intersectionGenerated A₁ A₂ := by
      intro hrH
      apply hg
      have hgr : g = q * r⁻¹ := by rw [hr]; group
      rw [hgr]
      exact (intersectionGenerated A₁ A₂).mul_mem hq hrH
    have hv'r : r⁻¹ * v * r ∉ intersectionGenerated A₁ A₂ := by
      intro hvH
      apply hvHg
      exact rebased_mem_conjugate hq hr hvH
    have hxswap :
        conjugate A₁ (r⁻¹ * x * r) = A₂ ∧
          conjugate A₂ (r⁻¹ * x * r) = A₁ := by
      rcases l.permutes_pair (r⁻¹ * x * r) hxr with hn | hs'
      · have hbad := rebased_diagonal_contradiction m.setup ht2 hv2 hvHg hq hr ht'r
          htrU hxr
          ⟨(mem_normalizer_iff_conjugate_eq _ _).mpr hn.1,
            (mem_normalizer_iff_conjugate_eq _ _).mpr hn.2⟩ (by rfl)
        exact hbad.elim
      · exact hs'
    have hIne : (A₁ ⊓ A₂ : Subgroup G) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hcap
      simp at hcap
    obtain ⟨z₀, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIne
    let z : G := z₀
    have hz : z ∈ (A₁ ⊓ A₂ : Subgroup G) := z₀.property
    have hz1' : z ≠ 1 := by
      intro he
      exact hz1 (Subtype.ext he)
    have hz2 : orderOf z = 2 := by
      apply orderOf_eq_prime
      · have hh := congrArg Subtype.val
          (show (⟨z, hz⟩ : (A₁ ⊓ A₂ : Subgroup G)) ^ 2 = 1 from
            hcap ▸ pow_card_eq_one')
        simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one,
          pow_two] using hh
      · exact hz1'
    have hzC : z ∈ centralizer ({t} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hh := DiagonalConstruction.intersection_fixed hs hcap hz
      have hh' : t⁻¹ * z * t = z := by simpa [t] using hh
      have htz : z * t = t * z := by
        calc
          z * t = t * (t⁻¹ * z * t) := by group
          _ = t * z := by rw [hh']
      exact htz
    have hzH : r⁻¹ * z * r ∈ intersectionGenerated A₁ A₂ := by
      have hzHg : z ∈ conjugate (intersectionGenerated A₁ A₂) g := by
        apply hcent
        simpa [t] using hzC
      rcases mem_map.mp hzHg with ⟨z₀, hz₀, hzEq⟩
      have hzEq' : g * z * g⁻¹ = z₀ := by
        have hh : g⁻¹ * z₀ * g = z := by
          simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply, inv_inv] using hzEq
        rw [← hh]
        group
      have heq : r⁻¹ * z * r = q⁻¹ * z₀ * q := by
        have heq0 : (g⁻¹ * q)⁻¹ * z * (g⁻¹ * q) =
            q⁻¹ * (g * z * g⁻¹) * q := by group
        rw [hr, heq0, hzEq']
      rw [heq]
      exact (intersectionGenerated A₁ A₂).mul_mem
        ((intersectionGenerated A₁ A₂).mul_mem
          ((intersectionGenerated A₁ A₂).inv_mem hq) hz₀) hq
    have candidate_not_invol_left (htA : r⁻¹ * t * r ∈ A₁) {c d : G}
        (hc : c ∈ A₁) (hd : d = c * (t⁻¹ * c * t))
        (hd2 : orderOf d = 2) (hdS : r⁻¹ * d * r ∈ S)
        (hdN : r⁻¹ * d * r ∈ normalizer (A₁ : Set G)) : c ^ 2 ≠ 1 := by
      intro hc2
      have hc1 : c⁻¹ = c := by
        apply inv_eq_of_mul_eq_one_left
        simpa only [pow_two] using hc2
      have ht1 : t⁻¹ = t := by
        apply inv_eq_of_mul_eq_one_left
        simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1
      have hconj : c⁻¹ * t * c = d * t := by
        rw [hc1, hd, ht1]
        have htsq : t * t = 1 := by
          simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1
        simp only [mul_assoc, htsq, mul_one]
      have hconj' : (r⁻¹ * c * r)⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * c * r) =
          (r⁻¹ * d * r) * (r⁻¹ * t * r) := by
        have hh := congrArg (MulAut.conj r⁻¹) hconj
        rw [show (r⁻¹ * c * r)⁻¹ = r⁻¹ * c⁻¹ * r by group]
        simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          MulAut.conj_apply, inv_inv, map_mul] using hh
      have hcH : r⁻¹ * c * r ∈ intersectionGenerated A₁ A₂ := by
        apply m.setup.transporter_mem_of_left_normalizer (Or.inl htA)
          (by
            have hne : r⁻¹ * t * r ≠ 1 := by
              intro he
              have ho : orderOf (r⁻¹ * t * r) = 2 := by
                simpa only [MulEquiv.toMonoidHom_eq_coe,
                  MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using
                  (MulAut.conj r⁻¹).orderOf_eq t |>.trans ht2
              rw [he] at ho
              simp at ho
            exact hne)
        rw [hconj']
        exact ⟨(S : Subgroup G).mul_mem hdS ht'r,
          (normalizer (A₁ : Set G)).mul_mem hdN (A₁.le_normalizer htA)⟩
      let X := closure ({c, z} : Set G)
      have hXle : X ≤ A₁ := by
        apply (closure_le _).mpr
        intro b hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with rfl | rfl
        · exact hc
        · exact hz.1
      have hcz : c ≠ z := by
        intro he
        apply (show d ≠ 1 by
          intro hd1
          have := orderOf_eq_one_iff.mpr hd1
          omega)
        rw [hd, he, DiagonalConstruction.intersection_fixed hs hcap hz]
        have hzsq : z * z = 1 := by
          have hh := pow_orderOf_eq_one z
          rw [hz2] at hh
          simpa only [pow_two] using hh
        exact hzsq
      have hczcomm : Commute c z := DiagonalConstruction.factors_commute m.setup hc hz.2
      have hXfour : IsKleinFour X := by
        have hh := isKleinFour_closure_pair_of_orderOf c z
          (orderOf_eq_prime hc2 (by
            intro hc1
            apply (show d ≠ 1 by
              intro hd1
              have := orderOf_eq_one_iff.mpr hd1
              omega)
            rw [hd, hc1]
            simp)) hz2 hcz hczcomm
        simpa [X] using hh
      have hXcard : 2 < Nat.card X := by
        rw [hXfour.card_four]
        omega
      have hrnot : r ∉ intersectionGenerated A₁ A₂ := by
        intro hrH
        exact hrout ((intersectionGenerated A₁ A₂).inv_mem hrH)
      have hXr : conjugate X r ≤ intersectionGenerated A₁ A₂ := by
        apply Subgroup.map_le_iff_le_comap.mpr
        apply (closure_le _).mpr
        intro b hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with rfl | rfl
        · show (MulEquiv.toMonoidHom (MulAut.conj r⁻¹)) b ∈ intersectionGenerated A₁ A₂
          simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply, inv_inv] using hcH
        · show (MulEquiv.toMonoidHom (MulAut.conj r⁻¹)) z ∈ intersectionGenerated A₁ A₂
          simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply, inv_inv] using hzH
      exact hrnot (((l.unique_large X (Or.inl hXle) hXcard).2 r).mp hXr)
    have candidate_not_invol_right (htA : r⁻¹ * t * r ∈ A₂) {c d : G}
        (hc : c ∈ A₁) (hd : d = c * (t⁻¹ * c * t))
        (hd2 : orderOf d = 2) (hdS : r⁻¹ * d * r ∈ S)
        (hdN : r⁻¹ * d * r ∈ normalizer (A₂ : Set G)) : c ^ 2 ≠ 1 := by
      intro hc2
      have hc1 : c⁻¹ = c := by
        apply inv_eq_of_mul_eq_one_left
        simpa only [pow_two] using hc2
      have ht1 : t⁻¹ = t := by
        apply inv_eq_of_mul_eq_one_left
        simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1
      have hconj : c⁻¹ * t * c = d * t := by
        rw [hc1, hd, ht1]
        have htsq : t * t = 1 := by
          simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht2).1
        simp only [mul_assoc, htsq, mul_one]
      have hconj' : (r⁻¹ * c * r)⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * c * r) =
          (r⁻¹ * d * r) * (r⁻¹ * t * r) := by
        have hh := congrArg (MulAut.conj r⁻¹) hconj
        rw [show (r⁻¹ * c * r)⁻¹ = r⁻¹ * c⁻¹ * r by group]
        simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          MulAut.conj_apply, inv_inv, map_mul] using hh
      have hcH : r⁻¹ * c * r ∈ intersectionGenerated A₁ A₂ := by
        apply m.setup.transporter_mem_of_right_normalizer (Or.inr htA)
          (by
            have hne : r⁻¹ * t * r ≠ 1 := by
              intro he
              have ho : orderOf (r⁻¹ * t * r) = 2 := by
                simpa only [MulEquiv.toMonoidHom_eq_coe,
                  MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using
                  (MulAut.conj r⁻¹).orderOf_eq t |>.trans ht2
              rw [he] at ho
              simp at ho
            exact hne)
        rw [hconj']
        exact ⟨(S : Subgroup G).mul_mem hdS ht'r,
          (normalizer (A₂ : Set G)).mul_mem hdN (A₂.le_normalizer htA)⟩
      let X := closure ({c, z} : Set G)
      have hXle : X ≤ A₁ := by
        apply (closure_le _).mpr
        intro b hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with rfl | rfl
        · exact hc
        · exact hz.1
      have hcz : c ≠ z := by
        intro he
        apply (show d ≠ 1 by
          intro hd1
          have := orderOf_eq_one_iff.mpr hd1
          omega)
        rw [hd, he, DiagonalConstruction.intersection_fixed hs hcap hz]
        have hzsq : z * z = 1 := by
          have hh := pow_orderOf_eq_one z
          rw [hz2] at hh
          simpa only [pow_two] using hh
        exact hzsq
      have hczcomm : Commute c z := DiagonalConstruction.factors_commute m.setup hc hz.2
      have hXfour : IsKleinFour X := by
        have hh := isKleinFour_closure_pair_of_orderOf c z
          (orderOf_eq_prime hc2 (by
            intro hc1
            apply (show d ≠ 1 by
              intro hd1
              have := orderOf_eq_one_iff.mpr hd1
              omega)
            rw [hd, hc1]
            simp)) hz2 hcz hczcomm
        simpa [X] using hh
      have hXcard : 2 < Nat.card X := by
        rw [hXfour.card_four]
        omega
      have hrnot : r ∉ intersectionGenerated A₁ A₂ := by
        intro hrH
        exact hrout ((intersectionGenerated A₁ A₂).inv_mem hrH)
      have hXr : conjugate X r ≤ intersectionGenerated A₁ A₂ := by
        apply Subgroup.map_le_iff_le_comap.mpr
        apply (closure_le _).mpr
        intro b hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with rfl | rfl
        · show (MulEquiv.toMonoidHom (MulAut.conj r⁻¹)) b ∈ intersectionGenerated A₁ A₂
          simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply, inv_inv] using hcH
        · show (MulEquiv.toMonoidHom (MulAut.conj r⁻¹)) z ∈ intersectionGenerated A₁ A₂
          simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply, inv_inv] using hzH
      exact hrnot (((l.unique_large X (Or.inl hXle) hXcard).2 r).mp hXr)
    rcases htrU with htA | htA
    · rcases l.permutes_pair (r⁻¹ * y * r) hyr with hyfix | hyswap
      · have hyN : r⁻¹ * y * r ∈ normalizer (A₁ : Set G) :=
          (mem_normalizer_iff_conjugate_eq _ _).mpr hyfix.1
        have hu2ne := candidate_not_invol_left htA hu (by rfl) hy2 hyr hyN
        exact ⟨u, by simp, hu2ne, by
          refine ⟨r⁻¹, hrout, ?_⟩
          have hh := transport_factor_geometry (d := y) htA hyN
          have hnorm : u * (t⁻¹ * u * t) ∈ normalizer (conjugate A₁ r⁻¹ : Set G) := by
            simpa [y] using hh.2
          exact Or.inl ⟨by simpa [t] using hh.1, by simpa [t] using hnorm⟩⟩
      · have hxyN : r⁻¹ * (x * y) * r ∈ normalizer (A₁ : Set G) := by
          apply (mem_normalizer_iff_conjugate_eq _ _).mpr
          have hmap : r⁻¹ * (x * y) * r = (r⁻¹ * x * r) * (r⁻¹ * y * r) := by group
          rw [hmap, ← conjugate_conjugate, hxswap.1, hyswap.2]
        have hxyS : r⁻¹ * (x * y) * r ∈ S := by
          have hmap : r⁻¹ * (x * y) * r = (r⁻¹ * x * r) * (r⁻¹ * y * r) := by group
          rw [hmap]
          exact (S : Subgroup G).mul_mem hxr hyr
        have hxyEq : (v * u) * (t⁻¹ * (v * u) * t) = x * y := by
          have hh := (DiagonalConstruction.diagonalHom m.setup hs.1).map_mul
            (⟨v, hv⟩ : A₁) (⟨u, hu⟩ : A₁)
          change (v * u) * (t⁻¹ * (v * u) * t) = x * y at hh
          exact hh
        have hvu2ne := candidate_not_invol_left htA (A₁.mul_mem hv hu) hxyEq.symm
          (by
            have hh := DiagonalConstruction.diagonal_four_replace m.setup hs.1 hv hu
              (DiagonalConstruction.diagonal_involution m.setup hs hcap hv hv2 hvout)
              hy2 hfour (by simp : v * u ∈ ({u, v * u} : Set G))
            have hxy2 : orderOf (x * y) = 2 := by rw [← hxyEq]; exact hh.2.1
            exact hxy2) hxyS hxyN
        exact ⟨v * u, by simp, hvu2ne, by
          refine ⟨r⁻¹, hrout, ?_⟩
          have hh := transport_factor_geometry (d := x * y) htA hxyN
          have hnorm : (v * u) * (t⁻¹ * (v * u) * t) ∈
              normalizer (conjugate A₁ r⁻¹ : Set G) := by
            rw [hxyEq]
            exact hh.2
          exact Or.inl ⟨by simpa [t] using hh.1, by simpa [t] using hnorm⟩⟩
    · rcases l.permutes_pair (r⁻¹ * y * r) hyr with hyfix | hyswap
      · have hyN : r⁻¹ * y * r ∈ normalizer (A₂ : Set G) :=
          (mem_normalizer_iff_conjugate_eq _ _).mpr hyfix.2
        have hu2ne := candidate_not_invol_right htA hu (by rfl) hy2 hyr hyN
        exact ⟨u, by simp, hu2ne, by
          refine ⟨r⁻¹, hrout, ?_⟩
          have hh := transport_factor_geometry (d := y) htA hyN
          have hnorm : u * (t⁻¹ * u * t) ∈ normalizer (conjugate A₂ r⁻¹ : Set G) := by
            simpa [y] using hh.2
          exact Or.inr ⟨by simpa [t] using hh.1, by simpa [t] using hnorm⟩⟩
      · have hxyN : r⁻¹ * (x * y) * r ∈ normalizer (A₂ : Set G) := by
          apply (mem_normalizer_iff_conjugate_eq _ _).mpr
          have hmap : r⁻¹ * (x * y) * r = (r⁻¹ * x * r) * (r⁻¹ * y * r) := by group
          rw [hmap, ← conjugate_conjugate, hxswap.2, hyswap.1]
        have hxyS : r⁻¹ * (x * y) * r ∈ S := by
          have hmap : r⁻¹ * (x * y) * r = (r⁻¹ * x * r) * (r⁻¹ * y * r) := by group
          rw [hmap]
          exact (S : Subgroup G).mul_mem hxr hyr
        have hxyEq : (v * u) * (t⁻¹ * (v * u) * t) = x * y := by
          have hh := (DiagonalConstruction.diagonalHom m.setup hs.1).map_mul
            (⟨v, hv⟩ : A₁) (⟨u, hu⟩ : A₁)
          change (v * u) * (t⁻¹ * (v * u) * t) = x * y at hh
          exact hh
        have hvu2ne := candidate_not_invol_right htA (A₁.mul_mem hv hu) hxyEq.symm
          (by
            have hh := DiagonalConstruction.diagonal_four_replace m.setup hs.1 hv hu
              (DiagonalConstruction.diagonal_involution m.setup hs hcap hv hv2 hvout)
              hy2 hfour (by simp : v * u ∈ ({u, v * u} : Set G))
            have hxy2 : orderOf (x * y) = 2 := by rw [← hxyEq]; exact hh.2.1
            exact hxy2) hxyS hxyN
        exact ⟨v * u, by simp, hvu2ne, by
          refine ⟨r⁻¹, hrout, ?_⟩
          have hh := transport_factor_geometry (d := x * y) htA hxyN
          have hnorm : (v * u) * (t⁻¹ * (v * u) * t) ∈
              normalizer (conjugate A₂ r⁻¹ : Set G) := by
            rw [hxyEq]
            exact hh.2
          exact Or.inr ⟨by simpa [t] using hh.1, by simpa [t] using hnorm⟩⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
