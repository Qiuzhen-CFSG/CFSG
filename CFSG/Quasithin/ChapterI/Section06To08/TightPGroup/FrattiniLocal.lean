module

public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.Family
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.Frattini.PGroup
/-!
# The local Frattini obstruction for commuting conjugate factors

If a member `T` of the conjugate family permutes a pairwise commuting
subfamily `Γ`, and `Φ(Q)` is nontrivial, then `T` commutes with every
member of `Γ` distinct from itself. No maximality of `Γ` is used.

First, a nontrivial `N_T(A)` forces commutation. A nonidentity element
`x ∈ N_T(A)` and the central intersection theorem in the 2-group
`A ⊔ ⟨x⟩` give a nonidentity `z ∈ Z(A)` centralizing `x`. This replaces
the source's two involution choices. Normalizer control I.7.2(5) and
I.7.4 finish this step by considering whether `z` centralizes `T`.

Otherwise `N_T(A) = 1`, and with `W = ⟨Γ⟩` one has `T ∩ W = 1`.
An element `x ∈ T` of order four has `C_W(x²) ≤ C_G(T)`.
For an involution `u ∈ A`, write `uᵢ = xⁱ u x⁻ⁱ`. The fixed-point
condition gives `u₀u₂ = u₁u₃`, hence `u₂u₃ = u₀u₁`; applying it again
gives `u₁u₂ = u₀u₁`. Commutation of `u₀,u₁` yields `u₂ = u₀`,
contradicting the disjointness of `A` and its `x²`-conjugate. This
calculation replaces the elementary-abelian rank calculation in the source
and does not require the factors themselves to be abelian.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, I.7.5, printed pp.426--427
(PDF pp.437--438). Conjugation here is left conjugation, as in `Family`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

private theorem family_factor_normalizes {Γ : Set (Subgroup G)}
    (hc : Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G)))
    {A : Subgroup G} (hA : A ∈ Γ) : sSup Γ ≤ normalizer (A : Set G) := by
  apply sSup_le
  intro B hB
  by_cases heq : B = A
  · exact heq ▸ A.le_normalizer
  · exact (hc hB hA heq).trans (centralizer_le_normalizer _)

private theorem family_permuter_normalizes {Γ : Set (Subgroup G)} {T : Subgroup G}
    (ht : ∀ t ∈ T, ∀ A ∈ Γ, conjSubgroup A t ∈ Γ) :
    T ≤ normalizer ((sSup Γ : Subgroup G) : Set G) := by
  have hmap (t : G) (htT : t ∈ T) : conjSubgroup (sSup Γ) t ≤ sSup Γ := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA
    exact map_le_iff_le_comap.mp (le_sSup (ht t htT A hA))
  intro t htT
  apply mem_normalizer_iff.mpr
  intro w
  constructor
  · intro hw
    exact hmap t htT ⟨w, hw, rfl⟩
  · intro hw
    have hh := hmap t⁻¹ (T.inv_mem htT) ⟨t * w * t⁻¹, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh

private theorem centralizer_element_normalizes [Finite G] {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) {x : G} (hx : x ∈ Q) (hne : x ≠ 1) :
    S ⊓ centralizer ({x} : Set G) ≤ normalizer (Q : Set G) := by
  have hc : centralizer ({x} : Set G) ≤ normalizer (zpowers x : Set G) := by
    rw [zpowers_eq_closure]
    rw [← Subgroup.centralizer_closure ({x} : Set G)]
    exact centralizer_le_normalizer (closure ({x} : Set G) : Set G)
  exact (inf_le_inf_left S hc).trans
    ((lemma_I_7_2_5 h (by simpa using hne) (zpowers_le.mpr hx)).2.trans inf_le_right)

private theorem family_center_mem {Γ : Set (Subgroup G)}
    (hc : Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G)))
    {A : Subgroup G} (hA : A ∈ Γ) {z : G} (hz : z ∈ A)
    (hzc : z ∈ centralizer (A : Set G)) : z ∈ centralizer ((sSup Γ : Subgroup G) : Set G) := by
  have hle : sSup Γ ≤ centralizer ({z} : Set G) := by
    apply sSup_le
    intro B hB b hb
    apply mem_centralizer_singleton_iff.mpr
    by_cases heq : B = A
    · exact hzc b (heq ▸ hb)
    · exact (hc hA hB (Ne.symm heq) hz b hb)
  intro w hw
  exact mem_centralizer_singleton_iff.mp (hle hw)

private theorem conjugate_centralizer_mem {W : Subgroup G} {t z : G}
    (ht : t ∈ normalizer (W : Set G)) (hz : z ∈ centralizer (W : Set G)) :
    t * z * t⁻¹ ∈ centralizer (W : Set G) := by
  intro w hw
  have hh := hz (t⁻¹ * w * t) ((mem_normalizer_iff''.mp ht w).mp hw)
  have := congrArg (fun a : G => t * a * t⁻¹) hh
  simpa [mul_assoc] using this

variable [Finite G]
private theorem exists_central_fixed {S A : Subgroup G} (hp : IsPGroup 2 S)
    (hAS : A ≤ S) (hne : A ≠ ⊥) {x : G} (hxS : x ∈ S)
    (hxn : x ∈ normalizer (A : Set G)) :
    ∃ z ∈ A, z ≠ 1 ∧ z ∈ centralizer (A : Set G) ∧ Commute z x := by
  let U := A ⊔ zpowers x
  have hAU : A ≤ U := le_sup_left
  have hUS : U ≤ S := sup_le hAS (zpowers_le.mpr hxS)
  have hUN : U ≤ normalizer (A : Set G) :=
    sup_le A.le_normalizer (zpowers_le.mpr hxn)
  let : (A.subgroupOf U).Normal := (normal_subgroupOf_iff_le_normalizer hAU).mpr hUN
  let : Fact (IsPGroup 2 U) := ⟨hp.to_le hUS⟩
  let : Nontrivial (A.subgroupOf U) := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
    intro heq
    apply hne
    rw [← map_subgroupOf_eq_of_le hAU, heq, Subgroup.map_bot])
  obtain ⟨z, hz, hzc⟩ := exists_nontrivial_center_mem_normal (p := 2) (A.subgroupOf U)
  refine ⟨z.val.val, z.property, ?_, ?_, ?_⟩
  · intro heq
    exact hz (Subtype.ext (Subtype.ext heq))
  · intro a ha
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzc) ⟨a, hAU ha⟩)
  · exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzc)
      ⟨x, (le_sup_right : zpowers x ≤ U) (mem_zpowers x)⟩)).symm
/-- The normalizer step `(∗)` of I.7.5, without a Frattini or maximality
hypothesis: a nontrivial relative normalizer forces the two factors to commute. -/
theorem TightPGroupSetup.family_commuting_of_nontrivial_normalizer {K H Q S T A : Subgroup G}
    (h : TightPGroupSetup K H Q S) {Γ : Set (Subgroup G)}
    (hΓ : Γ ⊆ tightConjugateFamily H Q S)
    (hc : Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G)))
    (hT : T ∈ tightConjugateFamily H Q S)
    (ht : ∀ t ∈ T, ∀ B ∈ Γ, conjSubgroup B t ∈ Γ)
    (hA : A ∈ Γ) (hne : A ≠ T)
    (hn : T ⊓ normalizer (A : Set G) ≠ ⊥) : A ≤ centralizer (T : Set G) := by
  obtain ⟨KA, hKA⟩ := h.family_setup (hΓ hA)
  obtain ⟨KT, hKT⟩ := h.family_setup hT
  obtain ⟨x, hxne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  have hx := x.property
  have hxne : (x : G) ≠ 1 := fun heq => hxne' (Subtype.ext heq)
  obtain ⟨z, hzA, hzne, hzcA, hzx⟩ := exists_central_fixed h.hSp
    (hΓ hA).1 hKA.hQne (hT.1 hx.1) hx.2
  have hzS : z ∈ S := (hΓ hA).1 hzA
  have hzW := family_center_mem hc hA hzA hzcA
  have hzNT : z ∈ normalizer (T : Set G) :=
    centralizer_element_normalizes hKT hx.1 hxne
      ⟨hzS, mem_centralizer_singleton_iff.mpr hzx.eq⟩
  by_cases hzT : z ∈ centralizer (T : Set G)
  · have hTN : T ≤ normalizer (A : Set G) := by
      intro t htT
      exact centralizer_element_normalizes hKA hzA hzne
        ⟨hT.1 htT, mem_centralizer_singleton_iff.mpr (hzT t htT)⟩
    exact h.family_commuting_of_normalizes (hΓ hA) hT hne hTN
  · obtain ⟨t, htT, htne⟩ : ∃ t ∈ T, t * z ≠ z * t := by
      change ¬ ∀ t : G, t ∈ T → t * z = z * t at hzT
      push Not at hzT
      exact hzT
    let y := z * t * z⁻¹ * t⁻¹
    have hyT : y ∈ T := T.mul_mem
      ((mem_normalizer_iff.mp hzNT t).mp htT) (T.inv_mem htT)
    have hyne : y ≠ 1 := by
      intro heq
      apply htne
      change z * t * z⁻¹ * t⁻¹ = 1 at heq
      have heq' : z * t = t * z := by
        calc
          z * t = (z * t * z⁻¹ * t⁻¹) * t * z := by group
          _ = t * z := by rw [heq, one_mul]
      exact heq'.symm
    have hyW : y ∈ centralizer ((sSup Γ : Subgroup G) : Set G) := by
      have hh := conjugate_centralizer_mem (family_permuter_normalizes ht htT)
        ((centralizer _).inv_mem hzW)
      convert (centralizer _).mul_mem hzW hh using 1
      simp [y, mul_assoc]
    have hAN : A ≤ normalizer (T : Set G) := by
      intro a ha
      exact centralizer_element_normalizes hKT hyT hyne
        ⟨(hΓ hA).1 ha, mem_centralizer_singleton_iff.mpr
          (hyW a (le_sSup hA ha))⟩
    exact le_centralizer_iff.mp
      (h.family_commuting_of_normalizes hT (hΓ hA) hne.symm hAN)

omit [Finite G] in
private theorem square_fixed_implies_orbit_two (W : Subgroup G) (f : G ≃* G) (u : G)
    (hu : u * u = 1) (h0 : u ∈ W) (h1 : f u ∈ W) (h2 : f (f u) ∈ W)
    (hperiod : f (f (f (f u))) = u)
    (hc01 : Commute u (f u)) (hc02 : Commute u (f (f u)))
    (hfix : ∀ v ∈ W, f (f v) = v → f v = v) : f (f u) = u := by
  have hnorm : f (u * f (f u)) = u * f (f u) := by
    apply hfix _ (W.mul_mem h0 h2)
    simp only [map_mul, hperiod]
    exact hc02.eq.symm
  have heq : u * f (f u) = f u * f (f (f u)) := by
    simpa only [map_mul] using hnorm.symm
  have h3 : f (f (f u)) * f (f (f u)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, hu, map_one, map_one, map_one]
  have hprod : f (f u) * f (f (f u)) = u * f u := by
    calc
      _ = u * (u * f (f u)) * f (f (f u)) := by rw [← mul_assoc u u, hu, one_mul]
      _ = u * (f u * f (f (f u))) * f (f (f u)) := by rw [heq]
      _ = u * f u := by rw [mul_assoc, mul_assoc, h3, mul_one]
  have hfixed : f (u * f u) = u * f u := by
    apply hfix _ (W.mul_mem h0 h1)
    simpa only [map_mul] using hprod
  have heq' : f u * f (f u) = f u * u := by
    calc
      _ = u * f u := by simpa only [map_mul] using hfixed
      _ = f u * u := hc01.eq
  exact mul_left_cancel heq'
private theorem exists_order_four_of_frattini_ne_bot (hp : IsPGroup 2 G) (hΦ : frattini G ≠ ⊥) :
    ∃ x : G, orderOf x = 4 := by
  have hex : ∃ x : G, x ^ 2 ≠ 1 := by
    by_contra! hall
    have hinv (x : G) : x⁻¹ = x :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hall x)
    let : IsElementaryAbelian 2 G := {
      is_comm := ⟨fun x y => by
        calc
          x * y = x⁻¹ * y⁻¹ := by rw [hinv x, hinv y]
          _ = (y * x)⁻¹ := (mul_inv_rev y x).symm
          _ = y * x := hinv _⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall }
    let : Fact (IsPGroup 2 G) := ⟨hp⟩
    exact hΦ (frattini_eq_bot_of_isElementaryAbelian (p := 2))
  obtain ⟨x, hx⟩ := hex
  obtain ⟨n, hn⟩ := hp.exists_orderOf_eq_pow x
  have hn2 : 2 ≤ n := by
    by_contra! hh
    apply hx
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hn]
    interval_cases n <;> norm_num
  have hdiv : 4 ∣ orderOf x := by
    rw [hn]
    exact pow_dvd_pow 2 hn2
  exact ⟨x ^ (orderOf x / 4), orderOf_pow_orderOf_div (orderOf_pos x).ne' hdiv⟩

private theorem exists_involution_of_two_group (hp : IsPGroup 2 G) [Nontrivial G] : ∃ x : G, orderOf x = 2 := by
  obtain ⟨n, hn, heq⟩ := hp.nontrivial_iff_card.mp inferInstance
  exact exists_prime_orderOf_dvd_card' 2 (heq ▸ dvd_pow_self 2 hn.ne')

private theorem free_normalizer_impossible {K H Q S T A : Subgroup G}
    (h : TightPGroupSetup K H Q S) {Γ : Set (Subgroup G)}
    (hΓ : Γ ⊆ tightConjugateFamily H Q S)
    (hc : Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G)))
    (hT : T ∈ tightConjugateFamily H Q S)
    (ht : ∀ t ∈ T, ∀ B ∈ Γ, conjSubgroup B t ∈ Γ)
    (hA : A ∈ Γ) (hn : T ⊓ normalizer (A : Set G) = ⊥)
    (x : G) (hxT : x ∈ T) (hx4 : x ^ 4 = 1) (hx2 : x ^ 2 ≠ 1) : False := by
  let W : Subgroup G := sSup Γ
  have hWS : W ≤ S := sSup_le fun B hB => (hΓ hB).1
  have hTNW : T ≤ normalizer (W : Set G) := family_permuter_normalizes ht
  have hWNA : W ≤ normalizer (A : Set G) := family_factor_normalizes hc hA
  have hTW : T ⊓ W = ⊥ := eq_bot_iff.mpr (by
    rw [← hn]
    exact inf_le_inf_left T hWNA)
  obtain ⟨KT, hKT⟩ := h.family_setup hT
  have hC : W ⊓ centralizer ({x ^ 2} : Set G) ≤ centralizer (T : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply eq_bot_iff.mpr
    rw [← hTW]
    refine le_inf ?_ ?_
    · apply le_normalizer_iff_commutator_le_right.mp
      exact (inf_le_inf_right _ hWS).trans
        (centralizer_element_normalizes hKT (T.pow_mem hxT 2) hx2)
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hTNW)
  have hneq (g : G) (hg : g ∈ T) (hg1 : g ≠ 1) : A ≠ conjSubgroup A g := by
    intro heq
    have hgn : g ∈ normalizer (A : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr heq.symm
    have hh : g ∈ T ⊓ normalizer (A : Set G) := ⟨hg, hgn⟩
    exact hg1 (mem_bot.mp (hn ▸ hh))
  obtain ⟨KA, hKA⟩ := h.family_setup (hΓ hA)
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hKA.hQne
  obtain ⟨uA, huA⟩ := exists_involution_of_two_group hKA.hQp
  let u : G := uA
  have hu2 : u * u = 1 := by
    have hh := pow_orderOf_eq_one uA
    rw [huA] at hh
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mul, pow_two] using congrArg Subtype.val hh
  have hune : u ≠ 1 := by
    intro hh
    have hh' : uA = 1 := Subtype.ext hh
    simp [hh'] at huA
  let f : G ≃* G := MulAut.conj x
  have hfu : f u ∈ conjSubgroup A x := ⟨u, uA.property, rfl⟩
  have hffu : f (f u) ∈ conjSubgroup A (x ^ 2) := by
    refine ⟨u, uA.property, ?_⟩
    simp [f, MulAut.conj_apply, pow_two, mul_assoc]
  have h1 : conjSubgroup A x ∈ Γ := ht x hxT A hA
  have h2 : conjSubgroup A (x ^ 2) ∈ Γ := ht _ (T.pow_mem hxT 2) A hA
  have hxne : x ≠ 1 := by intro hh; simp [hh] at hx2
  have hc01 : Commute u (f u) :=
    (hc hA h1 (hneq x hxT hxne) uA.property (f u) hfu).symm
  have hc02 : Commute u (f (f u)) :=
    (hc hA h2 (hneq _ (T.pow_mem hxT 2) hx2) uA.property _ hffu).symm
  have hperiod : f (f (f (f u))) = u := by
    have hh := congrArg (fun g : G => g * u * g⁻¹) hx4
    simpa [f, MulAut.conj_apply, pow_succ, mul_assoc] using hh
  have hfix : ∀ v ∈ W, f (f v) = v → f v = v := by
    intro v hv hfv
    have hh : x ^ 2 * v * (x ^ 2)⁻¹ = v := by
      simpa [f, MulAut.conj_apply, pow_two, mul_assoc] using hfv
    have hvC : v ∈ centralizer ({x ^ 2} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hvc := hC ⟨hv, hvC⟩ x hxT
    exact mul_inv_eq_iff_eq_mul.mpr hvc
  have heq := square_fixed_implies_orbit_two W f u hu2 (le_sSup hA uA.property)
    (le_sSup h1 hfu) (le_sSup h2 hffu) hperiod hc01 hc02 hfix
  exact hune ((h.family_disjoint (hΓ hA) (hΓ h2)
    (hneq _ (T.pow_mem hxT 2) hx2)).le_bot ⟨uA.property, heq ▸ hffu⟩)

/-- The local Frattini obstruction in I.7.5. A conjugate-family member
permuting a pairwise commuting subfamily centralizes every distinct member,
provided the original factor has nontrivial Frattini subgroup. -/
theorem TightPGroupSetup.family_commuting_of_permuting_of_frattini_ne_bot
    {K H Q S T A : Subgroup G} (h : TightPGroupSetup K H Q S)
    (hΦ : frattini Q ≠ ⊥) {Γ : Set (Subgroup G)}
    (hΓ : Γ ⊆ tightConjugateFamily H Q S)
    (hc : Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G)))
    (hT : T ∈ tightConjugateFamily H Q S)
    (ht : ∀ t ∈ T, ∀ B ∈ Γ, conjSubgroup B t ∈ Γ)
    (hA : A ∈ Γ) (hne : A ≠ T) : A ≤ centralizer (T : Set G) := by
  by_contra hnot
  have hn : T ⊓ normalizer (A : Set G) = ⊥ := by
    by_contra hnb
    exact hnot (h.family_commuting_of_nontrivial_normalizer hΓ hc hT ht hA hne hnb)
  obtain ⟨q, hq⟩ := exists_order_four_of_frattini_ne_bot h.hQp hΦ
  obtain ⟨g, _, hgT⟩ := hT.2
  let x : G := (MulAut.conj g) (q : G)
  have hxT : x ∈ T := hgT ▸ (show x ∈ conjSubgroup Q g from ⟨q, q.property, rfl⟩)
  have hxo : orderOf x = 4 := (MulAut.conj g).orderOf_eq (q : G) |>.trans
    ((Subgroup.orderOf_coe q).trans hq)
  have hx4 : x ^ 4 = 1 := hxo ▸ pow_orderOf_eq_one x
  have hx2 : x ^ 2 ≠ 1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hxo] at hd
    norm_num at hd
  exact free_normalizer_impossible h hΓ hc hT ht hA hn x hxT hx4 hx2

end CFSG.Quasithin.ChapterI.Section06To08
