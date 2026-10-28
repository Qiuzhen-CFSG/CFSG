module

public import Theory.SpecificGroups.Suzuki.EightOddTori
public import Theory.SpecificGroups.Suzuki.FieldTorus
public import Theory.SpecificGroups.Suzuki.EightOuterTori.LinearInput
public import Theory.SpecificGroups.Suzuki.EightOuterTori.ThirteenLinear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Full automorphism actions on the odd tori of Sz(8)

On the split torus, inner normalizer elements act as identity or inversion.
The defining-field action has cube one, so an inner-field product fixing the
torus pointwise has trivial field part. The torus coordinates detect that
field part faithfully. This proves pointwise rigidity for every Sylow
seven-subgroup and the exact outer index three.

Sylow conjugacy gives the order of each stabilizer in the full automorphism
group. Pointwise rigidity bounds the restriction kernel; counting then proves
surjectivity onto the torus automorphism group, through the literal inclusion.
For the thirteen-subgroup, `EightOuterTori.thirteen_twist_separation` removes
the field part by characteristic-polynomial descent from GF(8) to GF(2).
Thus both Sylow subgroups have only inner pointwise fixers and every torus
automorphism extends to Sz(8), giving full automizer orders six and twelve.

Source: Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449),
`refs/quasithin.pdf`; GLS3, Theorems 2.5.12 and 6.5.4. We use left
conjugation throughout and do not infer a torus action merely from outer order.
-/

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped Pointwise IsMulCommutative
public section

namespace BenderSuzuki.MatrixGroups

open EightOuterTori
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
private theorem field_mem_split (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    {x : SuzukiMatrixGroup m} (hx : x ∈ SuzukiSplitTorus m) :
    suzukiFieldAut m σ x ∈ SuzukiSplitTorus m := by
  obtain ⟨u, hu⟩ := (mem_suzukiSplitTorus_iff m x).mp hx
  have he : x = splitTorusElement m u := Subtype.ext hu
  rw [he, field_splitTorusElement]
  exact splitTorusElement_mem m _

private theorem field_cube
    (σ : BinaryGaloisField 3 ≃ₐ[ZMod 2] BinaryGaloisField 3) :
    suzukiFieldAut 1 σ ^ 3 = 1 := by
  have hc : Nat.card (BinaryGaloisField 3 ≃ₐ[ZMod 2] BinaryGaloisField 3) = 3 :=
    suzukiFieldAut_card 1
  have hσ : σ ^ 3 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := σ))
  simpa only [map_pow, map_one, suzukiFieldAutHom_apply] using
    congrArg (suzukiFieldAutHom 1) hσ

private theorem split_conj (g : SuzukiMatrixGroup 1)
    (hg : g ∈ normalizer (SuzukiSplitTorus 1)) :
    (∀ x : SuzukiSplitTorus 1, MulAut.conj g x = x) ∨
    (∀ x : SuzukiSplitTorus 1, MulAut.conj g x = (x : SuzukiMatrixGroup 1)⁻¹) := by
  let := suzukiSplitTorus_isCyclic 1 (by decide)
  have ht (t x : SuzukiSplitTorus 1) : MulAut.conj (t : SuzukiMatrixGroup 1) x = x := by
    change (t : SuzukiMatrixGroup 1) * x * (t : SuzukiMatrixGroup 1)⁻¹ = x
    have h := congrArg Subtype.val (mul_comm t x)
    change (t : SuzukiMatrixGroup 1) * x = (x : SuzukiMatrixGroup 1) * t at h
    rw [h, mul_inv_cancel_right]
  rcases (suzukiSplitTorus_normalizer_forms 1 (by decide) g).mp hg with hg | ⟨t, rfl⟩
  · exact Or.inl (ht ⟨g, hg⟩)
  · right
    intro x
    rw [map_mul, MulAut.mul_apply]
    have hw : MulAut.conj (suzukiWeyl 1) x = (x : SuzukiMatrixGroup 1)⁻¹ := by
      simpa only [MulAut.conj_apply, suzukiWeyl_inv] using suzukiWeyl_conj_splitTorus 1 x
    rw [hw]
    exact ht t x⁻¹

private theorem split_field_inner_separation
    (g : SuzukiMatrixGroup 1)
    (σ : BinaryGaloisField 3 ≃ₐ[ZMod 2] BinaryGaloisField 3)
    (hfix : ∀ x : SuzukiSplitTorus 1, (MulAut.conj g * suzukiFieldAut 1 σ) x = x) :
    σ = 1 := by
  let T := SuzukiSplitTorus 1
  let f := suzukiFieldAut 1 σ
  have hf : f ^ 3 = 1 := field_cube σ
  have hconj (x : T) : MulAut.conj g x = f (f x) := by
    have h := hfix ⟨f (f x), field_mem_split 1 σ (field_mem_split 1 σ x.property)⟩
    have h3 : f (f (f x)) = (x : SuzukiMatrixGroup 1) := by
      simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using
        congrArg (fun a : MulAut (SuzukiMatrixGroup 1) => a x) hf
    change MulAut.conj g (f (f (f x))) = f (f x) at h
    rwa [h3] at h
  have hg : g ∈ normalizer T := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      change MulAut.conj g x ∈ T
      rw [hconj ⟨x, hx⟩]
      exact field_mem_split 1 σ (field_mem_split 1 σ hx)
    · rw [card_map_of_injective (MulAut.conj g).injective]
  have htwo : ∀ x : T, f (f x) = x := by
    rcases split_conj g hg with h | h
    · intro x
      exact (hconj x).symm.trans (h x)
    · have hinv (x : T) : f (f x) = (x : SuzukiMatrixGroup 1)⁻¹ :=
        (hconj x).symm.trans (h x)
      intro x
      have h6 : f (f (f (f (f (f x))))) = (x : SuzukiMatrixGroup 1) := by
        have he : f ^ 6 = 1 := by rw [show 6 = 3 * 2 from rfl, pow_mul, hf, one_pow]
        simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using
          congrArg (fun a : MulAut (SuzukiMatrixGroup 1) => a x) he
      have he : (x : SuzukiMatrixGroup 1)⁻¹ = x := by
        simpa only [map_inv, hinv x, inv_inv] using h6
      exact (hinv x).trans he
  have hone : ∀ x : T, f x = x := by
    intro x
    have h3 : f (f (f x)) = (x : SuzukiMatrixGroup 1) := by
      simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using
        congrArg (fun a : MulAut (SuzukiMatrixGroup 1) => a x) hf
    rwa [htwo x] at h3
  apply field_eq_one_of_torus_two_power 1 (by decide) σ
  intro u
  refine ⟨0, ?_⟩
  rw [hone ⟨splitTorusElement 1 u, splitTorusElement_mem 1 u⟩]
  simp

private theorem seven_split (Y : Sylow 7 (SuzukiMatrixGroup 1)) :
    ∃ g, (Y : Subgroup (SuzukiMatrixGroup 1)) =
      (SuzukiSplitTorus 1).map (MulAut.conj g).toMonoidHom := by
  rcases suzuki_eight_sylow_odd_torus (Or.inl rfl) Y with h | h
  · exact h
  · have hd := h.card_dvd
    rw [suzuki_eight_sylow_odd_card (Or.inl rfl) Y] at hd
    norm_num at hd

/-- Every pointwise fixer of a Sylow seven-subgroup is conjugation by one of its elements. -/
theorem suzuki_eight_sylow_seven_fixing_inner (Y : Sylow 7 (SuzukiMatrixGroup 1))
    (α : MulAut (SuzukiMatrixGroup 1)) (hfix : ∀ y : Y, α y = y) :
    ∃ y : Y, α = MulAut.conj (y : SuzukiMatrixGroup 1) := by
  obtain ⟨g, hg⟩ := seven_split Y
  let e := MulAut.conj g
  let β := MulAut.congr e.symm α
  have hβ : ∀ x : SuzukiSplitTorus 1, β x = x := by
    intro x
    have hx : e x ∈ Y := by
      change e x ∈ (Y : Subgroup (SuzukiMatrixGroup 1))
      rw [hg]
      exact mem_map_of_mem e.toMonoidHom x.property
    change e.symm (α (e x)) = x
    rw [hfix ⟨e x, hx⟩, e.symm_apply_apply]
  obtain ⟨t, σ, ht⟩ := suzukiAut_eq_inner_mul_field 1 (by decide) β
  have hσ : σ = 1 := split_field_inner_separation t σ (by simpa only [← ht] using hβ)
  have hb : β = MulAut.conj t := by
    simpa only [hσ, ← suzukiFieldAutHom_apply, map_one, mul_one] using ht
  have hα : α = MulAut.conj (e t) := by
    apply (MulAut.congr e.symm).injective
    rw [MulAut.congr_conj, e.symm_apply_apply]
    exact hb
  have hmem : e t ∈ Y := by
    change e t ∈ (Y : Subgroup (SuzukiMatrixGroup 1))
    rw [← suzuki_eight_sylow_odd_centralizer (Or.inl rfl) Y, mem_centralizer_iff]
    intro x hx
    have h := hfix ⟨x, hx⟩
    rw [hα] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  exact ⟨⟨e t, hmem⟩, hα⟩

/-- The full outer index of Sz(8) is exactly three; field twists are separated using the split torus. -/
theorem suzuki_eight_outer_index :
    (MulAut.conj : SuzukiMatrixGroup 1 →* MulAut (SuzukiMatrixGroup 1)).range.index = 3 := by
  let I := (MulAut.conj : SuzukiMatrixGroup 1 →* MulAut (SuzukiMatrixGroup 1)).range
  let f := (QuotientGroup.mk' I).comp (suzukiFieldAutHom 1)
  have hi : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply f.ker.eq_bot_iff_forall.mpr
    intro σ hσ
    change QuotientGroup.mk' I (suzukiFieldAutHom 1 σ) = 1 at hσ
    rw [suzukiFieldAutHom_apply] at hσ
    have hmem : suzukiFieldAut 1 σ ∈ I := (QuotientGroup.eq_one_iff _).mp hσ
    obtain ⟨g, hg⟩ := hmem
    apply split_field_inner_separation g⁻¹ σ
    intro x
    rw [← hg, map_inv, inv_mul_cancel, MulAut.one_apply]
  have hd : 3 ∣ I.index := by
    have h := card_dvd_of_injective f hi
    rw [suzukiFieldAut_card] at h
    exact h
  exact Nat.dvd_antisymm (suzuki_outer_index_dvd 1 (by decide)) hd

/-- The intrinsic normalizers of the two specified Sylow subgroups have orders fourteen and fifty-two. -/
theorem suzuki_eight_sylow_odd_normalizer_card {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1)) :
    Nat.card (normalizer ((Y : Subgroup (SuzukiMatrixGroup 1)) : Set (SuzukiMatrixGroup 1))) =
      p * ((p - 1)/ 3) := by
  rcases suzuki_eight_sylow_odd_torus hp Y with ⟨g, hg⟩ | hY
  · have hc := suzuki_eight_sylow_odd_card hp Y
    rw [hg, card_map_of_injective (MulAut.conj g).injective, suzukiSplitTorus_card 1 (by decide)] at hc
    have hp7 : p = 7 := by norm_num at hc; omega
    rw [hg, ← map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
      card_map_of_injective (MulAut.conj g).injective,
      suzukiSplitTorus_normalizer_card 1 (by decide), hp7]
    norm_num
  · have hd := hY.card_dvd
    rw [suzuki_eight_sylow_odd_card hp Y] at hd
    have hp13 : p = 13 := by rcases hp with rfl | rfl <;> norm_num at *
    have hi := hY.normalizer_index_eq_four (by decide)
    have hc := ((Y : Subgroup (SuzukiMatrixGroup 1)).subgroupOf
      (normalizer ((Y : Subgroup (SuzukiMatrixGroup 1)) : Set (SuzukiMatrixGroup 1)))).card_mul_index
    rw [show Nat.card ((Y : Subgroup (SuzukiMatrixGroup 1)).subgroupOf
        (normalizer ((Y : Subgroup (SuzukiMatrixGroup 1)) : Set (SuzukiMatrixGroup 1)))) = Nat.card Y from
        Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv,
      suzuki_eight_sylow_odd_card hp Y] at hc
    change p * (Y : Subgroup (SuzukiMatrixGroup 1)).relIndex (normalizer ((Y : Subgroup (SuzukiMatrixGroup 1)) : Set _)) = _ at hc
    rw [hi] at hc
    rw [← hc, hp13]

private theorem eight_center_eq_bot : center (SuzukiMatrixGroup 1) = ⊥ := by
  have hd (p : ℕ) [Fact p.Prime] (hp : p = 7 ∨ p = 13) :
      Nat.card (center (SuzukiMatrixGroup 1)) ∣ p := by
    let Y : Sylow p (SuzukiMatrixGroup 1) := default
    have h := center_le_centralizer (Y : Set (SuzukiMatrixGroup 1))
    rw [suzuki_eight_sylow_odd_centralizer hp Y] at h
    simpa only [suzuki_eight_sylow_odd_card hp Y] using card_dvd_of_le h
  exact card_eq_one.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 7 13)
    (hd 7 (Or.inl rfl)) (hd 13 (Or.inr rfl)))

private theorem eight_aut_card : Nat.card (MulAut (SuzukiMatrixGroup 1)) =
    Nat.card (SuzukiMatrixGroup 1) * 3 := by
  have h := (MulAut.conj : SuzukiMatrixGroup 1 →* MulAut (SuzukiMatrixGroup 1)).range.card_mul_index
  rw [suzuki_eight_outer_index, Nat.card_congr
    (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot eight_center_eq_bot)).toEquiv.symm] at h
  exact h.symm

private noncomputable def sylowRestriction {G : Type*} [Group G] {p : ℕ}
    (Y : Sylow p G) : MulAction.stabilizer (MulAut G) Y →* MulAut Y where
  toFun a := (a.val.subgroupMap (Y : Subgroup G)).trans
    (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup a.property))
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

private theorem sylow_extension_of_cards {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (Y : Sylow p G) (k : ℕ)
    (hAut : Nat.card (MulAut G) = Nat.card G * k)
    (hN : Nat.card (normalizer (Y : Set G)) * k =
      Nat.card Y * Nat.card (MulAut Y))
    (hfix : ∀ α : MulAut G, (∀ y : Y, α y = y) →
      ∃ y : Y, α = MulAut.conj (y : G))
    (β : MulAut Y) : ∃ α : MulAut G, ∀ y : Y, α (y : G) = (β y : G) := by
  classical
  let S := MulAction.stabilizer (MulAut G) Y
  let r := sylowRestriction Y
  have hpre : MulAction.IsPretransitive (MulAut G) (Sylow p G) := by
    constructor
    intro P Q
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
    exact ⟨MulAut.conj g,hg⟩
  let := hpre
  have hi : S.index = (normalizer (Y : Set G)).index := by
    rw [MulAction.index_stabilizer_of_transitive, ← Y.card_eq_index_normalizer]
  have hcardS : Nat.card S = Nat.card Y * Nat.card (MulAut Y) := by
    have hs := S.card_mul_index
    have hn := (normalizer (Y : Set G)).card_mul_index
    rw [hi, hAut, ← hn] at hs
    rw [← hN]
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (normalizer (Y : Set G)).index from
      Nat.pos_of_ne_zero (normalizer (Y : Set G)).index_ne_zero_of_finite)
    exact hs.trans (by ac_rfl)
  have hker : Nat.card r.ker ≤ Nat.card Y := by
    have hw (a : r.ker) : ∃ y : Y, a.val.val = MulAut.conj (y : G) := by
      apply hfix
      intro y
      exact congrArg (fun a : MulAut Y => (a y : G)) a.property
    choose f hf using hw
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      rw [hf a, hf b, hab]
    exact Nat.card_le_card_of_injective f hinj
  have hsurj : Function.Surjective r := by
    apply MonoidHom.surjective_of_card_ker_le_div
    rw [hcardS, Nat.mul_div_cancel _ Nat.card_pos]
    exact hker
  obtain ⟨a, ha⟩ := hsurj β
  exact ⟨a.val, fun y => congrArg (fun b : MulAut Y => (b y : G)) ha⟩

private theorem eight_extension_of_fixers {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1))
    (hfix : ∀ α : MulAut (SuzukiMatrixGroup 1), (∀ y : Y, α y = y) →
      ∃ y : Y, α = MulAut.conj (y : SuzukiMatrixGroup 1))
    (β : MulAut Y) : ∃ α : MulAut (SuzukiMatrixGroup 1),
      ∀ y : Y, α (y : SuzukiMatrixGroup 1) = (β y : SuzukiMatrixGroup 1) := by
  apply sylow_extension_of_cards Y 3 eight_aut_card ?_ hfix β
  have hcAut : Nat.card (MulAut Y) = p - 1 := by
    let := isCyclic_of_prime_card (suzuki_eight_sylow_odd_card hp Y)
    rw [IsCyclic.card_mulAut, suzuki_eight_sylow_odd_card hp Y,
      Nat.totient_prime (Fact.out : p.Prime)]
  have hn : Nat.card (normalizer (Y : Set (SuzukiMatrixGroup 1))) = p * ((p - 1)/ 3) :=
    suzuki_eight_sylow_odd_normalizer_card hp Y
  rw [hn, hcAut, suzuki_eight_sylow_odd_card hp Y]
  rcases hp with rfl | rfl <;> norm_num

/-- Every automorphism of a Sylow seven-subgroup extends through its actual inclusion in Sz(8). -/
theorem suzuki_eight_sylow_seven_aut_extend (Y : Sylow 7 (SuzukiMatrixGroup 1)) (β : MulAut Y) :
    ∃ α : MulAut (SuzukiMatrixGroup 1), ∀ y : Y,
      α (y : SuzukiMatrixGroup 1) = (β y : SuzukiMatrixGroup 1) :=
  eight_extension_of_fixers (Or.inl rfl) Y (suzuki_eight_sylow_seven_fixing_inner Y) β


/-- The linear field-twist input removes the field part of every pointwise thirteen-torus fixer. -/
theorem suzuki_eight_sylow_thirteen_fixing_inner_of_twist_separation (hsep : ThirteenTwistSeparation)
    (Y : Sylow 13 (SuzukiMatrixGroup 1))
    (α : MulAut (SuzukiMatrixGroup 1)) (hfix : ∀ y : Y, α y = y) :
    ∃ y : Y, α = MulAut.conj (y : SuzukiMatrixGroup 1) := by
  have hc : Nat.card Y = 13 := suzuki_eight_sylow_odd_card (Or.inr rfl) Y
  let := isCyclic_of_prime_card hc
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := Y)
  have hoy : orderOf y = 13 := (orderOf_eq_card_of_forall_mem_zpowers hy).trans hc
  obtain ⟨g, σ, hα⟩ := suzukiAut_eq_inner_mul_field 1 (by decide) α
  have hσ : σ = 1 := by
    apply hsep y.val.val g.val σ
    · exact (orderOf_injective (SuzukiMatrixSubgroup 1).subtype Subtype.val_injective y.val).trans
        ((orderOf_injective (Y : Subgroup (SuzukiMatrixGroup 1)).subtype Subtype.val_injective y).trans hoy)
    · have he := congrArg Subtype.val (hfix y)
      rw [hα] at he
      change g.val * (suzukiFieldAut 1 σ y).val * g.val⁻¹ = y.val.val at he
      have hfield : (suzukiFieldAut 1 σ y).val =
          Matrix.GeneralLinearGroup.map σ.toRingHom y.val.val := by
        ext i j
        exact suzukiFieldAut_apply_entry 1 σ y i j
      rw [hfield] at he
      exact he
  have he : α = MulAut.conj g := by
    simpa only [hσ, ← suzukiFieldAutHom_apply, map_one, mul_one] using hα
  have hg : g ∈ Y := by
    change g ∈ (Y : Subgroup (SuzukiMatrixGroup 1))
    rw [← suzuki_eight_sylow_odd_centralizer (Or.inr rfl) Y, mem_centralizer_iff]
    intro x hx
    have h := hfix ⟨x, hx⟩
    rw [he] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  exact ⟨⟨g, hg⟩,he⟩

/-- The linear field-twist input supplies all automorphisms of the actual thirteen-torus. -/
theorem suzuki_eight_sylow_thirteen_aut_extend_of_twist_separation (hsep : ThirteenTwistSeparation)
    (Y : Sylow 13 (SuzukiMatrixGroup 1)) (β : MulAut Y) :
    ∃ α : MulAut (SuzukiMatrixGroup 1), ∀ y : Y,
      α (y : SuzukiMatrixGroup 1) = (β y : SuzukiMatrixGroup 1) :=
  eight_extension_of_fixers (Or.inr rfl) Y
    (suzuki_eight_sylow_thirteen_fixing_inner_of_twist_separation hsep Y) β


/-- Combined pointwise-fixer result, conditional only on the named linear input. -/
theorem suzuki_eight_sylow_odd_fixing_inner_of_twist_separation
    (hsep : ThirteenTwistSeparation) {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1))
    (α : MulAut (SuzukiMatrixGroup 1)) (hfix : ∀ y : Y, α y = y) :
    ∃ y : Y, α = MulAut.conj (y : SuzukiMatrixGroup 1) := by
  rcases hp with rfl | rfl
  · exact suzuki_eight_sylow_seven_fixing_inner Y α hfix
  · exact suzuki_eight_sylow_thirteen_fixing_inner_of_twist_separation hsep Y α hfix

/-- Combined extension result through the literal torus inclusion, conditional
only on the named linear input. -/
theorem suzuki_eight_sylow_odd_aut_extend_of_twist_separation
    (hsep : ThirteenTwistSeparation) {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1)) (β : MulAut Y) :
    ∃ α : MulAut (SuzukiMatrixGroup 1), ∀ y : Y,
      α (y : SuzukiMatrixGroup 1) = (β y : SuzukiMatrixGroup 1) :=
  eight_extension_of_fixers hp Y
    (suzuki_eight_sylow_odd_fixing_inner_of_twist_separation hsep hp Y) β

/-- Every pointwise fixer of a Sylow thirteen-subgroup is conjugation by one of its elements. -/
theorem suzuki_eight_sylow_thirteen_fixing_inner (Y : Sylow 13 (SuzukiMatrixGroup 1))
    (α : MulAut (SuzukiMatrixGroup 1)) (hfix : ∀ y : Y, α y = y) :
    ∃ y : Y, α = MulAut.conj (y : SuzukiMatrixGroup 1) :=
  suzuki_eight_sylow_thirteen_fixing_inner_of_twist_separation
    thirteen_twist_separation Y α hfix

/-- Every automorphism of a Sylow thirteen-subgroup extends through its actual inclusion in Sz(8). -/
theorem suzuki_eight_sylow_thirteen_aut_extend (Y : Sylow 13 (SuzukiMatrixGroup 1))
    (β : MulAut Y) : ∃ α : MulAut (SuzukiMatrixGroup 1), ∀ y : Y,
      α (y : SuzukiMatrixGroup 1) = (β y : SuzukiMatrixGroup 1) :=
  suzuki_eight_sylow_thirteen_aut_extend_of_twist_separation
    thirteen_twist_separation Y β

/-- Every pointwise fixer of either odd Sylow subgroup in J.2.10 is inner by a torus element. -/
theorem suzuki_eight_sylow_odd_fixing_inner {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1))
    (α : MulAut (SuzukiMatrixGroup 1)) (hfix : ∀ y : Y, α y = y) :
    ∃ y : Y, α = MulAut.conj (y : SuzukiMatrixGroup 1) :=
  suzuki_eight_sylow_odd_fixing_inner_of_twist_separation
    thirteen_twist_separation hp Y α hfix

/-- Every automorphism of either odd Sylow subgroup in J.2.10 extends through the literal inclusion. -/
theorem suzuki_eight_sylow_odd_aut_extend {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1)) (β : MulAut Y) :
    ∃ α : MulAut (SuzukiMatrixGroup 1), ∀ y : Y,
      α (y : SuzukiMatrixGroup 1) = (β y : SuzukiMatrixGroup 1) :=
  suzuki_eight_sylow_odd_aut_extend_of_twist_separation
    thirteen_twist_separation hp Y β

end BenderSuzuki.MatrixGroups
