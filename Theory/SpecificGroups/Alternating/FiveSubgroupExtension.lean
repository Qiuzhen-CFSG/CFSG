module

public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension.Transport
public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension.Generators
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizer

/-!
# Unique extension of A₄ markings across A₅

Every embedding of an order-twelve subgroup of A₅ into A₅ extends to a unique
ambient automorphism. No point-stabilizer identification is assumed.

The normalizer of a cubic subgroup in A₅ has order six. Sylow counting then
forces its normalizer inside an order-twelve subgroup to have order three.
Cauchy's theorem supplies a three-cycle and an involution; the normalizer
calculation excludes the dihedral possibility, leaving an A₄ generating pair.
Its twelve normal forms prove generation. Conjugacy of such pairs extends the
marking, and the trivial S₅ centralizer of the pair, together with Aut(A₅) = S₅,
proves uniqueness. The final theorem discharges the two model obligations in
the normal-supplement transport construction.

Source application: Aschbacher, “A 2-local characterization of M12”,
Proposition 3.3, printed p.38,
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

open Subgroup
namespace AlternatingFiveSubgroupExtension
open Generators
private lemma normalizer_card (S : Subgroup A5) (hS : Nat.card S = 12)
    (x : S) (hx : orderOf x = 3) : Nat.card (normalizer (zpowers x : Set S)) = 3 := by
  let P := zpowers x
  have hP : Nat.card P = 3 := by rw [Nat.card_zpowers, hx]
  have hm : Nat.card (P.map S.subtype) = 3 := by
    rw [card_map_of_injective S.subtype_injective, hP]
  have hn := alternatingGroup.FiveLocalGeometry.cubic_normalizer_card
    (MulEquiv.refl A5) (P.map S.subtype) hm
  have hb := card_le_of_le (P.le_normalizer_map S.subtype)
  rw [card_map_of_injective S.subtype_injective, hn] at hb
  have hlow := card_le_of_le P.le_normalizer
  rw [hP] at hlow
  let Q : Sylow 3 S := Sylow.ofCard P (by rw [hP, hS]; decide +kernel)
  have hs := card_sylow_modEq_one 3 S
  rw [Q.card_eq_index_normalizer] at hs
  change (normalizer (P : Set S)).index % 3 = 1 % 3 at hs
  have hc := (normalizer (P : Set S)).card_mul_index
  rw [hS] at hc
  change Nat.card (normalizer (P : Set S)) = 3
  generalize Nat.card (normalizer (P : Set S)) = n at *
  interval_cases n <;> omega


private abbrev c (g : S5) : MulAut A5 := MulAut.conjNormal g

private lemma exists_pair_conjugate (x y : A5) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy : y ^ 2 = 1) (hy1 : y ≠ 1) (hxy : (x * y) ^ 3 = 1) :
    ∃ e : MulAut A5, e a = x ∧ e b = y := by
  obtain ⟨g, hg⟩ := a_conjugate x hx hx1
  have ha : c g a = x := Subtype.ext hg
  let y' := (c g).symm y
  have hy' : y' ^ 2 = 1 := by
    apply (c g).injective
    simpa only [Subgroup.subtype_apply, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_one, map_pow, map_one, y', MulEquiv.apply_symm_apply] using hy
  have hy'1 : y' ≠ 1 := by
    intro he
    apply hy1
    have he' := congrArg (c g) he
    simpa only [map_one, y', MulEquiv.apply_symm_apply] using he'
  have hxy' : (a * y') ^ 3 = 1 := by
    apply (c g).injective
    simpa only [Subgroup.subtype_apply, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_one, map_pow, map_mul, map_one, ha, y', MulEquiv.apply_symm_apply] using hxy
  obtain ⟨i, j, h₁, h₂⟩ := b_conjugate y' hy' hy'1 hxy'
  let h : S5 := a.val ^ i.val * (Equiv.swap 3 4 : S5) ^ j.val
  have hh₁ : c h a = a := Subtype.ext h₁
  have hh₂ : c h b = y' := Subtype.ext h₂
  refine ⟨c g * c h, ?_, ?_⟩
  · change c g (c h a) = x
    rw [hh₁, ha]
  · change c g (c h b) = y
    rw [hh₂]
    exact (c g).apply_symm_apply y

private lemma product_cube (S : Subgroup A5) (hS : Nat.card S = 12)
    (x y : S) (hx : orderOf x = 3) (hy : orderOf y = 2) : (x * y) ^ 3 = 1 := by
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hx1 : (x : A5) ≠ 1 := by
    intro h
    have h' : x = 1 := Subtype.ext h
    simp [h'] at hx
  have hy1 : (y : A5) ≠ 1 := by
    intro h
    have h' : y = 1 := Subtype.ext h
    simp [h'] at hy
  obtain ⟨g, hg⟩ := a_conjugate x (congrArg S.subtype hx3) hx1
  have ha : c g a = x := Subtype.ext hg
  let y' := (c g).symm (y : A5)
  have hy' : y' ^ 2 = 1 := by
    apply (c g).injective
    simpa only [Subgroup.subtype_apply, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_one, map_pow, map_one, y', MulEquiv.apply_symm_apply] using
      congrArg S.subtype hy2
  have hy'1 : y' ≠ 1 := by
    intro he
    apply hy1
    have he' := congrArg (c g) he
    simpa only [map_one, y', MulEquiv.apply_symm_apply] using he'
  have h12 : (x * y) ^ 12 = 1 := by
    simpa only [hS] using (pow_card_eq_one' (x := x * y))
  have hxy' : (a * y') ^ 12 = 1 := by
    apply (c g).injective
    simpa only [Subgroup.subtype_apply, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_one, map_pow, map_mul, map_one, ha, y', MulEquiv.apply_symm_apply] using
      congrArg S.subtype h12
  rcases product_cases y' hy' hy'1 hxy' with hp | hn
  · apply S.subtype_injective
    have hp' := congrArg (c g) hp
    simpa only [Subgroup.subtype_apply, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_one, map_pow, map_mul, map_one, ha, y', MulEquiv.apply_symm_apply] using hp'
  · have hinv : y * x * y⁻¹ = x⁻¹ := by
      apply S.subtype_injective
      have hn' := congrArg (c g) hn
      simpa only [Subgroup.subtype_apply, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_one, map_mul, map_inv, ha, y', MulEquiv.apply_symm_apply] using hn'
    have hyn : y ∈ normalizer (zpowers x : Set S) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      change zpowers (y * x * y⁻¹) = zpowers x
      rw [hinv, zpowers_inv]
    have hd := (normalizer (zpowers x : Set S)).orderOf_dvd_natCard hyn
    rw [normalizer_card S hS x hx, hy] at hd
    norm_num at hd

private lemma exists_generating_pair (S : Subgroup A5) (hS : Nat.card S = 12) :
    ∃ x y : S, x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
      (x * y) ^ 3 = 1 ∧ Function.Surjective (word x y) := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 (by rw [hS]; decide)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hS]; decide)
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hx1 : x ≠ 1 := by intro h; simp [h] at hx
  have hy1 : y ≠ 1 := by intro h; simp [h] at hy
  have hxy := product_cube S hS x y hx hy
  refine ⟨x, y, hx3, hx1, hy2, hy1, hxy, ?_⟩
  have hx1' : (x : A5) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hy1' : (y : A5) ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨e, he₁, he₂⟩ := exists_pair_conjugate x y (congrArg S.subtype hx3)
    hx1' (congrArg S.subtype hy2) hy1' (congrArg S.subtype hxy)
  have hinj : Function.Injective (word x y) := by
    intro i j hij
    apply word_injective
    apply e.injective
    simp only [map_word, he₁, he₂]
    simpa only [map_word, Subgroup.subtype_apply] using congrArg S.subtype hij
  apply (hinj.bijective_of_nat_card_le ?_).surjective
  simp only [hS, Nat.card_prod, Nat.card_fin]
  norm_num

private lemma pair_rigid (α : MulAut A5) (ha : α a = a) (hb : α b = b) : α = 1 := by
  obtain ⟨g, rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective α
  have ha' : g * a.val * g⁻¹ = a.val := congrArg Subtype.val ha
  have hb' : g * b.val * g⁻¹ = b.val := congrArg Subtype.val hb
  have hg := centralizer_pair g (mul_inv_eq_iff_eq_mul.mp ha')
    (mul_inv_eq_iff_eq_mul.mp hb')
  simp [hg]

private lemma pair_agree (α β : MulAut A5) (ha : α a = β a) (hb : α b = β b) : α = β := by
  have h : β⁻¹ * α = 1 := pair_rigid _ (by
    change β.symm (α a) = a
    rw [ha, β.symm_apply_apply]) (by
    change β.symm (α b) = b
    rw [hb, β.symm_apply_apply])
  exact (inv_mul_eq_one.mp h).symm

/-- Every injective marking of an arbitrary order-twelve subgroup extends to A₅. -/
public theorem markingExtension : MarkingExtension := by
  intro S hS f hf
  obtain ⟨x, y, hx3, hx1, hy2, hy1, hxy, hgen⟩ := exists_generating_pair S hS
  obtain ⟨e, he₁, he₂⟩ := exists_pair_conjugate x y (congrArg S.subtype hx3)
    (fun h => hx1 (Subtype.ext h)) (congrArg S.subtype hy2)
    (fun h => hy1 (Subtype.ext h)) (congrArg S.subtype hxy)
  obtain ⟨d, hd₁, hd₂⟩ := exists_pair_conjugate (f x) (f y)
    (by rw [← map_pow, hx3, map_one]) (fun h => hx1 (hf (h.trans (map_one f).symm)))
    (by rw [← map_pow, hy2, map_one]) (fun h => hy1 (hf (h.trans (map_one f).symm)))
    (by rw [← map_mul, ← map_pow, hxy, map_one])
  refine ⟨e.symm.trans d, ?_⟩
  intro s
  obtain ⟨i, rfl⟩ := hgen s
  change d (e.symm (word (x : A5) (y : A5) i)) = f (word x y i)
  rw [← he₁, ← he₂, ← map_word e]
  rw [e.symm_apply_apply]
  rw [map_word d, map_word f, hd₁, hd₂]

/-- Restriction to any order-twelve subgroup determines an automorphism of A₅. -/
public theorem restrictionFaithful : RestrictionFaithful := by
  intro S hS α β hagree
  obtain ⟨x, y, hx3, hx1, hy2, hy1, hxy, _⟩ := exists_generating_pair S hS
  obtain ⟨e, he₁, he₂⟩ := exists_pair_conjugate x y (congrArg S.subtype hx3)
    (fun h => hx1 (Subtype.ext h)) (congrArg S.subtype hy2)
    (fun h => hy1 (Subtype.ext h)) (congrArg S.subtype hxy)
  apply mul_right_cancel (b := e)
  apply pair_agree
  · change α (e a) = β (e a)
    rw [he₁]
    exact hagree x
  · change α (e b) = β (e b)
    rw [he₂]
    exact hagree y
variable {A B : Type*} [Group A] [Group B]

/-- The actual normal-supplement extension, with both A₅ model obligations discharged.
The intersection, generation, and prescribed local map are exactly those of the
transport theorem. -/
public theorem exists_equiv_normal_supplement_of_models
    (N M : Subgroup A) [N.Normal] (R : Subgroup B) [R.Normal]
    (eN : N ≃* A5) (eR : R ≃* A5) (v : M →* B) (hv : Function.Injective v)
    (hgen : N ⊔ M = ⊤) (hgen' : R ⊔ v.range = ⊤)
    (hinter : ∀ m : M, v m ∈ R ↔ (m : A) ∈ N)
    (hcard : Nat.card (M.subgroupOf N) = 12) :
    ∃ E : A ≃* B, ∀ m : M, E m = v m :=
  exists_equiv_normal_supplement markingExtension restrictionFaithful
    N M R eN eR v hv hgen hgen' hinter hcard

end AlternatingFiveSubgroupExtension
