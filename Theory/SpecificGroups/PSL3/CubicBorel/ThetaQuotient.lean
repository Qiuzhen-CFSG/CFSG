module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# The cubic subgroup of a projective Borel modulo its two-core

For even n prime to three, the three-part of 2ⁿ − 1 is exactly three.
Consequently every cubic element of the projective diagonal torus lifts to
cubic diagonal parameters: a lift has ninth-power-one parameters, which
already have cube one. The two groups of cube roots have product order nine;
the diagonal scalar kernel has order three. Their projective image therefore
has order three.

The Borel quotient map sends the closure of its exact order-three elements
onto this cubic torus subgroup. Its restricted kernel is a two-group and has
index three, so it is exactly the two-core of that closure. The actual Borel
isomorphism at any specified Sylow subgroup transports both the quotient map
and its cubic diagonal lifts. No restriction to the four-element field is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.38, printed pp.1135--1136. The parameter condition is explicit here;
its deduction from the source's local hypotheses belongs to the consumer.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.CartanActions.BorelQuotient

namespace Matrix.PSL3.CubicBorel.ThetaQuotient

private theorem gcd_nine {n : ℕ} (he : Even n) (hn : ¬ 3 ∣ n) : Nat.gcd (2 ^ n - 1) 9 = 3 := by
  have hm : n % 6 = 2 ∨ n % 6 = 4 := by
    have he' := he.two_dvd
    rw [Nat.dvd_iff_mod_eq_zero] at he' hn
    omega
  have hp : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    conv_lhs => rw [← Nat.mod_add_div n 6, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  rcases hm with hm | hm <;> rw [hm] at hp <;> norm_num at hp
  · have hs : (2 ^ n - 1) % 9 = 3 := by omega
    rw [Nat.gcd_comm, Nat.gcd_rec, hs]
    norm_num
  · have hs : (2 ^ n - 1) % 9 = 6 := by omega
    rw [Nat.gcd_comm, Nat.gcd_rec, hs]
    norm_num

section Torus
variable (F : Type*) [Field F] [Finite F]

private abbrev R := (powMonoidHom 3 : Fˣ →* Fˣ).ker
private abbrev Q := (Fˣ × Fˣ) ⧸ cubicScalars F

private def cubicMap : (R F × R F) →* Q F :=
  (QuotientGroup.mk' (cubicScalars F)).comp ((R F).subtype.prodMap (R F).subtype)

private def cubicMapKerEquiv : (cubicMap F).ker ≃* R F where
  toFun x := x.val.1
  invFun a := ⟨(a,a), (QuotientGroup.eq_one_iff _).mpr ⟨rfl, a.property⟩⟩
  left_inv x := by
    have hx : (x.val.1.val, x.val.2.val) ∈ cubicScalars F :=
      (QuotientGroup.eq_one_iff _).mp x.property
    apply Subtype.ext
    exact Prod.ext rfl (Subtype.ext hx.1)
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite F] in
private theorem ninth_root_cubic {n : ℕ} (he : Even n) (hn : ¬ 3 ∣ n)
    (hF : Nat.card F = 2 ^ n) (a : Fˣ) (ha : a ^ 9 = 1) : a ^ 3 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  have hd := Nat.dvd_gcd (orderOf_dvd_natCard a) (orderOf_dvd_of_pow_eq_one ha)
  rwa [Nat.card_units, hF, gcd_nine he hn] at hd

private theorem cubic_lift {n : ℕ} (he : Even n) (hn : ¬ 3 ∣ n)
    (hF : Nat.card F = 2 ^ n) (x : Q F) (hx : x ^ 3 = 1) :
    ∃ a b : R F, cubicMap F (a,b) = x := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (cubicScalars F) x
  have hd : d ^ 3 ∈ cubicScalars F :=
    (QuotientGroup.eq_one_iff _).mp (by
      change QuotientGroup.mk' (cubicScalars F) (d ^ 3) = 1
      rw [map_pow]
      exact hx)
  have ha9 : d.1 ^ 9 = 1 := by
    have hh : (d.1 ^ 3) ^ 3 = 1 := hd.2
    simpa only [← pow_mul] using hh
  have hb9 : d.2 ^ 9 = 1 := by
    have hh := hd.2
    rw [hd.1] at hh
    change (d.2 ^ 3) ^ 3 = 1 at hh
    simpa only [← pow_mul] using hh
  exact ⟨⟨d.1, ninth_root_cubic F he hn hF _ ha9⟩,
    ⟨d.2, ninth_root_cubic F he hn hF _ hb9⟩, rfl⟩

private theorem cubic_range {n : ℕ} (he : Even n) (hn : ¬ 3 ∣ n)
    (hF : Nat.card F = 2 ^ n) :
    (cubicMap F).range = (powMonoidHom (α := Q F) 3).ker := by
  apply le_antisymm
  · rintro _ ⟨⟨a,b⟩,rfl⟩
    change cubicMap F (a,b) ^ 3 = 1
    rw [← map_pow]
    have hab : (a,b) ^ 3 = 1 := Prod.ext (Subtype.ext a.property) (Subtype.ext b.property)
    rw [hab, map_one]
  · intro x hx
    obtain ⟨a,b,hab⟩ := cubic_lift F he hn hF x hx
    exact ⟨(a,b),hab⟩

/-- The cube-one subgroup of the actual scalar quotient of the diagonal torus
has order three when the binary field degree is even and prime to three. -/
theorem card_cubic_torus {n : ℕ} (he : Even n) (hn : ¬ 3 ∣ n)
    (hF : Nat.card F = 2 ^ n) :
    Nat.card (powMonoidHom (α := (Fˣ × Fˣ) ⧸ cubicScalars F) 3).ker = 3 := by
  change Nat.card (powMonoidHom (α := Q F) 3).ker = 3
  have hg : Nat.gcd (Nat.card F - 1) 9 = 3 := by rw [hF, gcd_nine he hn]
  have hthree : 3 ∣ Nat.card F - 1 := hg ▸ Nat.gcd_dvd_left (Nat.card F - 1) 9
  have hR : Nat.card (R F) = 3 := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_units, Nat.gcd_eq_right hthree]
  have hh := (cubicMap F).ker.card_mul_index
  rw [index_ker, cubic_range F he hn hF, Nat.card_prod,
    Nat.card_congr (cubicMapKerEquiv F).toEquiv, hR] at hh
  omega
end Torus

section Abstract
variable {G T : Type*} [Group G] [CommGroup T]

private theorem cubic_mem_closure (B : Subgroup G) (z : G) (hz : z ∈ B)
    (h3 : z ^ 3 = 1) : z ∈ closure {z | z ∈ B ∧ orderOf z = 3} := by
  by_cases h : z = 1
  · subst z; exact one_mem _
  · have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact subset_closure ⟨hz, orderOf_eq_prime h3 h⟩

private theorem card_cubicClosure_quotient
    (B : Subgroup G) (f : B →* T) (hk : IsPGroup 2 f.ker)
    (hcard : Nat.card (powMonoidHom (α := T) 3).ker = 3)
    (hlift : ∀ x : T, x ^ 3 = 1 → ∃ b : B, b ^ 3 = 1 ∧ f b = x) :
    Nat.card ((closure {z : G | z ∈ B ∧ orderOf z = 3}) ⧸
      pCore 2 (closure {z : G | z ∈ B ∧ orderOf z = 3})) = 3 := by
  let C := closure {z : G | z ∈ B ∧ orderOf z = 3}
  let K := (powMonoidHom (α := T) 3).ker
  have hCB : C ≤ B := (closure_le _).mpr (fun _ h => h.1)
  let i : C →* B := inclusion hCB
  let g : C →* T := f.comp i
  have hCK : C ≤ (K.comap f).map B.subtype := by
    apply (closure_le _).mpr
    intro z hz
    refine ⟨⟨z,hz.1⟩, ?_, rfl⟩
    change (f ⟨z,hz.1⟩) ^ 3 = 1
    rw [← map_pow]
    have hb : (⟨z,hz.1⟩ : B) ^ 3 = 1 := Subtype.ext (by
      change z ^ 3 = 1
      simpa only [hz.2] using pow_orderOf_eq_one z)
    rw [hb, map_one]
  have hrange : g.range = K := by
    apply le_antisymm
    · rintro _ ⟨z,rfl⟩
      obtain ⟨b,hb,hbz⟩ := hCK z.property
      have he : b = i z := Subtype.ext hbz
      change f b ∈ K at hb
      change f (i z) ∈ K
      rwa [he] at hb
    · intro x hx
      obtain ⟨b,hb,hbx⟩ := hlift x hx
      have hbC : b.val ∈ C := cubic_mem_closure B b.val b.property
        (congrArg Subtype.val hb)
      exact ⟨⟨b.val,hbC⟩,hbx⟩
  have hgk : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.ker.comap i)
    exact hk.comap_of_injective i (inclusion_injective hCB)
  have hi : ¬ 2 ∣ g.ker.index := by
    rw [index_ker, hrange, hcard]
    decide
  have hcore : pCore 2 C = g.ker :=
    le_antisymm (pCore_isPGroup.le_sylow_of_normal (hgk.toSylow hi))
      (le_sSup ⟨inferInstance, hgk⟩)
  change Nat.card (C ⧸ pCore 2 C) = 3
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcore).toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hcard]
end Abstract

variable (F : Type*) [Field F] [Finite F]

/-- The subgroup generated by the exact order-three elements of any Sylow
normalizer in PSL₃(2ⁿ) has quotient of order three by its own two-core.
The degree remains arbitrary, subject to positivity, evenness and `¬ 3 ∣ n`. -/
theorem card_cubicNormalizer_quotient {n : ℕ} (hn : 0 < n) (he : Even n)
    (hF : Nat.card F = 2 ^ n) (hn3 : ¬ 3 ∣ n) (P : Sylow 2 PSL(3,F)) :
    Nat.card ((closure {z : PSL(3,F) | z ∈ normalizer (P : Set PSL(3,F)) ∧ orderOf z = 3}) ⧸
      pCore 2 (closure {z : PSL(3,F) | z ∈ normalizer (P : Set PSL(3,F)) ∧ orderOf z = 3})) = 3 := by
  let B := normalizer (P : Set PSL(3,F))
  let e := sylowNormalizerEquiv F hn hF P
  let q := (quotientTorusEquiv F hF).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (borel F)))
  let f : B →* Q F := q.comp e.toMonoidHom
  have hk : f.ker = (pCore 2 (borel F)).comap e.toMonoidHom := by
    ext x
    change quotientTorusEquiv F hF (QuotientGroup.mk (e x)) = 1 ↔ e x ∈ pCore 2 (borel F)
    rw [← (quotientTorusEquiv F hF).map_one,
      (quotientTorusEquiv F hF).injective.eq_iff, QuotientGroup.eq_one_iff]
  apply card_cubicClosure_quotient (T := Q F) B f
  · rw [hk]
    exact pCore_isPGroup.comap_of_injective e.toMonoidHom e.injective
  · exact card_cubic_torus F he hn3 hF
  · intro x hx
    obtain ⟨a,b,hab⟩ := cubic_lift F he hn3 hF x hx
    let d : Fˣ × Fˣ := (a.val,b.val)
    let t : borel F := ⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩
    have hd : d ^ 3 = 1 := Prod.ext a.property b.property
    have ht : t ^ 3 = 1 := by
      apply Subtype.ext
      change torusMap F d ^ 3 = 1
      rw [← map_pow, hd, map_one]
    refine ⟨e.symm t, ?_, ?_⟩
    · rw [← map_pow, ht, map_one]
    · change quotientTorusEquiv F hF (QuotientGroup.mk (e (e.symm t))) = x
      rw [e.apply_symm_apply, quotientTorusEquiv_mk_torus]
      exact hab
end Matrix.PSL3.CubicBorel.ThetaQuotient
