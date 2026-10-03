module

public import Theory.GroupAction.FiveFourBinaryModel
public import Theory.GroupAction.FiveOrbitBinaryCoordinates
public import Theory.GroupAction.FiveFourSquareFixed

/-!
# Left coordinates for a faithful five-four action

A faithful action of C₅ ⋊ C₄ on an elementary abelian group of order sixteen
admits the even-subset coordinates of `FiveFourBinaryModel`. The supplied
order-four actor fixes a nonidentity vector. Its five-orbit is a binary basis
with the sole relation that the five orbit points multiply to one. We label
these points by the complements of the five singleton subsets.

Conjugation by the supplied actor has exponent two or three on C₅. Choosing
that actor or its inverse accordingly realizes multiplication by two on orbit
indices, and preserves the square of the supplied actor. Translation by the
canonical generator realizes translation by one on the five underlying points.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
`refs/original/n-group-global/parrott-tits-characterization-1972.pdf`,
printed pp.673–674.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
open FiveFourBinaryModel
private abbrev C5 := Multiplicative (ZMod 5)
private abbrev C4 := Multiplicative (ZMod 4)

private theorem choose_turn
    (φ : C4 →* MulAut C5) (hφ : Function.Injective φ)
    (g : C5 ⋊[φ] C4) (hg : orderOf g = 4) :
    ∃ s : C5 ⋊[φ] C4, (s = g ∨ s = g⁻¹) ∧ s ^ 2 = g ^ 2 ∧
      s * SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 5)) * s⁻¹ =
        (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 5))) ^ 2 := by
  let : Finite (C5 ⋊[φ] C4) := Finite.of_equiv (C5 × C4) SemidirectProduct.equivProd.symm
  let d : C5 := Multiplicative.ofAdd 1
  let t : C5 ⋊[φ] C4 := SemidirectProduct.inl d
  let k : ZMod 5 := (φ g.right d).toAdd
  have hd (x : C5) : d ^ x.toAdd.val = x := by
    change Multiplicative.ofAdd _ = _
    simp [d, nsmul_eq_mul]
  have hk : φ g.right d = d ^ k.val := (hd _).symm
  have hc : g * t * g⁻¹ = t ^ k.val := by
    change g * t * g⁻¹ = SemidirectProduct.inl d ^ k.val
    rw [← map_pow]
    apply SemidirectProduct.ext
    · simpa [t, SemidirectProduct.mul_left, SemidirectProduct.inv_left,
        mul_comm, mul_left_comm, mul_assoc, ← map_pow] using hk
    · simp [t, -map_pow]
  have hg2 : orderOf (g ^ 2) = 2 := by rw [orderOf_pow, hg]; decide
  have hi : g ^ 2 * t * (g ^ 2)⁻¹ = t⁻¹ := by
    simpa [t] using faithful_five_four_involution_inverts_left φ hφ (g ^ 2) hg2 d
  have hkk : t ^ (k.val * k.val) = t⁻¹ := by
    calc
      t ^ (k.val * k.val) = (g * t * g⁻¹) ^ k.val := by rw [hc, pow_mul]
      _ = g * (g * t * g⁻¹) * g⁻¹ := by rw [conj_pow, hc]
      _ = g ^ 2 * t * (g ^ 2)⁻¹ := by simp [pow_two, mul_assoc]
      _ = t⁻¹ := hi
  have hkk' : (k.val * k.val : ℕ) • (1 : ZMod 5) = -1 := by
    have hh := congrArg (fun x : C5 ⋊[φ] C4 => x.left.toAdd) hkk
    simpa [t, d, ← map_pow] using hh
  have hk23 : k = 2 ∨ k = 3 := by
    exact (by decide +kernel : ∀ z : ZMod 5,
      (z.val * z.val) • (1 : ZMod 5) = -1 → z = 2 ∨ z = 3) k hkk'
  have hg4 : g ^ 4 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  rcases hk23 with hk2 | hk3
  · refine ⟨g, Or.inl rfl, rfl, ?_⟩
    simpa [hk2, t, d, ZMod.val_ofNat] using hc
  · refine ⟨g⁻¹, Or.inr rfl, ?_, ?_⟩
    · calc
        (g⁻¹) ^ 2 = (g ^ 2)⁻¹ := inv_pow ..
        _ = g ^ 2 := inv_eq_of_mul_eq_one_left (by simpa [← pow_add] using hg4)
    · have hc3 : g * t * g⁻¹ = t ^ 3 := by simpa [hk3, ZMod.val_ofNat] using hc
      have ht5 : t ^ 5 = 1 := by
        change (SemidirectProduct.inl d) ^ 5 = 1
        rw [← map_pow]
        have hd5 : d ^ 5 = 1 := by decide +kernel
        rw [hd5, map_one]
      have hh : g * t ^ 2 * g⁻¹ = t := by
        rw [← conj_pow, hc3, ← pow_mul]
        calc
          t ^ (3 * 2) = t ^ 5 * t := by rw [← pow_succ]
          _ = t := by rw [ht5, one_mul]
      change g⁻¹ * t * (g⁻¹)⁻¹ = t ^ 2
      calc
        g⁻¹ * t * (g⁻¹)⁻¹ = g⁻¹ * (g * t ^ 2 * g⁻¹) * g := by rw [hh, inv_inv]
        _ = t ^ 2 := by simp [mul_assoc]

private def word {V : Type*} [Group V] (v : Fin 4 → V) (e : Fin 4 → Fin 2) : V :=
  v 0 ^ (e 0).val * v 1 ^ (e 1).val * v 2 ^ (e 2).val * v 3 ^ (e 3).val

private def wordHom {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (v : Fin 4 → V) : Multiplicative (Fin 4 → Fin 2) →* V where
  toFun e := word v e.toAdd
  map_one' := by simp [word]
  map_mul' e f := by
    have hs (x : V) : x * x = 1 := by
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) x
    have hp (i : Fin 4) (a b : Fin 2) :
        v i ^ (a + b).val = v i ^ a.val * v i ^ b.val := by
      fin_cases a <;> fin_cases b <;> simp [hs]
    change word v (e.toAdd + f.toAdd) = word v e.toAdd * word v f.toAdd
    simp only [word, Pi.add_apply, hp]
    ac_rfl

private def modelPoint (i : Fin 5) : Space := Multiplicative.ofAdd
  (fun j : Fin 4 => if j.val = i.val then 0 else 1)

private def modelWord (e : Fin 4 → Fin 2) : Space :=
  word (fun i => modelPoint ⟨i.val, by omega⟩) e

private theorem modelWord_bijective : Function.Bijective modelWord := by decide +kernel

private theorem model_facts :
    (modelPoint 4 = modelPoint 0 * modelPoint 1 * modelPoint 2 * modelPoint 3) ∧
    (∀ i : Fin 5, translate (modelPoint i) = modelPoint (i + 1)) ∧
    (∀ i : Fin 5, turn (modelPoint i) = modelPoint (2 * i)) ∧
    (∀ x y, translate (x * y) = translate x * translate y) ∧
    (∀ x y, turn (x * y) = turn x * turn y) ∧
    translate 1 = 1 ∧ turn 1 = 1 := by decide +kernel

private def translateHom : Space →* Space where
  toFun := translate
  map_one' := model_facts.2.2.2.2.2.1
  map_mul' := model_facts.2.2.2.1

private def turnHom : Space →* Space where
  toFun := turn
  map_one' := model_facts.2.2.2.2.2.2
  map_mul' := model_facts.2.2.2.2.1

private theorem wordHom_single {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (v : Fin 4 → V) (i : Fin 4) :
    wordHom v (Multiplicative.ofAdd (fun j => if j = i then 1 else 0)) = v i := by
  fin_cases i <;> simp [wordHom, word]

private theorem coordinates_from_orbit
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (x : Fin 5 → V)
    (hbij : Function.Bijective (word (fun i : Fin 4 => x ⟨i.val, by omega⟩)))
    (hrel : x 4 = x 0 * x 1 * x 2 * x 3)
    (a c : MulAut V)
    (ha : ∀ i : Fin 5, a (x i) = x (i + 1))
    (hc : ∀ i : Fin 5, c (x i) = x (2 * i)) :
    ∃ left : V ≃* Space,
      (∀ v, left (a v) = translate (left v)) ∧
      (∀ v, left (c v) = turn (left v)) := by
  let ev : Multiplicative (Fin 4 → Fin 2) ≃* V := MulEquiv.ofBijective
    (wordHom (fun i : Fin 4 => x ⟨i.val, by omega⟩)) hbij
  let : IsElementaryAbelian 2 Space := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel) }
  let em : Multiplicative (Fin 4 → Fin 2) ≃* Space := MulEquiv.ofBijective
    (wordHom (fun i : Fin 4 => modelPoint ⟨i.val, by omega⟩)) modelWord_bijective
  let left := ev.symm.trans em
  have hx4 (i : Fin 4) : left (x ⟨i.val, by omega⟩) = modelPoint ⟨i.val, by omega⟩ := by
    have hv := wordHom_single (fun i : Fin 4 => x ⟨i.val, by omega⟩) i
    change ev _ = _ at hv
    rw [← hv]
    change em (ev.symm (ev _)) = _
    rw [ev.symm_apply_apply]
    exact wordHom_single (fun j : Fin 4 => modelPoint ⟨j.val, by omega⟩) i
  have hx (i : Fin 5) : left (x i) = modelPoint i := by
    fin_cases i
    · exact hx4 0
    · exact hx4 1
    · exact hx4 2
    · exact hx4 3
    · change left (x 4) = modelPoint 4
      have h0 : left (x 0) = modelPoint 0 := hx4 0
      have h1 : left (x 1) = modelPoint 1 := hx4 1
      have h2 : left (x 2) = modelPoint 2 := hx4 2
      have h3 : left (x 3) = modelPoint 3 := hx4 3
      rw [hrel, map_mul, map_mul, map_mul, h0, h1, h2, h3]
      exact model_facts.1.symm
  have all_words (p q : V →* Space)
      (heq : ∀ i : Fin 4, p (x ⟨i.val, by omega⟩) = q (x ⟨i.val, by omega⟩)) :
      p = q := by
    ext v
    obtain ⟨e, rfl⟩ := hbij.surjective v
    simp only [word, map_mul, map_pow, heq]
  refine ⟨left, ?_, ?_⟩
  · have hh := all_words (left.toMonoidHom.comp a.toMonoidHom)
      (translateHom.comp left.toMonoidHom) (fun i => by
        change left (a (x _)) = translate (left (x _))
        rw [ha, hx, hx, model_facts.2.1])
    exact fun v => DFunLike.congr_fun hh v
  · have hh := all_words (left.toMonoidHom.comp c.toMonoidHom)
      (turnHom.comp left.toMonoidHom) (fun i => by
        change left (c (x _)) = turn (left (x _))
        rw [hc, hx, hx, model_facts.2.2.1])
    exact fun v => DFunLike.congr_fun hh v

/-- A faithful five-four action on elementary sixteen has the standard binary
coordinates, with a turn actor whose square is the supplied actor's square. -/
public theorem exists_five_four_left_coordinates
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (f : (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) →* MulAut V)
    (hf : Function.Injective f)
    (g : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) (hg : orderOf g = 4) :
    ∃ (left : V ≃* Space) (t s : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)),
      (∀ v, left (f t v) = translate (left v)) ∧
      (∀ v, left (f s v) = turn (left v)) ∧ s ^ 2 = g ^ 2 := by
  classical
  let M := C5 ⋊[φ] C4
  let d : C5 := Multiplicative.ofAdd 1
  let t : M := SemidirectProduct.inl d
  let a := f t
  have hd : orderOf d = 5 := by simp [d, orderOf_ofAdd_eq_addOrderOf]
  have haorder : orderOf a = 5 := by
    rw [orderOf_injective f hf,
      orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective, hd]
  have ha5 : a ^ 5 = 1 := by simpa only [haorder] using pow_orderOf_eq_one a
  obtain ⟨s, hs, hs2, hst⟩ := choose_turn φ hφ g hg
  let c := f s
  have hca : c * a * c⁻¹ = a ^ 2 := by
    simpa only [map_mul, map_inv, map_pow] using congrArg f hst
  let F := FixedPoints.subgroup (zpowers (f g)) V
  have hF : Nat.card F = 2 :=
    (five_four_sixteen_order_four_fixed_cards hV φ hφ f hf g hg).1
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b0, hb0⟩ := exists_ne (1 : F)
  let b : V := b0
  have hb : b ≠ 1 := fun hh => hb0 (Subtype.ext hh)
  have hgb : f g b = b := b0.property ⟨f g, mem_zpowers (f g)⟩
  have hcb : c b = b := by
    rcases hs with rfl | rfl
    · exact hgb
    · change f g⁻¹ b = b
      rw [map_inv]
      exact (f g).injective (by simpa using hgb.symm)
  let : MulDistribMulAction C5 V := MulDistribMulAction.compHom V
    (f.comp (SemidirectProduct.inl : C5 →* M))
  have hC5 : Nat.card C5 = 5 := by change Nat.card (ZMod 5) = 5; simp
  have hfixed : FixedPoints.subgroup C5 V = ⊥ := by
    apply fixed_eq_bot_of_five_action_card_sixteen hC5 hV
    intro htop
    have haone : a = 1 := by
      ext v
      have hv : v ∈ FixedPoints.subgroup C5 V := by rw [htop]; trivial
      exact hv d
    simp [haone] at haorder
  have hdne : d ≠ 1 := by intro hh; simp [hh] at hd
  obtain ⟨hrel, hbij⟩ := five_orbit_binary_coordinates hC5 hV hfixed b hb d hdne
  have hsmul (n : ℕ) : d ^ n • b = (a ^ n) b := by
    change f (SemidirectProduct.inl (d ^ n)) b = (a ^ n) b
    rw [map_pow, map_pow]
  simp only [hsmul] at hbij
  have hrel' : (a ^ 4) b = b * a b * (a ^ 2) b * (a ^ 3) b := by
    simpa only [hsmul, show d • b = a b from rfl] using hrel
  let x : Fin 5 → V := fun i => (a ^ i.val) b
  have hxrel : x 4 = x 0 * x 1 * x 2 * x 3 := by
    simpa [x] using hrel'
  have hxbij : Function.Bijective (word (fun i : Fin 4 => x ⟨i.val, by omega⟩)) := hbij
  have haNat (n : ℕ) : a ((a ^ n) b) = (a ^ (n + 1)) b := by
    rw [pow_succ']
    rfl
  have hat (i : Fin 5) : a (x i) = x (i + 1) := by
    change a ((a ^ i.val) b) = (a ^ (i + 1).val) b
    rw [haNat]
    fin_cases i <;> norm_num [Fin.val_add, ha5]
  have hcNat (n : ℕ) : c ((a ^ n) b) = (a ^ (2 * n)) b := by
    have hh : c * a ^ n = a ^ (2 * n) * c := by
      apply mul_inv_eq_iff_eq_mul.mp
      rw [← conj_pow, hca, ← pow_mul]
    have he := congrArg (fun k : MulAut V => k b) hh
    simpa only [MulAut.mul_apply, hcb] using he
  have hct (i : Fin 5) : c (x i) = x (2 * i) := by
    change c ((a ^ i.val) b) = (a ^ (2 * i).val) b
    rw [hcNat]
    fin_cases i <;> norm_num [Fin.val_mul]
    · rw [show 6 = 5 + 1 from rfl, pow_add, ha5, one_mul, pow_one]
    · rw [show 8 = 5 + 3 from rfl, pow_add, ha5, one_mul]
  obtain ⟨left, ht, hs⟩ := coordinates_from_orbit x hxbij hxrel a c hat hct
  exact ⟨left, t, s, ht, hs, hs2⟩
end Theory.GroupAction
