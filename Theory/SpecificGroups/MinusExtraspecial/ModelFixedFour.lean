module

public import Theory.SpecificGroups.MinusExtraspecial.ModelFixedFourCalculation
public import Theory.ElementaryAbelian.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Fixed four and corrected square root for the minus extraspecial model

An outer involution which is an inner twist of an automorphism square fixes an
elementary abelian group of order four. The original automorphism can itself
be twisted by an inner automorphism to square to that involution.

We identify the model with five-bit coordinates, use `aut_word` to determine
automorphisms from their four generator images, and transfer the kernel-checked
certificate in `ModelFixedFourCalculation`. Removing the central bit of the
conjugating element leaves its inner automorphism unchanged. The calculation
actually does not require the stated two-power-order hypothesis.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.389–390,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace MinusExtraspecial.FixedFourCalculation

def decode (x : B) : Model :=
  ⟨if x[2] then .xa ((x.toNat % 4 : ℕ) : ZMod 4) else .a ((x.toNat % 4 : ℕ) : ZMod 4), x[3], x[4]⟩
def encode (x : Model) : B :=
  (match x.q with | .a i => BitVec.ofNat 5 i.val | .xa i => BitVec.ofNat 5 (i.val + 4)) +
    (if x.r then 8 else 0) + (if x.s then 16 else 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decode_encode : ∀ x, decode (encode x) = x := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encode_decode : ∀ x, encode (decode x) = x := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decode_mul : ∀ x y, decode (mul x y) = decode x * decode y := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decode_inv : ∀ x, decode (inv x) = (decode x)⁻¹ := by decide +kernel
theorem decode_zero : decode 0 = 1 := rfl

def equiv : B ≃ Model := ⟨decode, encode, encode_decode, decode_encode⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decode_conj : ∀ x y : B, decode (conj x y) = MulAut.conj (decode x) (decode y) := by
  decide +kernel

theorem decomposition : ∀ x : B, decode x =
    (if x[2] then generators 1 else 1) *
    (if x[1] then generators 0 * generators 0 else 1) *
    (if x[0] then generators 0 else 1) *
    (if x[3] then generators 2 else 1) *
    (if x[4] then generators 3 else 1) := by decide +kernel

theorem decode_word (b : MulAut Model) (x : B) :
    decode (word (encode (b (generators 0))) (encode (b (generators 1)))
      (encode (b (generators 2))) (encode (b (generators 3))) x) = b (decode x) := by
  conv_rhs => rw [decomposition x]
  simp only [word, decode_mul, apply_ite decode, decode_encode, decode_zero,
    map_mul, apply_ite b, map_one]


theorem decode_act (b : MulAut Model) (p : B) (x : B) :
    decode (act (encode (b (generators 0))) (encode (b (generators 1)))
      (encode (b (generators 2))) (encode (b (generators 3))) p x) =
      (MulAut.conj (decode p) * b ^ 2) (decode x) := by
  simp only [act, decode_conj, decode_word, pow_two, MulAut.mul_apply]

theorem aut_ext (a b : MulAut Model) (h : ∀ i, a (generators i) = b (generators i)) : a = b := by
  apply DFunLike.ext
  intro x
  rw [← aut_word a x, ← aut_word b x]
  exact congrArg (fun f => MinusExtraspecial.word f x) (funext h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inner_signs : ∀ t : Fin 4 → Bool, ∃ x : Model, ∀ i : Fin 4,
    MulAut.conj x (generators i) = if t i then decode 2 * generators i else generators i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask_sign : ∀ x g : B, (x ^^^ g) &&& 29 = 0 →
    ∃ t : Bool, decode x = if t then decode 2 * decode g else decode g := by decide +kernel

theorem mem_all : ∀ x : B, x ∈ all := by decide +kernel
theorem gens_mem : ∀ i : Fin 4, encode (generators i) ∈ gens := by decide +kernel

theorem sum_boole (l : List B) (f : B → Bool) :
    (l.map fun x => if f x then (1 : BitVec 6) else 0).sum =
      BitVec.ofNat 6 (l.countP f) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    cases h : f x <;> simp [h, BitVec.ofNat_add, add_comm]

theorem count_eq_card (f : B → B) :
    ((all.map fun x => if f x == x then (1 : BitVec 6) else 0).sum = 4) →
      Fintype.card {x : B // f x = x} = 4 := by
  intro h
  rw [sum_boole] at h
  have hle := List.countP_le_length (p := fun x => f x == x) (l := all)
  have hlen : all.length = 32 := by decide
  rw [hlen] at hle
  have hn := congrArg BitVec.toNat h
  change all.countP (fun x => f x == x) % 64 = 4 at hn
  have hc : all.countP (fun x => f x == x) = 4 := by omega
  have hall : all.toFinset = Finset.univ := by decide +kernel
  have hnodup : all.Nodup := by decide +kernel
  rw [Fintype.card_subtype, ← hall, hnodup.card_eq_countP]
  simpa only [Bool.beq_eq_decide_eq] using hc


theorem relations_aut (b : MulAut Model) :
    relations (encode (b (generators 0))) (encode (b (generators 1)))
      (encode (b (generators 2))) (encode (b (generators 3))) := by
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
    ne_eq, ← equiv.injective.eq_iff]
  dsimp only [equiv]
  simp only [Equiv.coe_fn_mk, decode_mul, decode_inv, decode_encode, decode_zero, ← map_mul, ← map_inv,
    b.injective.eq_iff, b.map_eq_one_iff]
  decide

theorem invol_aut (b : MulAut Model) (p : B)
    (ha : (MulAut.conj (decode p) * b ^ 2) ^ 2 = 1) :
    invol (encode (b (generators 0))) (encode (b (generators 1)))
      (encode (b (generators 2))) (encode (b (generators 3))) p := by
  apply List.all_eq_true.mpr
  intro g _
  apply beq_iff_eq.mpr
  apply equiv.injective
  change decode (act _ _ _ _ p (act _ _ _ _ p g)) = decode g
  rw [decode_act, decode_act]
  have h := congrArg (fun c : MulAut Model => c (decode g)) ha
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h

theorem outer_aut (b : MulAut Model) (p : B)
    (hout : ¬ ∃ x : Model, MulAut.conj (decode p) * b ^ 2 = MulAut.conj x) :
    outer (encode (b (generators 0))) (encode (b (generators 1)))
      (encode (b (generators 2))) (encode (b (generators 3))) p := by
  by_contra hn
  have hz := List.any_eq_false.mp (Bool.eq_false_iff.mpr hn)
  have hs : ∀ i : Fin 4, ∃ t : Bool,
      (MulAut.conj (decode p) * b ^ 2) (generators i) =
        if t then decode 2 * generators i else generators i := by
    intro i
    have hm := hz (encode (generators i)) (gens_mem i)
    have hm' : (act (encode (b (generators 0))) (encode (b (generators 1)))
        (encode (b (generators 2))) (encode (b (generators 3))) p
          (encode (generators i)) ^^^ encode (generators i)) &&& 29 = 0 := by
      simpa only [bne_iff_ne, not_not] using hm
    obtain ⟨t, ht⟩ := mask_sign _ _ hm'
    refine ⟨t, ?_⟩
    simpa only [decode_act, decode_encode] using ht
  choose t ht using hs
  obtain ⟨x, hx⟩ := inner_signs t
  exact hout ⟨x, aut_ext _ _ (fun i => (ht i).trans (hx i).symm)⟩


theorem finish (b : MulAut Model) (p : B)
    (hc :
      (all.all fun y => act (encode (b (generators 0))) (encode (b (generators 1)))
        (encode (b (generators 2))) (encode (b (generators 3))) p y != y || mul y y == 0) ∧
      count (encode (b (generators 0))) (encode (b (generators 1)))
        (encode (b (generators 2))) (encode (b (generators 3))) p = 4 ∧
      root (encode (b (generators 0))) (encode (b (generators 1)))
        (encode (b (generators 2))) (encode (b (generators 3))) p) :
    let a := MulAut.conj (decode p) * b ^ 2
    IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id Model)) ∧
    Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id Model)) = 4 ∧
    ∃ x : Model, (MulAut.conj x * b) ^ 2 = a := by
  let a := MulAut.conj (decode p) * b ^ 2
  let F := a.toMonoidHom.eqLocus (MonoidHom.id Model)
  let f := act (encode (b (generators 0))) (encode (b (generators 1)))
    (encode (b (generators 2))) (encode (b (generators 3))) p
  have hf (x : B) : decode (f x) = a (decode x) := decode_act b p x
  have hs : ∀ y : F, y ^ 2 = 1 := by
    intro y
    have hy : f (encode y.val) = encode y.val := by
      apply equiv.injective
      change decode (f (encode y.val)) = decode (encode y.val)
      rw [hf, decode_encode]
      exact y.property
    have h := List.all_eq_true.mp hc.1 (encode y.val) (mem_all _)
    change (f (encode y.val) != encode y.val || mul (encode y.val) (encode y.val) == 0) = true at h
    rw [hy] at h
    have hm : mul (encode y.val) (encode y.val) = 0 := by simpa using h
    apply Subtype.ext
    have hd := congrArg decode hm
    simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, pow_two, decode_mul, decode_encode, decode_zero] using hd
  have he : IsElementaryAbelian 2 F :=
    { toIsMulCommutative := ⟨⟨fun x y =>
        (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hs z)) x y).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  let e : {x : B // f x = x} ≃ F := Equiv.subtypeEquiv equiv (fun x => by
    change f x = x ↔ a (decode x) = decode x
    rw [← hf]
    exact equiv.injective.eq_iff.symm)
  have hcard : Nat.card F = 4 := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
    exact count_eq_card f hc.2.1
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp hc.2.2
  refine ⟨he, hcard, decode x, aut_ext _ _ ?_⟩
  intro i
  have hi := List.all_eq_true.mp hx (encode (generators i)) (gens_mem i)
  have hd := congrArg decode (beq_iff_eq.mp hi)
  simpa only [decode_conj, decode_word, decode_act, decode_encode,
    pow_two, MulAut.mul_apply] using hd

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem normalized_bit : ∀ p : B, (p &&& 29)[1] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem conj_normalized : ∀ p x : B, conj (p &&& 29) x = conj p x := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem conj_mask : ∀ p x g : B,
    (conj p x ^^^ g) &&& 29 = (x ^^^ g) &&& 29 := by decide +kernel

theorem outer_zero (u v r s p : B) : outer u v r s p = outer u v r s 0 := by
  simp only [outer, act, conj_mask]

theorem normalized_inner (p : B) :
    MulAut.conj (decode (p &&& 29)) = MulAut.conj (decode p) := by
  apply DFunLike.ext
  intro x
  obtain ⟨y, rfl⟩ := equiv.surjective x
  change MulAut.conj (decode (p &&& 29)) (decode y) = MulAut.conj (decode p) (decode y)
  rw [← decode_conj, ← decode_conj, conj_normalized]

theorem assembly (hcalc : ∀ u : B, calculation u)
    (a b : MulAut Model) (p : Model)
    (hab : a = MulAut.conj p * b ^ 2) (ha : a ^ 2 = 1)
    (hout : ¬ ∃ x, a = MulAut.conj x) :
    IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id Model)) ∧
    Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id Model)) = 4 ∧
    ∃ x : Model, (MulAut.conj x * b) ^ 2 = a := by
  let p' := encode p &&& 29
  have hp : MulAut.conj (decode p') = MulAut.conj p := by
    rw [normalized_inner, decode_encode]
  have ha' : (MulAut.conj (decode p') * b ^ 2) ^ 2 = 1 := by rw [hp, ← hab, ha]
  have hout' : ¬ ∃ x, MulAut.conj (decode p') * b ^ 2 = MulAut.conj x := by
    rwa [hp, ← hab]
  have hr := relations_aut b
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
  have ho := outer_aut b p' hout'
  rw [outer_zero] at ho
  have hi := invol_aut b p' ha'
  have hc := hcalc (encode (b (generators 0)))
  unfold calculation at hc
  have hc' := hc h1 _ h2 h3 _ h4 h5 h6 _ h7 h8 h9 h10 ho p' (normalized_bit _) hi
  have heq : MulAut.conj (decode p') * b ^ 2 = a := by rw [hp, ← hab]
  exact heq ▸ finish b p' hc'
end MinusExtraspecial.FixedFourCalculation

namespace MinusExtraspecial

/-- An outer involution given by an inner twist of a square fixes an elementary
four and has a square root in the prescribed coset of inner automorphisms. -/
public theorem square_action_fixed_four (a b : MulAut Model) (p : Model) (n : ℕ)
    (_hb : b ^ (2 ^ n) = 1) (hab : a = MulAut.conj p * b ^ 2)
    (ha : a ^ 2 = 1) (hout : ¬ ∃ x : Model, a = MulAut.conj x) :
    IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id Model)) ∧
    Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id Model)) = 4 ∧
    ∃ x : Model, (MulAut.conj x * b) ^ 2 = a :=
  FixedFourCalculation.assembly FixedFourCalculation.calculation_all a b p hab ha hout

end MinusExtraspecial
