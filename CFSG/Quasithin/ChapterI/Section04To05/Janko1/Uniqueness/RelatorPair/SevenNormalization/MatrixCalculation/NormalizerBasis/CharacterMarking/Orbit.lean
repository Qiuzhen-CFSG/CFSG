module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Labeling a seven-cycle compatible with a cubic action

An automorphism of order seven on an eight-element group cycles through all
nonidentity elements. A cubic automorphism has a nonidentity fixed point.
Starting this point at index 4 gives the source column permutations `i ↦ i−1`
and `i ↦ 2i+3`. Reversing the seven-cycle changes indices by `i ↦ 1−i`.

The final finite calculation uses the cubic orbits `{4}`, `{0,2,3}`, and
`{1,5,6}`. A cubic-invariant subset of size three consists of exactly one of
the triples. This is the character-labeling step in Gorenstein, *Finite Groups*,
§16.6, pp.482–483; it is independent of the seven-dimensional representation.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation.CharacterMarking

variable {W : Type*} [Group W]

private theorem seven_cycle [Finite W] (hW : Nat.card W = 8) (Y : MulAut W)
    (hY : Y ^ 7 = 1) (hnY : Y ≠ 1) :
    (MulAut.toPerm W Y).IsCycle ∧ ∀ w : W, w ≠ 1 → Y w ≠ w := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hy : (MulAut.toPerm W Y) ^ 7 = 1 := by
    rw [← map_pow, hY, map_one]
  have hne : (MulAut.toPerm W Y) ≠ 1 := fun he => hnY (MulEquiv.toEquiv_injective he)
  have ho : orderOf (MulAut.toPerm W Y) = 7 := orderOf_eq_prime hy hne
  have hc : (MulAut.toPerm W Y).IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [ho]; decide) (by rw [← Nat.card_eq_fintype_card, hW, ho]; decide)
  refine ⟨hc, ?_⟩
  have hs : (MulAut.toPerm W Y).support = ({1} : Finset W)ᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_compl, Finset.mem_singleton]
      intro he
      subst w
      exact (Equiv.Perm.mem_support.mp hw) (map_one Y)
    · rw [Finset.card_compl, Finset.card_singleton, ← Nat.card_eq_fintype_card,
        hW, ← hc.orderOf, ho]
  intro w hw
  exact Equiv.Perm.mem_support.mp (hs ▸ (by simpa using hw))

/-- The cubic action on seven nonidentity elements has a fixed point. -/
public theorem cubic_fixed [Finite W] (hW : Nat.card W = 8) (U : MulAut W) (hU : U ^ 3 = 1) :
    ∃ w : W, w ≠ 1 ∧ U w = w := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let up : Equiv.Perm {w : W // w ≠ 1} :=
    (MulAut.toPerm W U).subtypePerm (fun w => not_congr U.map_eq_one_iff)
  have hc : Fintype.card {w : W // w ≠ 1} = 7 := by
    rw [Fintype.card_subtype_compl, show Fintype.card {v : W // v = 1} = 1 from Fintype.card_unique, ← Nat.card_eq_fintype_card, hW]
  have hp : up ^ 3 = 1 := by
    apply Equiv.ext
    intro w
    apply Subtype.ext
    change (U ^ 3) w.val = w.val
    rw [hU]
    rfl
  obtain ⟨w, hw⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (by rw [hc]; decide) (by simpa using hp)
  exact ⟨w.val, w.property, congrArg Subtype.val hw⟩

/-- The source column labeling, anchored at its cubic-fixed index 4. -/
public def orbitLabel (Y : MulAut W) (w : W) : Fin 7 → W :=
  ![(Y ^ 4) w, (Y ^ 3) w, (Y ^ 2) w, Y w, w, (Y ^ 6) w, (Y ^ 5) w]

private theorem orbitLabel_eq (Y : MulAut W) (w : W) (i : Fin 7) :
    orbitLabel Y w i = (Y ^ ((4 - i : Fin 7).val)) w := by
  fin_cases i <;> rfl

public theorem orbitLabel_y (Y : MulAut W) (hY : Y ^ 7 = 1) (w : W) (i : Fin 7) :
    orbitLabel Y w (i - 1) = Y (orbitLabel Y w i) := by
  fin_cases i <;> dsimp [orbitLabel] <;>
    simp only [← MulAut.mul_apply, ← pow_succ', hY, MulAut.one_apply, ← pow_two]

public theorem orbitLabel_u (Y U : MulAut W) (hY : Y ^ 7 = 1)
    (hUY : U * Y = Y ^ 2 * U) (w : W) (hw : U w = w) (i : Fin 7) :
    orbitLabel Y w (2 * i + 3) = U (orbitLabel Y w i) := by
  have hpow (n : ℕ) : U * Y ^ n = Y ^ (2 * n) * U := by
    simpa only [← pow_mul] using ((show SemiconjBy U Y (Y ^ 2) from hUY).pow_right n).eq
  have happ (n : ℕ) : U ((Y ^ n) w) = (Y ^ (2 * n)) w := by
    rw [← MulAut.mul_apply, hpow, MulAut.mul_apply, hw]
  have h8 : Y ^ 8 = Y := by rw [show 8 = 7 + 1 from rfl, pow_add, hY]; simp
  have h10 : Y ^ 10 = Y ^ 3 := by rw [show 10 = 7 + 3 from rfl, pow_add, hY, one_mul]
  have h12 : Y ^ 12 = Y ^ 5 := by rw [show 12 = 7 + 5 from rfl, pow_add, hY, one_mul]
  fin_cases i <;> dsimp [orbitLabel] <;> try simp only [happ, hw, h8, h10, h12]
  · change (Y ^ 2) w = U (Y w)
    simpa using (happ 1).symm

public theorem orbitLabel_nontrivial (Y : MulAut W) {w : W} (hw : w ≠ 1) (i : Fin 7) :
    orbitLabel Y w i ≠ 1 := by
  rw [orbitLabel_eq]
  exact fun he => hw ((Y ^ _).map_eq_one_iff.mp he)

public theorem orbitLabel_injective [Finite W] (hW : Nat.card W = 8) (Y : MulAut W)
    (hY : Y ^ 7 = 1) (hnY : Y ≠ 1) {w : W} (hw : w ≠ 1) :
    Function.Injective (orbitLabel Y w) := by
  obtain ⟨hc, hm⟩ := seven_cycle hW Y hY hnY
  have ho : orderOf (MulAut.toPerm W Y) = 7 := by
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    apply orderOf_eq_prime
    · rw [← map_pow, hY, map_one]
    · exact fun he => hnY (MulEquiv.toEquiv_injective he)
  have hp (n : ℕ) : ((MulAut.toPerm W Y) ^ n) w = (Y ^ n) w := by
    rw [← map_pow]
    rfl
  intro i j hij
  have he : (MulAut.toPerm W Y) ^ (4 - i : Fin 7).val = (MulAut.toPerm W Y) ^ (4 - j : Fin 7).val :=
    hc.pow_eq_pow_iff.mpr ⟨w, hm w hw, by
      rw [hp, hp]
      simpa only [orbitLabel_eq] using hij⟩
  have hv := pow_injOn_Iio_orderOf (by simpa only [Set.mem_Iio, ho] using (4 - i : Fin 7).isLt)
    (by simpa only [Set.mem_Iio, ho] using (4 - j : Fin 7).isLt) he
  have hf : (4 - i : Fin 7) = 4 - j := Fin.ext hv
  exact sub_right_injective hf

public theorem orbitLabel_exhaustive [Finite W] (hW : Nat.card W = 8) (Y : MulAut W)
    (hY : Y ^ 7 = 1) (hnY : Y ≠ 1) {w : W} (hw : w ≠ 1) :
    ∀ v : W, v ≠ 1 → ∃ i, orbitLabel Y w i = v := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let f : Fin 7 → {v : W // v ≠ 1} := fun i => ⟨orbitLabel Y w i, orbitLabel_nontrivial Y hw i⟩
  have hb : Function.Bijective f := by
    apply (Nat.bijective_iff_injective_and_card f).mpr
    refine ⟨fun i j he => orbitLabel_injective hW Y hY hnY hw (congrArg Subtype.val he), ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl,
      show Fintype.card {v : W // v = 1} = 1 from Fintype.card_unique, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, hW]
  intro v hv
  obtain ⟨i, hi⟩ := hb.surjective ⟨v, hv⟩
  exact ⟨i, congrArg Subtype.val hi⟩

/-- Relabeling by `i ↦ 1−i` reverses the seven-action, pointwise. -/
public theorem reflected_y (Y : MulAut W) (f : Fin 7 → W)
    (hf : ∀ i, f (i - 1) = Y (f i)) (i : Fin 7) :
    f (1 - (i - 1)) = Y⁻¹ (f (1 - i)) := by
  apply Y.injective
  rw [MulAut.apply_inv_self, ← hf]
  congr 1
  omega

public theorem reflected_u (U : MulAut W) (f : Fin 7 → W)
    (hf : ∀ i, f (2 * i + 3) = U (f i)) (i : Fin 7) :
    f (1 - (2 * i + 3)) = U (f (1 - i)) := by
  rw [← hf]
  congr 1
  omega

/-- A four-element evaluation kernel has three nonidentity orbit labels. -/
public theorem positive_card [Finite W] (hW : Nat.card W = 8) (Y : MulAut W)
    (hY : Y ^ 7 = 1) (hnY : Y ≠ 1) {w : W} (hw : w ≠ 1)
    {K : Type*} [CommGroup K] (e : W →* K) (he : Nat.card e.ker = 4) :
    Nat.card {i : Fin 7 // e (orbitLabel Y w i) = 1} = 3 := by
  classical
  let : Fintype e.ker := Fintype.ofFinite e.ker
  let f : {i : Fin 7 // e (orbitLabel Y w i) = 1} → {v : e.ker // v ≠ 1} :=
    fun i => ⟨⟨orbitLabel Y w i.val, i.property⟩,
      fun hh => orbitLabel_nontrivial Y hw i.val (congrArg Subtype.val hh)⟩
  have hb : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Subtype.ext
      exact orbitLabel_injective hW Y hY hnY hw
        (congrArg (fun v : {v : e.ker // v ≠ 1} => v.val.val) hij)
    · intro v
      have hv : (v.val : W) ≠ 1 := fun hh => v.property (Subtype.ext hh)
      obtain ⟨i, hi⟩ := orbitLabel_exhaustive hW Y hY hnY hw v.val hv
      refine ⟨⟨i, by rw [hi]; exact v.val.property⟩, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hi
  rw [Nat.card_congr (Equiv.ofBijective f hb), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, show Fintype.card {v : e.ker // v = 1} = 1 from Fintype.card_unique, ← Nat.card_eq_fintype_card, he]

/-- The three +1 entries in the diagonal of the source marked involution. -/
@[expose] public def positivePattern : Fin 7 → Bool := ![false, true, false, false, false, true, true]

private theorem count_pattern (a b c : Bool) :
    (Finset.univ.filter (fun i : Fin 7 => ![a, b, a, a, c, b, b] i = true)).card = 3 →
    (a = false ∧ b = true ∧ c = false) ∨ (a = true ∧ b = false ∧ c = false) := by
  have hu : (Finset.univ : Finset (Fin 7)) = {0, 1, 2, 3, 4, 5, 6} := by
    ext i
    fin_cases i <;> simp
  cases a <;> cases b <;> cases c <;> simp [hu, Finset.filter_insert, Finset.filter_singleton]

private theorem cubic_tuple (p : Fin 7 → Bool) (hU : ∀ i, p (2 * i + 3) = p i) :
    p = ![p 0, p 1, p 0, p 0, p 4, p 1, p 1] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact (hU 3).trans (hU 0)
  · exact hU 0
  · rfl
  · exact hU 1
  · exact (hU 5).trans (hU 1)

private theorem negative_reflection (i : Fin 7) :
    ![true, false, true, true, false, false, false] (1 - i) = positivePattern i := by
  fin_cases i <;> rfl

public theorem finite_pattern : ∀ p : Fin 7 → Bool,
    (∀ i, p (2 * i + 3) = p i) →
    (Finset.univ.filter (fun i => p i = true)).card = 3 →
    (∀ i, p i = positivePattern i) ∨ (∀ i, p (1 - i) = positivePattern i) := by
  intro p hU hc
  have he := cubic_tuple p hU
  have hc' : (Finset.univ.filter (fun i : Fin 7 =>
      ![p 0, p 1, p 0, p 0, p 4, p 1, p 1] i = true)).card = 3 := by
    rwa [he] at hc
  rcases count_pattern (p 0) (p 1) (p 4) hc' with ⟨h0, h1, h4⟩ | ⟨h0, h1, h4⟩
  · have hh : p = positivePattern := by
      simpa only [h0, h1, h4, positivePattern] using he
    exact Or.inl (congrFun hh)
  · have hh : p = ![true, false, true, true, false, false, false] := by
      simpa only [h0, h1, h4] using he
    exact Or.inr (fun i => (congrFun hh (1 - i)).trans (negative_reflection i))

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation.CharacterMarking
