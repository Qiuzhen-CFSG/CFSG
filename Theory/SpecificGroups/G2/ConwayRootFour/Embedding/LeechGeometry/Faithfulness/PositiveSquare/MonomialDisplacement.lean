module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare.Reduction

/-!
# Short displacements of monomial involutions

Every noncentral involution in the Golay monomial group has a nonzero signed
Leech displacement of norm less than eight. A coordinate pair with coefficients
four handles a permutation with both fixed and moved coordinates. For the
identity and fixed-point-free cases, central negation reduces the negative
support to at most twelve coordinates, and a suitable odd glue vector gives
raw squared norm four times that support size, or 32 when the signs are positive.
The integral half-norm identity supplies the exact strict bounds.

This proves the monomial premise of `eq_sign_of_fixed_cross`, used in the
faithful-action argument of Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, with the scalar geometry of Section 48, p.269.

The coordinate model and lattice APIs are Gerald Höhn's attributed ATLAS ports,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, in
`Theory.AtlasPort.OtherSporadic.Lattices`. See `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. The displacement calculation here uses these
literal signed-permutation and lattice conventions.
-/

public section

open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.PositiveSquare

private def signedCoordinates (c : BinaryWord) (p : Equiv.Perm Omega)
    (x : IntegerCoordinates) : IntegerCoordinates :=
  fun i => if c i = 0 then x (p i) else -x (p i)

private theorem mixed_pair_sub (c : BinaryWord) (p : Equiv.Perm Omega)
    (hp : Function.Involutive p) (a b : Omega) (ha : p a = a) (hb : p b ≠ b)
    (hc : c a = 0) :
    let x := coordinateVector a 4 + coordinateVector b 4
    integerDot (signedCoordinates c p x - x) (signedCoordinates c p x - x) = 32 := by
  classical
  dsimp only
  have hab : a ≠ b := by rintro rfl; exact hb ha
  have hpa (i : Omega) : p i = a ↔ i = a := by
    constructor
    · intro hi; have := congrArg p hi; simpa only [hp i, ha] using this
    · rintro rfl; exact ha
  have hpb (i : Omega) : p i = b ↔ i = p b := by
    constructor
    · intro hi; have := congrArg p hi; simpa only [hp i] using this
    · rintro rfl; exact hp b
  have hab' : a ≠ p b := by
    intro he; have := congrArg p he; rw [ha, hp] at this; exact hab this
  have he (i : Omega) :
      (signedCoordinates c p (coordinateVector a 4 + coordinateVector b 4) -
          (coordinateVector a 4 + coordinateVector b 4)) i *
        (signedCoordinates c p (coordinateVector a 4 + coordinateVector b 4) -
          (coordinateVector a 4 + coordinateVector b 4)) i =
        (if i = b then 16 else 0) + (if i = p b then 16 else 0) := by
    simp only [Pi.sub_apply, signedCoordinates, Pi.add_apply, coordinateVector,
      Pi.single_apply, hpa, hpb]
    by_cases hi : i = a
    · subst i; simp [hc, hab, hab']
    · by_cases hib : i = b <;> by_cases hip : i = p b <;>
        by_cases hci : c i = 0 <;> simp_all
  simp only [integerDot, he, Finset.sum_add_distrib]
  simp

private theorem mixed_pair_add (c : BinaryWord) (p : Equiv.Perm Omega)
    (hp : Function.Involutive p) (a b : Omega) (ha : p a = a) (hb : p b ≠ b)
    (hc : c a ≠ 0) :
    let x := coordinateVector a 4 + coordinateVector b 4
    integerDot (signedCoordinates c p x + x) (signedCoordinates c p x + x) = 32 := by
  classical
  dsimp only
  have hab : a ≠ b := by rintro rfl; exact hb ha
  have hpa (i : Omega) : p i = a ↔ i = a := by
    constructor
    · intro hi; have := congrArg p hi; simpa only [hp i, ha] using this
    · rintro rfl; exact ha
  have hpb (i : Omega) : p i = b ↔ i = p b := by
    constructor
    · intro hi; have := congrArg p hi; simpa only [hp i] using this
    · rintro rfl; exact hp b
  have hab' : a ≠ p b := by
    intro he; have := congrArg p he; rw [ha, hp] at this; exact hab this
  have he (i : Omega) :
      (signedCoordinates c p (coordinateVector a 4 + coordinateVector b 4) +
          (coordinateVector a 4 + coordinateVector b 4)) i *
        (signedCoordinates c p (coordinateVector a 4 + coordinateVector b 4) +
          (coordinateVector a 4 + coordinateVector b 4)) i =
        (if i = b then 16 else 0) + (if i = p b then 16 else 0) := by
    simp only [Pi.add_apply, signedCoordinates, coordinateVector,
      Pi.single_apply, hpa, hpb]
    by_cases hi : i = a
    · subst i; simp [hc, hab, hab']
    · by_cases hib : i = b <;> by_cases hip : i = p b <;>
        by_cases hci : c i = 0 <;> simp_all
  simp only [integerDot, he, Finset.sum_add_distrib]
  simp

private theorem glue_fixed_norm (c : BinaryWord) (p : Equiv.Perm Omega)
    (hp : ∀ i, p i = i) (a : Omega) (ha : c a = 0) :
    integerDot (signedCoordinates c p (oddGlue a) - oddGlue a)
      (signedCoordinates c p (oddGlue a) - oddGlue a) = 4 * (hammingNorm c : ℤ) := by
  classical
  rw [hammingNorm_eq_sum, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, signedCoordinates, oddGlue, hp]
  by_cases hi : i = a
  · subst i; simp [ha]
  · by_cases hc : c i = 0 <;> simp [hi, hc]

private theorem glue_moved_negative_norm (c : BinaryWord) (p : Equiv.Perm Omega)
    (hc : ∀ i, c (p i) = c i)
    (a : Omega) (ha : p a ≠ a) (hca : c a ≠ 0) :
    integerDot (signedCoordinates c p (oddGlue a) - oddGlue a)
      (signedCoordinates c p (oddGlue a) - oddGlue a) = 4 * (hammingNorm c : ℤ) := by
  classical
  rw [hammingNorm_eq_sum, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, signedCoordinates, oddGlue]
  by_cases hi : i = a
  · subst i; simp [ha, hca]
  · by_cases hpi : p i = a
    · have hci : c i ≠ 0 := by rw [← hc i, hpi]; exact hca
      simp [hi, hpi, hci]
    · by_cases hci : c i = 0 <;> simp [hi, hpi, hci]

private theorem glue_moved_zero_norm (p : Equiv.Perm Omega)
    (hp : Function.Involutive p) (a : Omega) (ha : p a ≠ a) :
    integerDot (signedCoordinates 0 p (oddGlue a) - oddGlue a)
      (signedCoordinates 0 p (oddGlue a) - oddGlue a) = 32 := by
  classical
  have hpa (i : Omega) : p i = a ↔ i = p a := by
    constructor
    · intro hi; have := congrArg p hi; simpa only [hp i] using this
    · rintro rfl; exact hp a
  have he (i : Omega) :
      (signedCoordinates 0 p (oddGlue a) - oddGlue a) i *
        (signedCoordinates 0 p (oddGlue a) - oddGlue a) i =
        (if i = a then 16 else 0) + (if i = p a then 16 else 0) := by
    simp only [Pi.sub_apply, signedCoordinates, Pi.zero_apply, ite_true, oddGlue, hpa]
    by_cases hi : i = a <;> by_cases hip : i = p a <;> simp_all
  simp only [integerDot, he, Finset.sum_add_distrib]
  simp

private theorem raw_short (x : leech)
    (hpos : 0 < integerDot x.val x.val) (hsmall : integerDot x.val x.val < 64) :
    0 < leechHalfNorm x ∧ leechHalfNorm x < 4 := by
  have h := leechHalfNorm_mul x
  omega

private theorem glue_mem (a : Omega) : oddGlue a ∈ leech := by
  change oddGlue a ∈ leechAt ((0, 0), 0)
  rw [leechAt_independent ((0, 0), 0) a]
  exact oddGlue_mem a

private theorem short_of_small_support (g : LeechIsometryGroup)
    (c : BinaryWord) (p : Equiv.Perm Omega)
    (hp : Function.Involutive p) (hc : ∀ i, c (p i) = c i)
    (hact : ∀ x : leech, (g.val x).val = signedCoordinates c p x.val)
    (hne : g ≠ 1) (hw : hammingNorm c ≤ 12) : ShortDisplacement g := by
  classical
  by_cases hfixed : ∃ a, p a = a
  · obtain ⟨a, ha⟩ := hfixed
    by_cases hmoved : ∃ b, p b ≠ b
    · obtain ⟨b, hb⟩ := hmoved
      let x : leech := ⟨coordinateVector a 4 + coordinateVector b 4,
        coordinate_pair_mem a b⟩
      refine ⟨x, ?_⟩
      by_cases hca : c a = 0
      · left
        have hn : integerDot (g.val x - x).val (g.val x - x).val = 32 := by
          change integerDot ((g.val x).val - x.val) ((g.val x).val - x.val) = 32
          rw [hact]
          exact mixed_pair_sub c p hp a b ha hb hca
        exact raw_short _ (by omega) (by omega)
      · right
        have hn : integerDot (g.val x + x).val (g.val x + x).val = 32 := by
          change integerDot ((g.val x).val + x.val) ((g.val x).val + x.val) = 32
          rw [hact]
          exact mixed_pair_add c p hp a b ha hb hca
        exact raw_short _ (by omega) (by omega)
    · push Not at hmoved
      have hcz : c ≠ 0 := by
        intro hz
        apply hne
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        rw [hact, hz]
        ext i
        simp [signedCoordinates, hmoved]
      have hwpos : 0 < hammingNorm c := Nat.pos_of_ne_zero (fun hz =>
        hcz (hammingNorm_eq_zero.mp hz))
      obtain ⟨a, ha⟩ : ∃ a, c a = 0 := by
        by_contra! hn
        have he : c = allOnes := by
          ext i
          rcases bit_cases (c i) with hi | hi
          · exact (hn i hi).elim
          · exact hi
        have hh : hammingNorm c = 24 := by rw [he]; decide
        omega
      let x : leech := ⟨oddGlue a, glue_mem a⟩
      have hn : integerDot (g.val x - x).val (g.val x - x).val =
          4 * (hammingNorm c : ℤ) := by
        change integerDot ((g.val x).val - x.val) ((g.val x).val - x.val) = _
        rw [hact]
        exact glue_fixed_norm c p hmoved a ha
      exact ⟨x, Or.inl (raw_short _ (by omega) (by omega))⟩
  · push Not at hfixed
    by_cases hcz : c = 0
    · let a : Omega := ((0, 0), 0)
      let x : leech := ⟨oddGlue a, glue_mem a⟩
      have hn : integerDot (g.val x - x).val (g.val x - x).val = 32 := by
        change integerDot ((g.val x).val - x.val) ((g.val x).val - x.val) = 32
        rw [hact, hcz]
        exact glue_moved_zero_norm p hp a (hfixed a)
      exact ⟨x, Or.inl (raw_short _ (by omega) (by omega))⟩
    · have hwpos : 0 < hammingNorm c := Nat.pos_of_ne_zero (fun hz =>
        hcz (hammingNorm_eq_zero.mp hz))
      obtain ⟨a, ha⟩ : ∃ a, c a ≠ 0 := by
        by_contra! hn
        exact hcz (funext hn)
      let x : leech := ⟨oddGlue a, glue_mem a⟩
      have hn : integerDot (g.val x - x).val (g.val x - x).val =
          4 * (hammingNorm c : ℤ) := by
        change integerDot ((g.val x).val - x.val) ((g.val x).val - x.val) = _
        rw [hact]
        exact glue_moved_negative_norm c p hc a (hfixed a) ha
      exact ⟨x, Or.inl (raw_short _ (by omega) (by omega))⟩

private theorem short_of_negation (g : LeechIsometryGroup)
    (h : ShortDisplacement (negationIsometry * g)) : ShortDisplacement g := by
  obtain ⟨x, hx | hx⟩ := h
  · refine ⟨x, Or.inr ?_⟩
    have he : (negationIsometry * g).val x - x = -(g.val x + x) := by
      change negationIsometry.val (g.val x) - x = _
      rw [negationIsometry_apply]
      abel
    rwa [he, leechHalfNorm_neg] at hx
  · refine ⟨x, Or.inl ?_⟩
    have he : (negationIsometry * g).val x + x = -(g.val x - x) := by
      change negationIsometry.val (g.val x) + x = _
      rw [negationIsometry_apply]
      abel
    rwa [he, leechHalfNorm_neg] at hx

/-- A noncentral monomial involution moves an actual Leech vector by a nonzero
vector of normalized norm less than eight, after allowing either sign. -/
theorem monomial_short_displacement : MonomialShortDisplacement := by
  classical
  intro m hsq hne hneg
  let c : BinaryWord := m.left.toAdd.val
  let p : Equiv.Perm Omega := m.right.val.symm
  have hm : m * m = 1 := monomialEmbedding_injective (by
    rw [map_mul, map_one]
    exact hsq)
  have hp : Function.Involutive p := by
    intro i
    have he := congrArg (fun n : GolayMonomialGroup => n.right.val.symm i) hm
    exact he
  have hc : ∀ i, c (p i) = c i := by
    intro i
    have he := congrArg (fun n : GolayMonomialGroup => n.left.toAdd.val i) hm
    change c i + c (p i) = 0 at he
    rcases bit_cases (c i) with hi | hi <;>
      rcases bit_cases (c (p i)) with hj | hj <;> simp_all
  have hact : ∀ x : leech, ((monomialEmbedding m).val x).val =
      signedCoordinates c p x.val := fun _ => rfl
  by_cases hw : hammingNorm c ≤ 12
  · exact short_of_small_support (monomialEmbedding m) c p hp hc hact hne hw
  · apply short_of_negation
    apply short_of_small_support (negationIsometry * monomialEmbedding m)
      (c + allOnes) p hp
    · intro i
      simp only [Pi.add_apply, allOnes, hc]
    · intro x
      ext i
      change -(((monomialEmbedding m).val x).val i) = _
      rw [congrFun (hact x) i]
      rcases bit_cases (c i) with hi | hi <;>
        simp [signedCoordinates, Pi.add_apply, allOnes, hi]
    · intro he
      apply hneg
      have he' := congrArg (fun k : LeechIsometryGroup => negationIsometry * k) he
      simpa only [← mul_assoc, negationIsometry_sq, one_mul, mul_one] using he'
    · have hh := complement_weight c
      omega

/-- The actual fixed-cross reduction with its monomial premise discharged. -/
theorem eq_sign_of_fixed_cross_of_no_short (h : LeechIsometryGroup)
    (hsq : h ^ 2 = 1) (X : LeechCross) (hX : crossAction h X = X)
    (hshort : ¬ ShortDisplacement h) : h = 1 ∨ h = negationIsometry :=
  eq_sign_of_fixed_cross monomial_short_displacement h hsq X hX hshort

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.PositiveSquare
