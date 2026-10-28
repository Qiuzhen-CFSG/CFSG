module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_3_d
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.RootSystemType

/-!
Classifies point-injective algebraic-group morphisms of the additive
one-dimensional group.  The coordinate regular function is represented by a
polynomial; injectivity forces every root to be zero, so the polynomial is a
nonzero scalar times a monomial.  Additivity of the morphism then makes its
degree a Frobenius power: in characteristic zero, the derivative at zero gives
degree one, while in positive characteristic the same derivative gives
divisibility by the characteristic and Frobenius injectivity descends the
exponent.  This is the source-faithful proof of the staged classification
declaration and uses only its strict ancestor imports.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

public theorem injective_additive_morphism_eq_scalar_frobenius
    {k : Type u} [Field k] [IsAlgClosed k]
    (f : AlgebraicGroup.Morphism (KPlus k) (KPlus k))
    (hf : Function.Injective f.onPoints) :
    ∃ n : ℕ, ∃ c : k,
      (ringChar k = 0 → n = 0) ∧
      0 < (ringChar k : ℝ) ^ n ∧
      c ≠ 0 ∧
      ∀ t : k,
        f.onPoints (kPlusPoint t) =
          kPlusPoint (c * t ^ ((ringChar k) ^ n)) := by
  rcases f.toVariety.regular PUnit.unit with ⟨p, hp⟩
  let P : Polynomial k := MvPolynomial.uniqueAlgEquiv k PUnit p
  have hP : ∀ t : k,
      (f.onPoints (kPlusPoint t)).val PUnit.unit = P.eval t := by
    intro t
    change (f.toVariety.toFun (kPlusPoint t)).val PUnit.unit = P.eval t
    rw [hp]
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) p = P.eval t
    rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
    rfl
  have hpoint : ∀ t : k,
      f.onPoints (kPlusPoint t) = kPlusPoint (P.eval t) := by
    intro t
    apply Variety.Point.ext
    funext i
    exact hP t
  have hPzero : P.eval 0 = 0 := by
    calc
      P.eval 0 = (f.onPoints (kPlusPoint 0)).val PUnit.unit := (hP 0).symm
      _ = (f.onPoints 1).val PUnit.unit := by rfl
      _ = (1 : Variety.Point (KPlus k)).val PUnit.unit :=
        congrArg (fun z : Variety.Point (KPlus k) ↦ z.val PUnit.unit) f.map_one
      _ = 0 := by rfl
  have hP0 : P ≠ 0 := by
    intro hzero
    have hconst : ∀ t : k,
        f.onPoints (kPlusPoint t) = kPlusPoint 0 := by
      intro t
      rw [hpoint t, hzero]
      simp
    have h01 : kPlusPoint (0 : k) = kPlusPoint 1 :=
      hf (by rw [hconst 0, hconst 1])
    have hcoord := congrArg
      (fun z : Variety.Point (KPlus k) ↦ z.val PUnit.unit) h01
    simp [kPlusPoint, additiveGroupPointEquiv] at hcoord
    exact zero_ne_one (Multiplicative.ofAdd.injective hcoord)
  have hroot_zero : ∀ a : k, a ∈ P.roots → a = 0 := by
    intro a ha
    have hroot : P.eval a = 0 := (Polynomial.mem_roots hP0).mp ha
    have hout : f.onPoints (kPlusPoint a) = f.onPoints (kPlusPoint 0) := by
      rw [hpoint a, hpoint 0, hroot, hPzero]
    have hin := hf hout
    have hcoord := congrArg
      (fun z : Variety.Point (KPlus k) ↦ z.val PUnit.unit) hin
    simp [kPlusPoint, additiveGroupPointEquiv] at hcoord
    exact Multiplicative.ofAdd.injective hcoord
  have hroots : P.roots = Multiset.replicate P.natDegree 0 := by
    have h := Multiset.eq_replicate_of_mem (s := P.roots) (a := (0 : k)) hroot_zero
    simpa [IsAlgClosed.card_roots_eq_natDegree] using h
  have hPshape : P = Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree := by
    calc
      P = Polynomial.C P.leadingCoeff *
          (Multiset.map (fun x : k ↦ Polynomial.X - Polynomial.C x) P.roots).prod :=
        (IsAlgClosed.splits P).eq_prod_roots
      _ = Polynomial.C P.leadingCoeff *
          (Multiset.map (fun x : k ↦ Polynomial.X - Polynomial.C x)
            (Multiset.replicate P.natDegree 0)).prod := by rw [hroots]
      _ = Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree := by simp
  have hmpos : 0 < P.natDegree := by
    by_contra hm
    have hmzero : P.natDegree = 0 := Nat.eq_zero_of_not_pos hm
    have hs := congrArg (Polynomial.eval 0) hPshape
    have hlead : P.leadingCoeff = 0 := by
      simpa [hmzero, hPzero] using hs.symm
    apply hP0
    rw [hPshape, hmzero, hlead]
    simp
  let c : k := P.leadingCoeff
  have hc : c ≠ 0 := by
    dsimp [c]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hcm : ∀ t : k, P.eval t = c * t ^ P.natDegree := by
    intro t
    calc
      P.eval t = (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree).eval t :=
        congrArg (Polynomial.eval t) hPshape
      _ = c * t ^ P.natDegree := by simp [c]
  have haddP : ∀ x y : k, P.eval (x + y) = P.eval x + P.eval y := by
    intro x y
    have hmul :
        f.onPoints (kPlusPoint (x + y)) =
          f.onPoints (kPlusPoint x) * f.onPoints (kPlusPoint y) := by
      rw [← kPlusPoint_mul]
      exact f.map_mul _ _
    have hcoord := congrArg
      (fun z : Variety.Point (KPlus k) ↦ z.val PUnit.unit) hmul
    calc
      P.eval (x + y) = (f.onPoints (kPlusPoint (x + y))).val PUnit.unit :=
        (hP (x + y)).symm
      _ = (f.onPoints (kPlusPoint x) * f.onPoints (kPlusPoint y)).val PUnit.unit := hcoord
      _ = P.eval x + P.eval y := by
        rw [hpoint x, hpoint y, kPlusPoint_coordinate_mul]
        have hcoord_x : (kPlusPoint (P.eval x)).val PUnit.unit = P.eval x := by
          change Multiplicative.toAdd
            (additiveGroupPointEquiv k (kPlusPoint (P.eval x))) = P.eval x
          simp [kPlusPoint]
        have hcoord_y : (kPlusPoint (P.eval y)).val PUnit.unit = P.eval y := by
          change Multiplicative.toAdd
            (additiveGroupPointEquiv k (kPlusPoint (P.eval y))) = P.eval y
          simp [kPlusPoint]
        rw [hcoord_x, hcoord_y]
  have hmadd : ∀ x y : k,
      (x + y) ^ P.natDegree = x ^ P.natDegree + y ^ P.natDegree := by
    intro x y
    apply mul_left_cancel₀ hc
    calc
      c * (x + y) ^ P.natDegree = P.eval (x + y) := (hcm (x + y)).symm
      _ = P.eval x + P.eval y := haddP x y
      _ = c * x ^ P.natDegree + c * y ^ P.natDegree := by
        rw [hcm x, hcm y]
      _ = c * (x ^ P.natDegree + y ^ P.natDegree) := by rw [mul_add]
  have hcast_zero : ∀ (m : ℕ), 1 < m →
      (∀ x y : k, (x + y) ^ m = x ^ m + y ^ m) → (m : k) = 0 := by
    intro m hm hadd
    have hpoly : (Polynomial.X + Polynomial.C (1 : k)) ^ m =
        Polynomial.X ^ m + Polynomial.C 1 := by
      apply Polynomial.eq_of_infinite_eval_eq
      exact Set.infinite_univ.mono (by
        intro x _
        simpa using hadd x 1)
    have hd := congrArg Polynomial.derivative hpoly
    have he := congrArg (Polynomial.eval 0) hd
    have hm1 : 0 < m - 1 := Nat.sub_pos_of_lt hm
    simpa [Polynomial.derivative_pow, Polynomial.derivative_X_add_C,
      zero_pow (Nat.ne_of_gt hm1)] using he
  by_cases hchar0 : ringChar k = 0
  · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp hchar0
    have hmone : P.natDegree = 1 := by
      by_contra hm
      have hmg : 1 < P.natDegree := by omega
      have hcast := hcast_zero P.natDegree hmg hmadd
      exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmpos)) hcast
    refine ⟨0, c, ?_, ?_, hc, ?_⟩
    · intro _
      rfl
    · simp [hchar0]
    · intro t
      rw [hpoint t, hcm t, hmone]
      simp
  · have hpprime : Nat.Prime (ringChar k) :=
      (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hchar0
    letI : Fact (Nat.Prime (ringChar k)) := ⟨hpprime⟩
    letI : PerfectRing k (ringChar k) := IsAlgClosed.perfectRing k (ringChar k)
    have hpow : ∀ m : ℕ, 0 < m →
        (∀ x y : k, (x + y) ^ m = x ^ m + y ^ m) →
        ∃ n : ℕ, m = (ringChar k) ^ n := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
          intro hm hadd
          by_cases hmone : m = 1
          · exact ⟨0, by simp [hmone]
          ⟩
          have hmg : 1 < m := by omega
          have hcast := hcast_zero m hmg hadd
          have hdiv : ringChar k ∣ m := (CharP.cast_eq_zero_iff k (ringChar k) m).mp hcast
          rcases exists_eq_mul_left_of_dvd hdiv with ⟨q, hq⟩
          have hqpos : 0 < q := by
            by_contra hq'
            have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq'
            rw [hq0] at hq
            omega
          have hqlt : q < m := by
            calc
              q = q * 1 := by simp
              _ < q * ringChar k := Nat.mul_lt_mul_of_pos_left hpprime.one_lt hqpos
              _ = m := hq.symm
          have hqadd : ∀ x y : k,
              (x + y) ^ q = x ^ q + y ^ q := by
            intro x y
            apply injective_pow_p k (ringChar k)
            calc
              ((x + y) ^ q) ^ ringChar k = (x + y) ^ (q * ringChar k) := by rw [pow_mul]
              _ = x ^ (q * ringChar k) + y ^ (q * ringChar k) := by simpa [hq] using hadd x y
              _ = (x ^ q) ^ ringChar k + (y ^ q) ^ ringChar k := by rw [pow_mul, pow_mul]
              _ = (x ^ q + y ^ q) ^ ringChar k := by
                rw [add_pow_char]
          rcases ih q hqlt hqpos hqadd with ⟨n, hn⟩
          refine ⟨n + 1, ?_⟩
          simpa [hq, hn, pow_succ]
    rcases hpow P.natDegree hmpos hmadd with ⟨n, hn⟩
    refine ⟨n, c, ?_, ?_, hc, ?_⟩
    · intro hzero
      exact (hchar0 hzero).elim
    · have hp_real : (0 : ℝ) < (ringChar k : ℝ) := by
        exact_mod_cast hpprime.pos
      exact pow_pos hp_real n
    · intro t
      rw [hpoint t, hcm t, hn]

end Theory.AlgebraicGroup
