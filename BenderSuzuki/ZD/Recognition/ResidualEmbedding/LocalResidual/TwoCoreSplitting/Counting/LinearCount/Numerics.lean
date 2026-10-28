module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.Fibers

/-!
# Section 17 incidence cancellation and congruence

The two counts of the actual conjugacy-class incidences eliminate their
common class and ordered-pair cardinalities. The result is Lemma 17.1 with
the fixed-coset degree expressed as the circle index and with the genuine
rational centralizer-order ratio. Finite nonempty carriers justify cancellation.

After the concrete model supplies its Sylow order p, degree p+1, and torus
index q-1, the Section 16 divisibility q*p ∣ |G/M|-1 gives c ≡ 1 mod q.
We clear denominators before taking a natural-number remainder; a need not
be an integer. `Section17.linear_count_at_source_parameter` supplies these
model evaluations and consumes both results on the original local data.

Source: GLS4, Chapter 2, Lemma 17.1 and Lemma 17.2(a,b),
`refs/KGroup/GLS4/Chapter2.tex`, lines 3042–3100.
-/

namespace BenderSuzuki.ZD.Section17
open Subgroup Theory.GroupTheory

private theorem count_elimination {N C f U V : ℕ} {a : ℚ}
    (hC : 0 < C) (hU : U ≠ 0) (hf : f ≤ N) (hf1 : 1 ≤ f)
    (hfixed : C * (f * (f - 1)) = (N * (N - 1)) * U)
    (hmoved : C * (N - f) = (N * (N - 1)) * V)
    (ha : a = (V : ℚ) / U) :
    (N : ℚ) - 1 = ((f : ℚ) - 1) * ((f : ℚ) * a + 1) := by
  have he : (N - f) * U = (f * (f - 1)) * V := by
    apply Nat.eq_of_mul_eq_mul_left hC
    calc
      C * ((N - f) * U) = (C * (N - f)) * U := by ac_rfl
      _ = ((N * (N - 1)) * V) * U := by rw [hmoved]
      _ = ((N * (N - 1)) * U) * V := by ac_rfl
      _ = C * ((f * (f - 1)) * V) := by rw [← hfixed]; ac_rfl
  have he' : ((N : ℚ) - f) * U = ((f : ℚ) * (f - 1)) * V := by
    exact_mod_cast (show ((N - f : ℕ) : ℚ) * U =
      ((f : ℚ) * ((f - 1 : ℕ) : ℚ)) * V from by exact_mod_cast he)
  have ha' : a * U = V := (eq_div_iff (show (U : ℚ) ≠ 0 by exact_mod_cast hU)).mp ha
  have hfactor : ((N : ℚ) - f - (f * (f - 1)) * a) * U = 0 := by
    calc
      _ = ((N : ℚ) - f) * U - (f * (f - 1)) * (a * U) := by ring
      _ = 0 := by rw [ha', he']; ring
  have hz := (mul_eq_zero.mp hfactor).resolve_right (by exact_mod_cast hU)
  nlinarith [hz]

private theorem count_congruence {N p q c : ℕ} {a : ℚ}
    (hN : 0 < N) (hp : 0 < p) (hq : 1 < q) (hqp : q ∣ p)
    (hdvd : q * p ∣ N - 1)
    (hcount : (N : ℚ) - 1 = (p : ℚ) * (((p : ℚ) + 1) * a + 1))
    (hratio : a * c = (q : ℚ) - 1) : c % q = 1 := by
  obtain ⟨k, hk⟩ := hdvd
  have hk' : (N : ℚ) - 1 = (q : ℚ) * p * k := by
    have hh : ((N - 1 : ℕ) : ℚ) = (q : ℚ) * p * k := by exact_mod_cast hk
    simpa only [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] using hh
  have he : (p : ℚ) * ((q : ℚ) * k) =
      (p : ℚ) * (((p : ℚ) + 1) * a + 1) := by nlinarith [hk', hcount]
  have he' := mul_left_cancel₀ (show (p : ℚ) ≠ 0 by positivity) he
  have hc : (q : ℚ) * k * c + (p + 1) = (p + 1) * q + c := by
    nlinarith [congrArg (fun x : ℚ => x * c) he', hratio]
  have hc' : q * k * c + (p + 1) = (p + 1) * q + c := by exact_mod_cast hc
  have hh := congrArg (fun x : ℕ => x % q) hc'
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hqp, Nat.mod_eq_of_lt hq] using hh.symm

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Lemma 17.1 before evaluating the model: the degree is the actual
circle index, and a is the ratio of the two actual centralizer orders. -/
public theorem count_at_circle_index
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G))) :
    let f := (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index
    (Nat.card (G ⧸ M) : ℚ) - 1 =
      ((f : ℚ) - 1) * ((f : ℚ) * centralizerRatio d + 1) := by
  let F := {gamma : G ⧸ M // ((d.u : M) : G) • gamma = gamma}
  let C := {v : G // IsConj ((d.u : M) : G) v}
  have : Nonempty C := ⟨⟨((d.u : M) : G), IsConj.refl _⟩⟩
  have : Nonempty F := ⟨⟨QuotientGroup.mk 1, by
    exact QuotientGroup.eq.mpr (by simp)⟩⟩
  have hf : Nat.card F ≤ Nat.card (G ⧸ M) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hh := count_elimination (Nat.card_pos (α := C))
    (show (centralizer ({((d.u : M) : G)} : Set G)).relIndex
        (residualPairStabilizer M d.t) ≠ 0 from Nat.card_pos.ne')
    hf (Nat.card_pos (α := F)) (fixed_pair_count h ha d hlocal)
    (moved_pair_count_at_centralizer_index h ha d hlocal hfusion)
    (centralizerRatio_eq_index_ratio d)
  dsimp only at hh ⊢
  rwa [fixedPoints_card_eq_circle_index h r d] at hh

/-- Lemma 17.2(a,b), after the concrete action has supplied its Sylow
order, degree, and torus index. The final four-model assembly supplies
these evaluations; they are not additional source assumptions. -/
public theorem ratio_and_congruence_of_action
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G)))
    (p q : ℕ) (hp : 0 < p) (hq : 1 < q) (hqp : q ∣ p)
    (hdvd : q * p ∣ Nat.card (G ⧸ M) - 1)
    (hdegree : (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index = p + 1)
    (htorus : (centralizer ({d.t} : Set G)).relIndex
      (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G)) = q - 1) :
    let c := (centralizer ({d.t} : Set G)).relIndex
      (residualPairStabilizer M d.t ⊓ centralizerClosure Z (d.t * ((d.u : M) : G)))
    centralizerRatio d * c = (q : ℚ) - 1 ∧ c % q = 1 := by
  have hc := count_at_circle_index h r ha d hlocal hfusion
  dsimp only at hc ⊢
  rw [hdegree, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hc
  have hr := centralizerRatio_mul_twisted_index h r d
  rw [htorus, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] at hr
  exact ⟨hr, count_congruence Nat.card_pos hp hq hqp hdvd hc hr⟩

end BenderSuzuki.ZD.Section17
