module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Tactic

/-!
# Seven-point actions of the symmetric group on four letters

If every nonidentity permutation fixes fewer than four points in the disjoint
union of the natural four-point action and a supplied seven-point action, the
latter has a fixed point and is transitive on the six remaining points.

The proof uses three adjacent transpositions. Their images are involutions
with at most one fixed point, hence have cycle type `2 + 2 + 2 + 1`. Relabel
one image as `(0 1)(2 3)(4 5)`. A kernel-checked finite certificate considers
the 105 involutions of this cycle type for each of the other two images.
The adjacent braid relations, the commuting relation for the outside
transpositions, and the fixed-point bound on their product force a common
fixed point and transitivity on its complement. A list of 24 words in the
adjacent transpositions gives all elements of the four-letter symmetric group.
The final proof transports these conclusions along equivalences of finite types.
All enumerations are checked by Lean's kernel; no native evaluation axiom is used.

This is the independent small permutation-action ingredient of Jordan's
degree-eleven argument, cited in Wong (1964), p. 108, and Hall,
*The Theory of Groups*, §5.8.1. It uses no Mathieu-group or design recognition.
-/

open Equiv

namespace S4SevenPointOrbits

private def fixedCount {X : Type*} [Fintype X] [DecidableEq X] (f : Perm X) : ℕ :=
  (Finset.univ.filter (fun x => f x = x)).card

private theorem fixedCount_eq_card {X : Type*} [Fintype X] [DecidableEq X]
    (f : Perm X) : fixedCount f = Fintype.card (Function.fixedPoints f) := by
  rw [Fintype.card_subtype]
  rfl

private theorem fixedCount_congr {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (f : Perm X) :
    fixedCount (e.permCongrHom f) = fixedCount f := by
  rw [fixedCount_eq_card, fixedCount_eq_card]
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨e.symm x, by
      change f (e.symm x) = e.symm x
      have h := congrArg e.symm x.property
      simpa only [Equiv.permCongrHom_coe, Equiv.permCongr_apply,
        Equiv.symm_apply_apply] using h⟩
    invFun := fun x => ⟨e x, by
      change e (f (e.symm (e x))) = e x
      rw [e.symm_apply_apply, x.property]⟩
    left_inv := fun x => Subtype.ext (e.apply_symm_apply x)
    right_inv := fun x => Subtype.ext (e.symm_apply_apply x) }

private def base : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5

private theorem small_involution_cycleType (f : Perm (Fin 7))
    (hpow : f ^ 2 = 1) (hcount : fixedCount f ≤ 1) :
    f.cycleType = Multiset.replicate 3 2 := by
  have hrep := Perm.cycleType_of_pow_prime_eq_one hpow
  have hle := f.sum_cycleType_le
  have hcard := f.card_fixedPoints
  rw [← fixedCount_eq_card] at hcard
  rw [hrep, Multiset.sum_replicate, nsmul_eq_mul] at hcard hle
  simp only [Fintype.card_fin, Nat.cast_id] at hcard hle
  have hn : f.cycleType.card = 3 := by
    omega
  simpa only [hn] using hrep

private theorem normalize_involution (f : Perm (Fin 7)) (hpow : f ^ 2 = 1)
    (hcount : fixedCount f ≤ 1) : ∃ e : Perm (Fin 7), e.permCongrHom f = base := by
  have hbpow : base ^ 2 = 1 := by decide +kernel
  have hbcount : fixedCount base ≤ 1 := by decide +kernel
  have hconj : IsConj f base := Perm.isConj_iff_cycleType_eq.mpr
    ((small_involution_cycleType f hpow hcount).trans
      (small_involution_cycleType base hbpow hbcount).symm)
  obtain ⟨e, he⟩ := isConj_iff.mp hconj
  exact ⟨e, he⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def matchings : Fin 105 → Fin 7 → Fin 7 := ![![0, 2, 1, 4, 3, 6, 5],
  ![0, 2, 1, 5, 6, 3, 4],
  ![0, 2, 1, 6, 5, 4, 3],
  ![0, 3, 4, 1, 2, 6, 5],
  ![0, 3, 5, 1, 6, 2, 4],
  ![0, 3, 6, 1, 5, 4, 2],
  ![0, 4, 3, 2, 1, 6, 5],
  ![0, 4, 5, 6, 1, 2, 3],
  ![0, 4, 6, 5, 1, 3, 2],
  ![0, 5, 3, 2, 6, 1, 4],
  ![0, 5, 4, 6, 2, 1, 3],
  ![0, 5, 6, 4, 3, 1, 2],
  ![0, 6, 3, 2, 5, 4, 1],
  ![0, 6, 4, 5, 2, 3, 1],
  ![0, 6, 5, 4, 3, 2, 1],
  ![1, 0, 2, 4, 3, 6, 5],
  ![1, 0, 2, 5, 6, 3, 4],
  ![1, 0, 2, 6, 5, 4, 3],
  ![1, 0, 3, 2, 4, 6, 5],
  ![1, 0, 3, 2, 5, 4, 6],
  ![1, 0, 3, 2, 6, 5, 4],
  ![1, 0, 4, 3, 2, 6, 5],
  ![1, 0, 4, 5, 2, 3, 6],
  ![1, 0, 4, 6, 2, 5, 3],
  ![1, 0, 5, 3, 6, 2, 4],
  ![1, 0, 5, 4, 3, 2, 6],
  ![1, 0, 5, 6, 4, 2, 3],
  ![1, 0, 6, 3, 5, 4, 2],
  ![1, 0, 6, 4, 3, 5, 2],
  ![1, 0, 6, 5, 4, 3, 2],
  ![2, 1, 0, 4, 3, 6, 5],
  ![2, 1, 0, 5, 6, 3, 4],
  ![2, 1, 0, 6, 5, 4, 3],
  ![2, 3, 0, 1, 4, 6, 5],
  ![2, 3, 0, 1, 5, 4, 6],
  ![2, 3, 0, 1, 6, 5, 4],
  ![2, 4, 0, 3, 1, 6, 5],
  ![2, 4, 0, 5, 1, 3, 6],
  ![2, 4, 0, 6, 1, 5, 3],
  ![2, 5, 0, 3, 6, 1, 4],
  ![2, 5, 0, 4, 3, 1, 6],
  ![2, 5, 0, 6, 4, 1, 3],
  ![2, 6, 0, 3, 5, 4, 1],
  ![2, 6, 0, 4, 3, 5, 1],
  ![2, 6, 0, 5, 4, 3, 1],
  ![3, 1, 4, 0, 2, 6, 5],
  ![3, 1, 5, 0, 6, 2, 4],
  ![3, 1, 6, 0, 5, 4, 2],
  ![3, 2, 1, 0, 4, 6, 5],
  ![3, 2, 1, 0, 5, 4, 6],
  ![3, 2, 1, 0, 6, 5, 4],
  ![3, 4, 2, 0, 1, 6, 5],
  ![3, 4, 5, 0, 1, 2, 6],
  ![3, 4, 6, 0, 1, 5, 2],
  ![3, 5, 2, 0, 6, 1, 4],
  ![3, 5, 4, 0, 2, 1, 6],
  ![3, 5, 6, 0, 4, 1, 2],
  ![3, 6, 2, 0, 5, 4, 1],
  ![3, 6, 4, 0, 2, 5, 1],
  ![3, 6, 5, 0, 4, 2, 1],
  ![4, 1, 3, 2, 0, 6, 5],
  ![4, 1, 5, 6, 0, 2, 3],
  ![4, 1, 6, 5, 0, 3, 2],
  ![4, 2, 1, 3, 0, 6, 5],
  ![4, 2, 1, 5, 0, 3, 6],
  ![4, 2, 1, 6, 0, 5, 3],
  ![4, 3, 2, 1, 0, 6, 5],
  ![4, 3, 5, 1, 0, 2, 6],
  ![4, 3, 6, 1, 0, 5, 2],
  ![4, 5, 2, 6, 0, 1, 3],
  ![4, 5, 3, 2, 0, 1, 6],
  ![4, 5, 6, 3, 0, 1, 2],
  ![4, 6, 2, 5, 0, 3, 1],
  ![4, 6, 3, 2, 0, 5, 1],
  ![4, 6, 5, 3, 0, 2, 1],
  ![5, 1, 3, 2, 6, 0, 4],
  ![5, 1, 4, 6, 2, 0, 3],
  ![5, 1, 6, 4, 3, 0, 2],
  ![5, 2, 1, 3, 6, 0, 4],
  ![5, 2, 1, 4, 3, 0, 6],
  ![5, 2, 1, 6, 4, 0, 3],
  ![5, 3, 2, 1, 6, 0, 4],
  ![5, 3, 4, 1, 2, 0, 6],
  ![5, 3, 6, 1, 4, 0, 2],
  ![5, 4, 2, 6, 1, 0, 3],
  ![5, 4, 3, 2, 1, 0, 6],
  ![5, 4, 6, 3, 1, 0, 2],
  ![5, 6, 2, 4, 3, 0, 1],
  ![5, 6, 3, 2, 4, 0, 1],
  ![5, 6, 4, 3, 2, 0, 1],
  ![6, 1, 3, 2, 5, 4, 0],
  ![6, 1, 4, 5, 2, 3, 0],
  ![6, 1, 5, 4, 3, 2, 0],
  ![6, 2, 1, 3, 5, 4, 0],
  ![6, 2, 1, 4, 3, 5, 0],
  ![6, 2, 1, 5, 4, 3, 0],
  ![6, 3, 2, 1, 5, 4, 0],
  ![6, 3, 4, 1, 2, 5, 0],
  ![6, 3, 5, 1, 4, 2, 0],
  ![6, 4, 2, 5, 1, 3, 0],
  ![6, 4, 3, 2, 1, 5, 0],
  ![6, 4, 5, 3, 1, 2, 0],
  ![6, 5, 2, 4, 3, 1, 0],
  ![6, 5, 3, 2, 4, 1, 0],
  ![6, 5, 4, 3, 2, 1, 0]]
private def words : Fin 24 → List (Fin 3) := ![[], [0], [1], [2], [1, 0], [2, 0], [0, 1], [2, 1], [1, 2], [0, 1, 0], [2, 1, 0], [1, 2, 0], [2, 0, 1], [1, 2, 1], [0, 1, 2], [2, 0, 1, 0], [1, 2, 1, 0], [0, 1, 2, 0], [1, 2, 0, 1], [0, 1, 2, 1], [1, 2, 0, 1, 0], [0, 1, 2, 1, 0], [0, 1, 2, 0, 1], [0, 1, 2, 0, 1, 0]]
private def evalWord {X : Type*} (g : Fin 3 → X → X) : List (Fin 3) → X → X
  | [], x => x
  | i :: w, x => g i (evalWord g w x)
private theorem certificate : ∀ i j : Fin 105,
    let b := matchings i
    let c := matchings j
    (∀ x, base (b (base (b (base (b x))))) = x) →
    (∀ x, b (c (b (c (b (c x))))) = x) →
    (∀ x, base (c x) = c (base x)) →
    (Finset.univ.filter (fun x => base (c x) = x)).card ≤ 3 →
    (∀ k : Fin 24, evalWord ![base, b, c] (words k) 6 = 6) ∧
    ∀ q r : Fin 7, q ≠ 6 → r ≠ 6 →
      ∃ k : Fin 24, evalWord ![base, b, c] (words k) q = r := by
  decide +kernel
private def generator : Fin 3 → Perm (Fin 4) := ![swap 0 1, swap 1 2, swap 2 3]
private def wordPerm (k : Fin 24) : Perm (Fin 4) := ((words k).map generator).prod
private theorem words_surjective : Function.Surjective wordPerm := by decide +kernel

private theorem matchings_complete : ∀ f : Equiv.Perm (Fin 7), (∀ i, f (f i) = i) →
    (Finset.univ.filter (fun i => f i = i)).card ≤ 1 →
    ∃ k : Fin 105, ∀ i, f i = matchings k i := by
  decide +kernel

private theorem generator_sq : ∀ i : Fin 3, generator i ^ 2 = 1 := by decide +kernel
private theorem generator_cube01 : (generator 0 * generator 1) ^ 3 = 1 := by decide +kernel
private theorem generator_cube12 : (generator 1 * generator 2) ^ 3 = 1 := by decide +kernel
private theorem generator_commute02 : generator 0 * generator 2 = generator 2 * generator 0 :=
  by decide +kernel

private theorem evalWord_map {X : Type*} (ρ : Perm (Fin 4) →* Perm X)
    (w : List (Fin 3)) (x : X) :
    ρ ((w.map generator).prod) x = evalWord (fun i => ρ (generator i)) w x := by
  induction w generalizing x with
  | nil => simp [evalWord]
  | cons i w ih => simp [evalWord, ih]

private theorem concrete_normalized (ρ : Perm (Fin 4) →* Perm (Fin 7))
    (hbase : ρ (generator 0) = base)
    (hcount : ∀ i : Fin 3, fixedCount (ρ (generator i)) ≤ 1)
    (hdouble : fixedCount (ρ (generator 0 * generator 2)) ≤ 3) :
    (∀ σ, ρ σ 6 = 6) ∧ ∀ q r : Fin 7, q ≠ 6 → r ≠ 6 → ∃ σ, ρ σ q = r := by
  have hpows (i : Fin 3) : (ρ (generator i)) ^ 2 = 1 := by
    rw [← map_pow, generator_sq, map_one]
  have hinv (i : Fin 3) (x : Fin 7) : ρ (generator i) (ρ (generator i) x) = x := by
    exact congrArg (fun f : Perm (Fin 7) => f x) (hpows i)
  obtain ⟨ib, hb⟩ := matchings_complete (ρ (generator 1)) (hinv 1) (hcount 1)
  obtain ⟨ic, hc⟩ := matchings_complete (ρ (generator 2)) (hinv 2) (hcount 2)
  have hgens : (fun i => (ρ (generator i) : Fin 7 → Fin 7)) =
      ![(base : Fin 7 → Fin 7), matchings ib, matchings ic] := by
    funext i x
    fin_cases i
    · exact congrArg (fun f : Perm (Fin 7) => f x) hbase
    · exact hb x
    · exact hc x
  have h01 : (ρ (generator 0) * ρ (generator 1)) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, generator_cube01, map_one]
  have h12 : (ρ (generator 1) * ρ (generator 2)) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, generator_cube12, map_one]
  have h02 : ρ (generator 0) * ρ (generator 2) =
      ρ (generator 2) * ρ (generator 0) := by
    rw [← map_mul, ← map_mul, generator_commute02]
  have hcert := certificate ib ic
  dsimp only at hcert
  have hfirst : ∀ x, base (matchings ib (base (matchings ib (base (matchings ib x))))) = x := by
    intro x
    have h := congrArg (fun f : Perm (Fin 7) => f x) h01
    simpa only [pow_succ, pow_zero, mul_one, Perm.mul_apply, Perm.one_apply,
      hbase, hb] using h
  have hsecond : ∀ x, matchings ib (matchings ic (matchings ib
      (matchings ic (matchings ib (matchings ic x))))) = x := by
    intro x
    have h := congrArg (fun f : Perm (Fin 7) => f x) h12
    simpa only [pow_succ, pow_zero, mul_one, Perm.mul_apply, Perm.one_apply, hb, hc] using h
  have hcomm : ∀ x, base (matchings ic x) = matchings ic (base x) := by
    intro x
    have h := congrArg (fun f : Perm (Fin 7) => f x) h02
    simpa only [Perm.mul_apply, hbase, hc] using h
  have hfix : (Finset.univ.filter (fun x => base (matchings ic x) = x)).card ≤ 3 := by
    simpa only [fixedCount, map_mul, Perm.mul_apply, hbase, hc] using hdouble
  obtain ⟨hfixed, htrans⟩ := hcert hfirst hsecond hcomm hfix
  constructor
  · intro σ
    obtain ⟨k, rfl⟩ := words_surjective σ
    rw [wordPerm, evalWord_map, hgens]
    exact hfixed k
  · intro q r hq hr
    obtain ⟨k, hk⟩ := htrans q r hq hr
    refine ⟨wordPerm k, ?_⟩
    rw [wordPerm, evalWord_map, hgens]
    exact hk

private def HasOneSixOrbits {A B : Type*} (ρ : Perm A →* Perm B) : Prop :=
  ∃ p : B, (∀ σ, ρ σ p = p) ∧
    ∀ q : B, q ≠ p → ∀ r : B, r ≠ p → ∃ σ, ρ σ q = r

private theorem orbits_of_transport {A B C D : Type*}
    (eA : A ≃ C) (eB : B ≃ D) (ρ : Perm A →* Perm B)
    (h : HasOneSixOrbits (eB.permCongrHom.toMonoidHom.comp
      (ρ.comp eA.symm.permCongrHom.toMonoidHom))) : HasOneSixOrbits ρ := by
  obtain ⟨p, hp, ht⟩ := h
  refine ⟨eB.symm p, ?_, ?_⟩
  · intro σ
    have hh := hp (eA.permCongrHom σ)
    change eB (ρ (eA.symm.permCongrHom (eA.permCongrHom σ)) (eB.symm p)) = p at hh
    have hσ : eA.symm.permCongrHom (eA.permCongrHom σ) = σ :=
      eA.permCongrHom.symm_apply_apply σ
    rw [hσ] at hh
    apply eB.injective
    simpa only [eB.apply_symm_apply] using hh
  · intro q hq r hr
    have hq' : eB q ≠ p := by
      intro he
      apply hq
      exact (eB.symm_apply_apply q).symm.trans (congrArg eB.symm he)
    have hr' : eB r ≠ p := by
      intro he
      apply hr
      exact (eB.symm_apply_apply r).symm.trans (congrArg eB.symm he)
    obtain ⟨σ, hσ⟩ := ht (eB q) hq' (eB r) hr'
    refine ⟨eA.symm.permCongrHom σ, ?_⟩
    change eB (ρ (eA.symm.permCongrHom σ) (eB.symm (eB q))) = eB r at hσ
    simp only [eB.symm_apply_apply] at hσ
    exact eB.injective hσ

private theorem concrete (ρ : Perm (Fin 4) →* Perm (Fin 7))
    (hcount : ∀ i : Fin 3, fixedCount (ρ (generator i)) ≤ 1)
    (hdouble : fixedCount (ρ (generator 0 * generator 2)) ≤ 3) :
    HasOneSixOrbits ρ := by
  have hpow : (ρ (generator 0)) ^ 2 = 1 := by
    rw [← map_pow, generator_sq, map_one]
  obtain ⟨e, he⟩ := normalize_involution (ρ (generator 0)) hpow (hcount 0)
  let τ := e.permCongrHom.toMonoidHom.comp ρ
  have hτcount (i : Fin 3) : fixedCount (τ (generator i)) ≤ 1 := by
    change fixedCount (e.permCongrHom (ρ (generator i))) ≤ 1
    rw [fixedCount_congr]
    exact hcount i
  have hτdouble : fixedCount (τ (generator 0 * generator 2)) ≤ 3 := by
    change fixedCount (e.permCongrHom (ρ (generator 0 * generator 2))) ≤ 3
    rw [fixedCount_congr]
    exact hdouble
  obtain ⟨hf, ht⟩ := concrete_normalized τ he hτcount hτdouble
  apply orbits_of_transport (Equiv.refl (Fin 4)) e ρ
  change HasOneSixOrbits τ
  exact ⟨6, hf, fun q hq r hr => ht q r hq hr⟩

private theorem generator_fixedCount : ∀ i : Fin 3, fixedCount (generator i) = 2 :=
  by decide +kernel

private theorem generator_ne_one : ∀ i : Fin 3, generator i ≠ 1 := by decide +kernel

private theorem double_ne_one : generator 0 * generator 2 ≠ 1 := by decide +kernel

/-- Under the combined fixed-point bound, a seven-point action of the symmetric
four-letter group has a fixed point and is transitive on its complement. -/
public theorem exists_fixed_point_and_transitive_complement
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (hA : Fintype.card A = 4) (hB : Fintype.card B = 7)
    (ρ : Perm A →* Perm B)
    (hfixed : ∀ σ, σ ≠ 1 →
      (Finset.univ.filter (fun a : A => σ a = a)).card +
        (Finset.univ.filter (fun b : B => ρ σ b = b)).card < 4) :
    ∃ p : B, (∀ σ, ρ σ p = p) ∧
      ∀ q : B, q ≠ p → ∀ r : B, r ≠ p → ∃ σ, ρ σ q = r := by
  let eA := Fintype.equivFinOfCardEq hA
  let eB := Fintype.equivFinOfCardEq hB
  let τ := eB.permCongrHom.toMonoidHom.comp (ρ.comp eA.symm.permCongrHom.toMonoidHom)
  have hτ : ∀ σ, σ ≠ 1 → fixedCount σ + fixedCount (τ σ) < 4 := by
    intro σ hσ
    have hne : eA.symm.permCongrHom σ ≠ 1 := by
      intro he
      apply hσ
      exact eA.symm.permCongrHom.injective (he.trans (map_one _).symm)
    have hh := hfixed (eA.symm.permCongrHom σ) hne
    change fixedCount (eA.symm.permCongrHom σ) +
      fixedCount (ρ (eA.symm.permCongrHom σ)) < 4 at hh
    change fixedCount σ + fixedCount (eB.permCongrHom
      (ρ (eA.symm.permCongrHom σ))) < 4
    rw [fixedCount_congr] at hh ⊢
    exact hh
  have hcount (i : Fin 3) : fixedCount (τ (generator i)) ≤ 1 := by
    have h := hτ (generator i) (generator_ne_one i)
    rw [generator_fixedCount] at h
    omega
  have hdouble : fixedCount (τ (generator 0 * generator 2)) ≤ 3 := by
    have h := hτ (generator 0 * generator 2) double_ne_one
    omega
  exact orbits_of_transport eA eB ρ (concrete τ hcount hdouble)

end S4SevenPointOrbits
