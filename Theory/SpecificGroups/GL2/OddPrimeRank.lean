module

public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Odd-prime ranks of GL₂ in characteristic two

Every elementary abelian p-subgroup of GL₂(F), for F a finite field of
characteristic two and p an odd prime, has order at most p². Extend the
natural matrix action faithfully to an algebraic closure. The group order
is nonzero in that field, so the action splits into at most two character
weights, including the trivial weight if it occurs. These characters
separate elements and take values in the p-th roots of unity. Evaluation
therefore embeds the subgroup into a product of at most two sets of size
at most p. The proved elementary-abelian characterization of prime rank
then gives the bound for the abelian-generator definition of `primeRank`.

This is the GL₂ input to the odd-rank bounds for the full PSL₃ parabolics
in the generic case of Aschbacher–Smith, *The Classification of Quasithin
Groups*, Theorem 0.1.2(1), printed p.4, repeated on p.482. The elementary
rank convention is specified on printed p.4.
-/

open scoped IsMulCommutative

namespace Matrix.GeneralLinearGroup

/-- Elementary abelian odd-prime subgroups of GL₂ over a finite field of
characteristic two have order at most the square of the prime. -/
public theorem elementaryAbelian_card_le_sq_of_odd
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (GL (Fin 2) F)) [IsElementaryAbelian p A] :
    Nat.card A ≤ p ^ 2 := by
  classical
  let E := AlgebraicClosure F
  let f : GL (Fin 2) F →* GL (Fin 2) E := map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : GL (Fin 2) E => c i j) h
  let sigma : Representation E A (Fin 2 → E) :=
    (Representation.generalLinearNatural 2).comp (f.comp A.subtype)
  have hsigma : Function.Injective sigma :=
    (Representation.generalLinearNatural_injective 2).comp (hf.comp A.subtype_injective)
  have hpF : (p : F) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff F 2]
    exact hp.not_two_dvd_nat
  have horderF : (Nat.card A : F) ≠ 0 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n hpF
  have horder : (Nat.card A : E) ≠ 0 := by
    intro h
    apply horderF
    apply (algebraMap F E).injective
    simpa using h
  obtain ⟨hfinite, hweights⟩ := sigma.characterWeight_card_le horder
  let := hfinite
  have hweights2 : Nat.card sigma.CharacterWeight ≤ 2 := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using hweights
  let evaluate : A → (sigma.CharacterWeight → rootsOfUnity p E) := fun a chi =>
    ⟨chi.val a, by
      rw [mem_rootsOfUnity, ← map_pow]
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p A) a, map_one]⟩
  have hevaluate : Function.Injective evaluate := by
    intro a b hab
    apply sigma.eq_of_characterWeight_values hsigma horder a b
    intro chi
    exact congrArg Subtype.val (congrFun hab chi)
  calc
    Nat.card A ≤ Nat.card (sigma.CharacterWeight → rootsOfUnity p E) :=
      Nat.card_le_card_of_injective evaluate hevaluate
    _ = Nat.card (rootsOfUnity p E) ^ Nat.card sigma.CharacterWeight := Nat.card_fun
    _ ≤ p ^ Nat.card sigma.CharacterWeight :=
      Nat.pow_le_pow_left (card_rootsOfUnity E p) _
    _ ≤ p ^ 2 := pow_le_pow_right' (Fact.out : p.Prime).one_lt.le hweights2

/-- Every odd-prime rank of GL₂ over a finite field of characteristic two
is at most two, with prime rank defined using abelian generator ranks. -/
public theorem primeRank_le_two_of_odd
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    primeRank p (GL (Fin 2) F) ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le (GL (Fin 2) F)).mpr
  intro A hA
  let := hA
  exact elementaryAbelian_card_le_sq_of_odd F hp A

end Matrix.GeneralLinearGroup
