module
public import Theory.Character.CyclicThirteenNormalizer
public import Theory.Character.ThirteenPeriods

/-!
# Thirteenth-root periods of the local cubic characters

Evaluating all nonprincipal linear characters at a generator identifies them
with the twelve nontrivial thirteenth roots. The four complement orbits give
a partition into triples, and hence the exact periods used by the ordinary
cyclic-block interfaces. Fourier inversion also gives sum minus one away from
the identity. The final constructor supplies the rows and period witnesses
from the original local Sylow hypotheses.

Source: Alperin--Brauer--Gorenstein, III.8, printed pp.116--117.
-/

public section
noncomputable section
open scoped BigOperators IsMulCommutative
attribute [local instance] Fintype.ofFinite
namespace CyclicThirteenNormalizer
variable {G : Type*} [Group G] [Finite G] {P : Subgroup G}

omit [Finite G] in
private theorem linear_eq_of_generator (hP : Nat.card P = 13) (u : P) (hu : u ≠ 1)
    (χ ψ : P →* ℂ) (he : χ u = ψ u) : χ = ψ := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  ext x
  obtain ⟨n, rfl⟩ := mem_powers_of_prime_card hP (g' := x) hu
  simp only [map_pow, he]

/-- At a generator the four restriction sums partition the twelve nontrivial
thirteenth roots into four triples. -/
theorem Rows.exists_periods (s : Rows P) (hP : Nat.card P = 13) :
    ∃ (u : P) (ζ : ℂ) (a : Fin 4 × Fin 3 ≃ Fin 12),
      u ≠ 1 ∧ IsPrimitiveRoot ζ 13 ∧
      (∀ i : Fin 4, s.chi i (ConjClasses.mk (inclusion P u)) =
        ThirteenPeriods.period ζ a i) := by
  classical
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  rw [hP] at hu
  have hune : u ≠ 1 := by intro h; simp [h] at hu
  let ζ := s.linear 0 u
  have hζ : IsPrimitiveRoot ζ 13 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact (orderOf_injective (s.linear 0)
      (CyclicThirteenOrbits.linear_injective hP _ (s.linear_ne_one 0)) u).trans hu
  let e3 : Three ≃ Fin 3 := (Finite.equivFin Three).trans
    (finCongr (by simp [Three, Nat.card_eq_fintype_card]))
  let θ (q : Fin 4 × Fin 3) : P →* ℂ :=
    (s.linear q.1).comp (s.action (e3.symm q.2)).toMonoidHom
  have hθ (q : Fin 4 × Fin 3) : θ q ≠ 1 := by
    intro he
    apply s.linear_ne_one q.1
    ext x
    have hh := DFunLike.congr_fun he ((s.action (e3.symm q.2)).symm x)
    simpa [θ] using hh
  have hpow (q : Fin 4 × Fin 3) : θ q u ^ 13 = 1 := by
    rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  have hexp (q : Fin 4 × Fin 3) : ∃ n : ℕ, 0 < n ∧ n < 13 ∧ ζ ^ n = θ q u := by
    obtain ⟨n, hn, he⟩ := hζ.eq_pow_of_pow_eq_one (hpow q)
    refine ⟨n, ?_, hn, he⟩
    by_contra hz
    have hn0 : n = 0 := by omega
    have hone : θ q u = 1 := by simpa [hn0] using he.symm
    exact hθ q (linear_eq_of_generator hP u hune (θ q) 1 hone)
  choose n hnpos hnlt hn using hexp
  let f : Fin 4 × Fin 3 → Fin 12 := fun q => ⟨n q - 1, by have := hnlt q; omega⟩
  have hf : Function.Injective f := by
    intro q r hqr
    have hnqr : n q = n r := by
      have := congrArg Fin.val hqr
      change n q - 1 = n r - 1 at this
      have := hnpos q
      have := hnpos r
      omega
    have he : θ q = θ r := linear_eq_of_generator hP u hune _ _
      ((hn q).symm.trans (by rw [hnqr, hn r]))
    have hpair : (q.1, e3.symm q.2) = (r.1, e3.symm r.2) := s.orbit_injective he
    have hparts := Prod.mk.inj hpair
    exact Prod.ext hparts.1 (e3.symm.injective hparts.2)
  let a : Fin 4 × Fin 3 ≃ Fin 12 := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp⟩)
  refine ⟨u, ζ, a, hune, hζ, ?_⟩
  intro i
  rw [s.restriction]
  rw [← e3.symm.sum_comp (fun b => s.linear i (s.action b u))]
  apply Finset.sum_congr rfl
  intro j _
  change θ (i,j) u = ζ ^ ((n (i,j) - 1) + 1)
  rw [Nat.sub_add_cancel (hnpos (i,j)), hn]

/-- The sum of all four local cubic rows is minus one at every nonidentity
Sylow element. This follows from exhaustion of the nonprincipal Fourier rows. -/
theorem Rows.sum_restriction (s : Rows P) (hP : Nat.card P = 13) (u : P) (hu : u ≠ 1) :
    ∑ i : Fin 4, s.chi i (ConjClasses.mk (inclusion P u)) = -1 := by
  classical
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let X := {ψ : P →* ℂ // ψ ≠ 1}
  have hn (q : Fin 4 × Three) : (s.linear q.1).comp (s.action q.2).toMonoidHom ≠ 1 := by
    intro hh
    apply s.linear_ne_one q.1
    ext x
    simpa using DFunLike.congr_fun hh ((s.action q.2).symm x)
  let f : Fin 4 × Three → X := fun q => ⟨_, hn q⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r hh
      exact s.orbit_injective (congrArg Subtype.val hh)
    · intro ψ
      obtain ⟨i,a,ha⟩ := s.orbit_covers ψ.val ψ.property
      exact ⟨(i,a), Subtype.ext ha⟩
  let e := Equiv.ofBijective f hf
  have hsum : (∑ ψ : X, ψ.val u) = -1 := by
    have hh := AbelianLinearCharacters.sum_apply u
    rw [if_neg hu] at hh
    have hs := Fintype.sum_subtype_add_sum_subtype (fun ψ : P →* ℂ => ψ ≠ 1)
      (fun ψ => ψ u)
    have hone : (∑ ψ : {ψ : P →* ℂ // ¬ψ ≠ 1}, ψ.val u) = 1 := by
      have he : (fun ψ : {ψ : P →* ℂ // ¬ψ ≠ 1} => ψ.val u) = fun _ => (1 : ℂ) := by
        funext ψ
        rw [not_not.mp ψ.property]
        rfl
      rw [he]
      simp
    rw [hone, hh] at hs
    exact eq_neg_of_add_eq_zero_left hs
  simp_rw [s.restriction]
  rw [← Fintype.sum_prod_type (fun q : Fin 4 × Three => s.linear q.1 (s.action q.2 u))]
  calc
    _ = ∑ ψ : X, ψ.val u := e.sum_comp (fun ψ : X => ψ.val u)
    _ = -1 := hsum

/-- The local rows with the root and period coordinates used by the ordinary
cyclic-block construction. -/
structure PeriodRows (P : Subgroup G) extends Rows P where
  generator : P
  generator_ne_one : generator ≠ 1
  root : ℂ
  root_primitive : IsPrimitiveRoot root 13
  periods : Fin 4 × Fin 3 ≃ Fin 12
  period_value : ∀ i : Fin 4, chi i (ConjClasses.mk (inclusion P generator)) =
    ThirteenPeriods.period root periods i

/-- Construct the period coordinates along with the actual local rows. -/
theorem nonempty_periodRows (P : Subgroup G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = P)
    (hindex : P.relIndex (Normalizer P) = 3) : Nonempty (PeriodRows P) := by
  obtain ⟨s⟩ := nonempty_rows P hP hC hindex
  obtain ⟨u, ζ, a, hu, hζ, hv⟩ := s.exists_periods hP
  exact ⟨{
    toRows := s
    generator := u
    generator_ne_one := hu
    root := ζ
    root_primitive := hζ
    periods := a
    period_value := hv }⟩

/-- Entry point in the Sylow and automizer-index form: self-centralization
identifies the automizer index with the index of P in its normalizer. -/
theorem sylow_normalizer_data (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 3) :
    Nat.card (Normalizer (P : Subgroup G)) = 39 ∧
      Nonempty (PeriodRows (P : Subgroup G)) := by
  rw [hC] at hindex
  exact ⟨normalizer_card (P : Subgroup G) hP hindex,
    nonempty_periodRows (P : Subgroup G) hP hC hindex⟩

end CyclicThirteenNormalizer
