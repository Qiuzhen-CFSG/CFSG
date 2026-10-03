module
public import Theory.Character.CyclicSevenNormalizer
public import Theory.Character.SevenPeriods

/-!
# Seventh-root periods of the local quadratic characters

Evaluating all nonprincipal linear characters at a generator identifies them
with the six nontrivial seventh roots. The three complement orbits give
a partition into pairs, and hence the exact periods used by the ordinary
cyclic-block interfaces. Fourier inversion also gives sum minus one away from
the identity. The final constructor supplies the rows and period witnesses
from the original local Sylow hypotheses.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.Character.CyclicThirteenNormalizerPeriods`,
whose source is Alperin--Brauer--Gorenstein, III.8, pp.116--117.
-/

public section
noncomputable section
open scoped BigOperators IsMulCommutative
attribute [local instance] Fintype.ofFinite
namespace CyclicSevenNormalizer
variable {G : Type*} [Group G] [Finite G] {P : Subgroup G}

omit [Finite G] in
private theorem linear_eq_of_generator (hP : Nat.card P = 7) (u : P) (hu : u ≠ 1)
    (χ ψ : P →* ℂ) (he : χ u = ψ u) : χ = ψ := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  ext x
  obtain ⟨n, rfl⟩ := mem_powers_of_prime_card hP (g' := x) hu
  simp only [map_pow, he]

/-- At a generator the three restriction sums partition the six nontrivial
seventh roots into three pairs. -/
theorem Rows.exists_periods (s : Rows P) (hP : Nat.card P = 7) :
    ∃ (u : P) (ζ : ℂ) (a : Fin 3 × Fin 2 ≃ Fin 6),
      u ≠ 1 ∧ IsPrimitiveRoot ζ 7 ∧
      (∀ i : Fin 3, s.chi i (ConjClasses.mk (inclusion P u)) =
        SevenPeriods.period ζ a i) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  rw [hP] at hu
  have hune : u ≠ 1 := by intro h; simp [h] at hu
  let ζ := s.linear 0 u
  have hζ : IsPrimitiveRoot ζ 7 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact (orderOf_injective (s.linear 0)
      (CyclicSevenOrbits.linear_injective hP _ (s.linear_ne_one 0)) u).trans hu
  let e2 : Two ≃ Fin 2 := (Finite.equivFin Two).trans
    (finCongr (by simp [Two, Nat.card_eq_fintype_card]))
  let θ (q : Fin 3 × Fin 2) : P →* ℂ :=
    (s.linear q.1).comp (s.action (e2.symm q.2)).toMonoidHom
  have hθ (q : Fin 3 × Fin 2) : θ q ≠ 1 := by
    intro he
    apply s.linear_ne_one q.1
    ext x
    have hh := DFunLike.congr_fun he ((s.action (e2.symm q.2)).symm x)
    simpa [θ] using hh
  have hpow (q : Fin 3 × Fin 2) : θ q u ^ 7 = 1 := by
    rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  have hexp (q : Fin 3 × Fin 2) : ∃ n : ℕ, 0 < n ∧ n < 7 ∧ ζ ^ n = θ q u := by
    obtain ⟨n, hn, he⟩ := hζ.eq_pow_of_pow_eq_one (hpow q)
    refine ⟨n, ?_, hn, he⟩
    by_contra hz
    have hn0 : n = 0 := by omega
    have hone : θ q u = 1 := by simpa [hn0] using he.symm
    exact hθ q (linear_eq_of_generator hP u hune (θ q) 1 hone)
  choose n hnpos hnlt hn using hexp
  let f : Fin 3 × Fin 2 → Fin 6 := fun q => ⟨n q - 1, by have := hnlt q; omega⟩
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
    have hpair : (q.1, e2.symm q.2) = (r.1, e2.symm r.2) := s.orbit_injective he
    have hparts := Prod.mk.inj hpair
    exact Prod.ext hparts.1 (e2.symm.injective hparts.2)
  let a : Fin 3 × Fin 2 ≃ Fin 6 := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp⟩)
  refine ⟨u, ζ, a, hune, hζ, ?_⟩
  intro i
  rw [s.restriction]
  rw [← e2.symm.sum_comp (fun b => s.linear i (s.action b u))]
  apply Finset.sum_congr rfl
  intro j _
  change θ (i,j) u = ζ ^ ((n (i,j) - 1) + 1)
  rw [Nat.sub_add_cancel (hnpos (i,j)), hn]

/-- The sum of all three local quadratic rows is minus one at every nonidentity
Sylow element. This follows from exhaustion of the nonprincipal Fourier rows. -/
theorem Rows.sum_restriction (s : Rows P) (hP : Nat.card P = 7) (u : P) (hu : u ≠ 1) :
    ∑ i : Fin 3, s.chi i (ConjClasses.mk (inclusion P u)) = -1 := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let X := {ψ : P →* ℂ // ψ ≠ 1}
  have hn (q : Fin 3 × Two) : (s.linear q.1).comp (s.action q.2).toMonoidHom ≠ 1 := by
    intro hh
    apply s.linear_ne_one q.1
    ext x
    simpa using DFunLike.congr_fun hh ((s.action q.2).symm x)
  let f : Fin 3 × Two → X := fun q => ⟨_, hn q⟩
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
  rw [← Fintype.sum_prod_type (fun q : Fin 3 × Two => s.linear q.1 (s.action q.2 u))]
  calc
    _ = ∑ ψ : X, ψ.val u := e.sum_comp (fun ψ : X => ψ.val u)
    _ = -1 := hsum

/-- The local rows with the root and period coordinates used by the ordinary
cyclic-block construction. -/
structure PeriodRows (P : Subgroup G) extends Rows P where
  generator : P
  generator_ne_one : generator ≠ 1
  root : ℂ
  root_primitive : IsPrimitiveRoot root 7
  periods : Fin 3 × Fin 2 ≃ Fin 6
  period_value : ∀ i : Fin 3, chi i (ConjClasses.mk (inclusion P generator)) =
    SevenPeriods.period root periods i

/-- Construct the period coordinates along with the actual local rows. -/
theorem nonempty_periodRows (P : Subgroup G) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = P)
    (hindex : P.relIndex (Normalizer P) = 2) : Nonempty (PeriodRows P) := by
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
theorem sylow_normalizer_data (P : Sylow 7 G) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2) :
    Nat.card (Normalizer (P : Subgroup G)) = 14 ∧
      Nonempty (PeriodRows (P : Subgroup G)) := by
  rw [hC] at hindex
  exact ⟨normalizer_card (P : Subgroup G) hP hindex,
    nonempty_periodRows (P : Subgroup G) hP hC hindex⟩

end CyclicSevenNormalizer
