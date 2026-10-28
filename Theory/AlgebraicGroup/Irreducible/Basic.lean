module

public import Theory.AlgebraicGroup.Connected
public import Theory.AlgebraicGroup.Dimension.Basic

universe u

/-!
Irreducibility and integral-domain criteria for presented varieties and algebraic groups.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

public theorem isPrime_of_isDomain_coordinateRing (V : Variety k)
    (h : IsDomain (coordinateRing V)) :
    (vanishingIdeal (Set.univ : Set (Variety.Point V))).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime (I := vanishingIdeal (Set.univ : Set (Variety.Point V)))).mp h

/-- A prime vanishing ideal makes its zero locus irreducible: the zero locus
of a prime ideal is an irreducible closed set. -/
public theorem isIrreducible_zeroLocus_of_isPrime (V : Variety k)
    {S : Set (Variety.Point V)} (_hS : IsZariskiClosed V S)
    (hI : (vanishingIdeal S).IsPrime) :
    IsIrreducible S := by
  have hnonempty : S.Nonempty := by
    by_contra h
    have : S = ∅ := by
      ext x
      simp
      intro hx
      exact h ⟨x, hx⟩
    have htop : vanishingIdeal S = ⊤ := by
      ext p
      constructor
      · intro hp; simp
      · intro hp x hx; exact False.elim (h ⟨x, hx⟩)
    exact hI.1 htop
  refine ⟨hnonempty, ?_⟩
  intro u v hu hv hSu hSv
  by_contra h
  have hsub : S ⊆ uᶜ ∪ vᶜ := by
    intro x hx
    by_contra hxuv
    have hxu : x ∈ u := by
      by_contra hxu'
      exact hxuv (Or.inl hxu')
    have hxv : x ∈ v := by
      by_contra hxv'
      exact hxuv (Or.inr hxv')
    exact h ⟨x, ⟨hx, ⟨hxu, hxv⟩⟩⟩
  let A := uᶜ
  let B := vᶜ
  have hAz : IsZariskiClosed V A :=
    Variety.isClosed_iff_isZariskiClosed.mp hu.isClosed_compl
  have hBz : IsZariskiClosed V B :=
    Variety.isClosed_iff_isZariskiClosed.mp hv.isClosed_compl
  rcases hAz with ⟨J, hJ⟩
  rcases hBz with ⟨K, hK⟩
  have hJI : J ≤ vanishingIdeal S ∨ K ≤ vanishingIdeal S := by
    by_contra h'
    have hJInot : ¬ ∀ p, p ∈ J → p ∈ vanishingIdeal S := by
      intro hpall
      exact h' (Or.inl (by intro p hp; exact hpall p hp))
    have hJex : ∃ p, p ∈ J ∧ p ∉ vanishingIdeal S := by
      by_contra hne
      apply hJInot
      intro p hp
      by_contra hpI
      exact hne ⟨p, hp, hpI⟩
    have hKInot : ¬ ∀ q, q ∈ K → q ∈ vanishingIdeal S := by
      intro hqall
      exact h' (Or.inr (by intro q hq; exact hqall q hq))
    have hKex : ∃ q, q ∈ K ∧ q ∉ vanishingIdeal S := by
      by_contra hne
      apply hKInot
      intro q hq
      by_contra hqI
      exact hne ⟨q, hq, hqI⟩
    rcases hJex with ⟨p, hpJ, hpI⟩
    rcases hKex with ⟨q, hqK, hqI⟩
    have hpq : p * q ∈ vanishingIdeal S := by
      intro x hx
      have hxAB : x ∈ A ∪ B := hsub hx
      rcases hxAB with hxA | hxB
      · have hpzero : evalPolynomial x.val p = 0 := by
          have hJx : x ∈ {x | ∀ p ∈ J, evalPolynomial x.val p = 0} := by
            simpa [hJ, A] using hxA
          exact hJx p hpJ
        rw [show evalPolynomial x.val (p * q) =
            evalPolynomial x.val p * evalPolynomial x.val q by
          simp [evalPolynomial]]
        rw [hpzero]
        simp
      · have hqzero : evalPolynomial x.val q = 0 := by
          have hKx : x ∈ {x | ∀ p ∈ K, evalPolynomial x.val p = 0} := by
            simpa [hK, B] using hxB
          exact hKx q hqK
        rw [show evalPolynomial x.val (p * q) =
            evalPolynomial x.val p * evalPolynomial x.val q by
          simp [evalPolynomial]]
        rw [hqzero]
        simp
    rcases hI.2 hpq with hpI' | hqI'
    · exact hpI hpI'
    · exact hqI hqI'
  rcases hJI with hJle | hKle
  · have hsubset : S ⊆ A := by
      intro x hx
      have hxJ : ∀ p ∈ J, evalPolynomial x.val p = 0 := by
        intro p hpJ
        exact (hJle hpJ) x hx
      simpa [hJ, A] using hxJ
    rcases hSu with ⟨x, hx, hxu⟩
    have : x ∈ A := hsubset hx
    exact (this hxu).elim
  · have hsubset : S ⊆ B := by
      intro x hx
      have hxK : ∀ p ∈ K, evalPolynomial x.val p = 0 := by
        intro p hpK
        exact (hKle hpK) x hx
      simpa [hK, B] using hxK
    rcases hSv with ⟨x, hx, hxv⟩
    have : x ∈ B := hsubset hx
    exact (this hxv).elim

/-- Proposition 1.1.4(f), the direction `irreducible → domain`: if the
rational point space is irreducible, the coordinate ring is an integral
domain. -/
public theorem irreducibleVariety_coordinateRing_domain (G : Variety k) [AlgebraicGroup G]
    (h : IsIrreducible (Set.univ : Set (Variety.Point G))) :
    IsDomain (coordinateRing G) :=
  isDomain_coordinateRing_of_isIrreducible G h

/-- Every polynomial is the finite sum of its monomials, with the degree index
restricted to a given set `D` containing the support. -/
public lemma polynomial_eq_sum_monomial (σ : Type*) (p : MvPolynomial σ k) (D : Finset (σ →₀ ℕ))
    (hD : ∀ d, d ∈ p.support → d ∈ D) :
    p = ∑ d ∈ D, MvPolynomial.coeff d p • MvPolynomial.monomial d (1 : k) := by
  calc
    p = ∑ v ∈ p.support, MvPolynomial.monomial v (MvPolynomial.coeff v p) := MvPolynomial.as_sum p
    _ = ∑ v ∈ p.support, MvPolynomial.coeff v p • MvPolynomial.monomial v (1 : k) := by
        apply Finset.sum_congr rfl
        intro d hd
        calc
          MvPolynomial.monomial d (MvPolynomial.coeff d p)
              = MvPolynomial.monomial d (MvPolynomial.coeff d p • (1 : k)) := by congr 1; simp
          _ = MvPolynomial.coeff d p • MvPolynomial.monomial d (1 : k) :=
              (MvPolynomial.monomial d).map_smul (MvPolynomial.coeff d p) (1 : k)
    _ = ∑ d ∈ D, MvPolynomial.coeff d p • MvPolynomial.monomial d (1 : k) := by
        exact (Finset.sum_subset hD (by
          intro d hd hd'
          have hz : MvPolynomial.coeff d p = 0 := by
            by_contra hz
            exact hd' ((MvPolynomial.mem_support_iff).mpr hz)
          simp [hz]))

public theorem isIrreducible_univ_of_prime_vanishingIdeal (V : Variety k)
    [Nonempty (Variety.Point V)]
    (hI : (vanishingIdeal (Set.univ : Set (Variety.Point V))).IsPrime) :
    IsIrreducible (Set.univ : Set (Variety.Point V)) := by
  refine ⟨Set.univ_nonempty, ?_⟩
  intro u v hu hv huniv vuniv
  by_contra h
  have hsub : (Set.univ : Set (Variety.Point V)) ⊆ uᶜ ∪ vᶜ := by
    intro x hx
    by_contra hxuv
    have hxu : x ∈ u := by
      by_contra hxu'
      exact hxuv (Or.inl hxu')
    have hxv : x ∈ v := by
      by_contra hxv'
      exact hxuv (Or.inr hxv')
    exact h ⟨x, ⟨hx, ⟨hxu, hxv⟩⟩⟩
  let A := uᶜ
  let B := vᶜ
  have hAz : IsZariskiClosed V A :=
    Variety.isClosed_iff_isZariskiClosed.mp hu.isClosed_compl
  have hBz : IsZariskiClosed V B :=
    Variety.isClosed_iff_isZariskiClosed.mp hv.isClosed_compl
  rcases hAz with ⟨J, hJ⟩
  rcases hBz with ⟨K, hK⟩
  have hclosedUniv : IsZariskiClosed V (Set.univ : Set (Variety.Point V)) :=
    ⟨∅, by ext x; simp⟩
  have hJI : J ≤ vanishingIdeal (Set.univ : Set (Variety.Point V)) ∨
      K ≤ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
    by_contra h'
    have hJInot : ¬ ∀ p, p ∈ J → p ∈ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      intro hpall
      exact h' (Or.inl (by intro p hp; exact hpall p hp))
    have hJex : ∃ p, p ∈ J ∧ p ∉ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      by_contra hne
      apply hJInot
      intro p hp
      by_contra hpI
      exact hne ⟨p, hp, hpI⟩
    have hKInot : ¬ ∀ q, q ∈ K → q ∈ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      intro hqall
      exact h' (Or.inr (by intro q hq; exact hqall q hq))
    have hKex : ∃ q, q ∈ K ∧ q ∉ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      by_contra hne
      apply hKInot
      intro q hq
      by_contra hqI
      exact hne ⟨q, hq, hqI⟩
    rcases hJex with ⟨p, hpJ, hpI⟩
    rcases hKex with ⟨q, hqK, hqI⟩
    have hpq : p * q ∈ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      intro x hx
      have hxAB : x ∈ A ∪ B := hsub hx
      rcases hxAB with hxA | hxB
      · have hpzero : evalPolynomial x.val p = 0 := by
          have hJx : x ∈ {x | ∀ p ∈ J, evalPolynomial x.val p = 0} := by
            simpa [hJ, A] using hxA
          exact hJx p hpJ
        rw [show evalPolynomial x.val (p * q) =
            evalPolynomial x.val p * evalPolynomial x.val q by
          simp [evalPolynomial]]
        rw [hpzero]
        simp
      · have hqzero : evalPolynomial x.val q = 0 := by
          have hKx : x ∈ {x | ∀ p ∈ K, evalPolynomial x.val p = 0} := by
            simpa [hK, B] using hxB
          exact hKx q hqK
        rw [show evalPolynomial x.val (p * q) =
            evalPolynomial x.val p * evalPolynomial x.val q by
          simp [evalPolynomial]]
        rw [hqzero]
        simp
    rcases hI.2 hpq with hpI' | hqI'
    · exact hpI hpI'
    · exact hqI hqI'
  rcases hJI with hJle | hKle
  · have hsubset : (Set.univ : Set (Variety.Point V)) ⊆ A := by
      intro x hx
      have hxV : x ∈ {x : Variety.Point V |
          ∀ p ∈ vanishingIdeal (Set.univ : Set (Variety.Point V)), evalPolynomial x.val p = 0} := by
        rw [zeroLocus_vanishingIdeal (V := V) (S := Set.univ) hclosedUniv]
        exact hx
      have hxJ : ∀ p ∈ J, evalPolynomial x.val p = 0 := by
        intro p hpJ
        exact hxV p (hJle hpJ)
      simpa [hJ, A] using hxJ
    rcases huniv with ⟨x, hx, hxu⟩
    have : x ∈ A := hsubset hx
    exact (this hxu).elim
  · have hsubset : (Set.univ : Set (Variety.Point V)) ⊆ B := by
      intro x hx
      have hxV : x ∈ {x : Variety.Point V |
          ∀ p ∈ vanishingIdeal (Set.univ : Set (Variety.Point V)), evalPolynomial x.val p = 0} := by
        rw [zeroLocus_vanishingIdeal (V := V) (S := Set.univ) hclosedUniv]
        exact hx
      have hxK : ∀ p ∈ K, evalPolynomial x.val p = 0 := by
        intro p hpK
        exact hxV p (hKle hpK)
      simpa [hK, B] using hxK
    rcases vuniv with ⟨x, hx, hxv⟩
    have : x ∈ B := hsubset hx
    exact (this hxv).elim

/-- Proposition 1.1.4(f), the direction `domain → connected`: if the
coordinate ring is an integral domain, the variety is connected. -/
public theorem coordinateRing_domain_variety_connected (V : Variety k)
    [Nonempty (Variety.Point V)] (h : IsDomain (coordinateRing V)) :
    Variety.IsConnected V := by
  have hirr : IsIrreducible (Set.univ : Set (Variety.Point V)) :=
    isIrreducible_univ_of_prime_vanishingIdeal V (isPrime_of_isDomain_coordinateRing V h)
  exact hirr.isConnected

public theorem IsIrreducible.subset_union_of_closed {X : Type*} [TopologicalSpace X]
    {s A B : Set X} (hs : IsIrreducible s)
    (hA : IsClosed A) (hB : IsClosed B) (hsub : s ⊆ A ∪ B) :
    s ⊆ A ∨ s ⊆ B := by
  by_contra h
  push Not at h
  rcases h with ⟨hA', hB'⟩
  rcases (Set.not_subset.mp hA') with ⟨a, ha, haA⟩
  rcases (Set.not_subset.mp hB') with ⟨b, hb, hbB⟩
  rcases hs.2 Aᶜ Bᶜ hA.isOpen_compl hB.isOpen_compl ⟨a, ha, haA⟩ ⟨b, hb, hbB⟩ with
    ⟨t, ht, htAB⟩
  rcases htAB with ⟨htA, htB⟩
  exact (hsub ht).elim htA htB

/-- An irreducible set is contained in some irreducible component. -/
public theorem irreducible_subset_of_contains_component {X : Type*} [TopologicalSpace X]
    {C W : Set X}
    (hC : C ∈ irreducibleComponents X)
    (hCW : C ⊆ W) (hW : IsIrreducible W) :
    W ⊆ C := by
  rcases exists_mem_irreducibleComponents_subset_of_isIrreducible W hW with ⟨C', hC', hWC'⟩
  rcases hC with ⟨hCirr, hCmax⟩
  intro x hx
  exact hCmax hC'.1 (hCW.trans hWC') (hWC' hx)

end Theory.AlgebraicGroup
