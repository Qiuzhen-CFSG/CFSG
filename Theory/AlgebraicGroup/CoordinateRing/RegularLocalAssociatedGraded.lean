module

public import Theory.CommutativeAlgebra.AssociatedGraded
public import Theory.CommutativeAlgebra.HilbertSamuelGradedLength
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Leading terms in regular local rings

For a regular local ring `R`, this module proves that the product of elements
of exact maximal-ideal orders `m` and `n` has exact order `m + n`. This is the
leading-term consequence of the polynomial associated-graded description in
Stacks Project, Lemma 10.106.1 (tag 00NO), and is the input used by tag 00NP to
deduce that regular local rings are domains.

The proof presents the maximal-ideal associated graded ring as a quotient of a
polynomial ring on a basis of `m / m²`. If a nonzero homogeneous relation
existed, multiplication by it would force a strict deficit in the dimensions
of all sufficiently high homogeneous pieces. The Hilbert--Samuel degree
theorem contradicts that deficit because regularity identifies the number of
variables with the Krull dimension. Thus nonzero homogeneous leading terms
have nonzero product. The dimension-zero and degree-zero boundary cases use
only primality of the maximal ideal.

The public `HilbertSamuel.regularLocal_associatedGraded_presentation` also
exports the full polynomial presentation without exposing the private
evaluation machinery. Homogeneous decomposition reduces its kernel to the
homogeneous relations excluded above. In embedding dimension zero every
polynomial is constant, and the residue field embeds in the nontrivial graded
ring. The variable count agrees with the minimal number of generators by
the same dimension comparison, or the elementary upper bound in dimension zero.
-/

namespace HilbertSamuel

noncomputable section

open Filter IsLocalRing

set_option linter.style.haveILetI false

private lemma finrank_homogeneousSubmodule
    (K : Type*) [Field K] (d n : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin d) K n) =
      (d + n - 1).choose n := by
  let e : {s : Fin d →₀ ℕ // s.degree = n} ≃
      (Finset.univ.finsuppAntidiag n : Finset (Fin d →₀ ℕ)) :=
    Equiv.setCongr (by
      ext s
      change s.degree = n ↔ s ∈ Finset.univ.finsuppAntidiag n
      rw [show s.degree = ∑ i, s i by
        rw [Finsupp.degree_apply]
        exact Finsupp.sum_fintype s (fun _ x ↦ x) (by simp)]
      simp [Finset.mem_finsuppAntidiag])
  letI : Fintype {s : Fin d →₀ ℕ // s.degree = n} :=
    Fintype.ofEquiv _ e.symm
  let b : Module.Basis {s : Fin d →₀ ℕ // s.degree = n} K
      (MvPolynomial.homogeneousSubmodule (Fin d) K n) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact MvPolynomial.basisRestrictSupport K {s : Fin d →₀ ℕ | s.degree = n}
  rw [Module.finrank_eq_card_basis b]
  rw [Fintype.card_congr e, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ,
    Fintype.card_fin]

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

private abbrev m : Ideal R := maximalIdeal R

private abbrev k := R ⧸ m (R := R)

private noncomputable local instance : Field (k (R := R)) :=
  Ideal.Quotient.field (m (R := R))

private abbrev gr := AssociatedGraded (m (R := R))

private abbrev grPiece (n : ℕ) := AssociatedGradedPiece (m (R := R)) n

private abbrev embDim : ℕ := Module.finrank (k (R := R)) (grPiece (R := R) 1)

private noncomputable def degreeOneBasis :
    Module.Basis (Fin (embDim (R := R))) (k (R := R)) (grPiece (R := R) 1) := by
  letI : Module.Free (k (R := R)) (grPiece (R := R) 1) :=
    Module.Free.of_divisionRing _ _
  letI : Module.Finite (k (R := R)) (grPiece (R := R) 1) :=
    associatedGradedPiece_finite (m (R := R)) 1
  exact Module.finBasis (k (R := R)) (grPiece (R := R) 1)

private noncomputable def grGenerator (i : Fin (embDim (R := R))) : gr (R := R) :=
  associatedGradedOf (m (R := R)) 1 (degreeOneBasis (R := R) i)

private noncomputable def grAeval :
    MvPolynomial (Fin (embDim (R := R))) (k (R := R)) →ₐ[k (R := R)] gr (R := R) :=
  MvPolynomial.aeval (grGenerator (R := R))

private lemma grAeval_surjective : Function.Surjective (grAeval (R := R)) := by
  rw [← AlgHom.range_eq_top]
  change (MvPolynomial.aeval (grGenerator (R := R))).range = ⊤
  rw [← Algebra.adjoin_range_eq_range_aeval]
  apply top_unique
  intro z _
  induction z using DirectSum.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | of n x =>
      rw [← associatedGradedOf_apply]
      apply associatedGradedOf_mem_adjoin
        (m (R := R)) (Set.range (grGenerator (R := R)))
      intro y
      rw [← (degreeOneBasis (R := R)).sum_repr y]
      change associatedGradedOf (m (R := R)) 1
          (∑ i, (degreeOneBasis (R := R)).repr y i •
            degreeOneBasis (R := R) i) ∈ _
      rw [map_sum]
      apply Subalgebra.sum_mem
      intro i _
      rw [(associatedGradedOf (m (R := R)) 1).map_smul]
      exact Subalgebra.smul_mem _
        (Algebra.subset_adjoin (Set.mem_range_self i)) _
  | add x y hx hy => exact Subalgebra.add_mem _ (hx trivial) (hy trivial)

private lemma grAeval_isHomogeneous
    {p : MvPolynomial (Fin (embDim (R := R))) (k (R := R))}
    {n : ℕ} (hp : p.IsHomogeneous n) :
    ∃ x : grPiece (R := R) n,
      grAeval (R := R) p = associatedGradedOf (m (R := R)) n x := by
  exact associatedGraded_aeval_isHomogeneous
    (m (R := R)) (degreeOneBasis (R := R)) hp

private lemma component_grAeval_eq_zero
    {p : MvPolynomial (Fin (embDim (R := R))) (k (R := R))}
    {i j : ℕ} (hp : p.IsHomogeneous i) (hij : i ≠ j) :
    (grAeval (R := R) p) j = 0 := by
  obtain ⟨x, hx⟩ := grAeval_isHomogeneous (R := R) hp
  rw [hx]
  simp [associatedGradedOf_apply, DirectSum.of_apply, hij]

private lemma grAeval_homogeneous_surjective (n : ℕ) (x : grPiece (R := R) n) :
    ∃ p : MvPolynomial (Fin (embDim (R := R))) (k (R := R)),
      p.IsHomogeneous n ∧
        grAeval (R := R) p = associatedGradedOf (m (R := R)) n x := by
  obtain ⟨q, hq⟩ := grAeval_surjective (R := R)
    (associatedGradedOf (m (R := R)) n x)
  let p := MvPolynomial.homogeneousComponent n q
  have hp : p.IsHomogeneous n :=
    MvPolynomial.homogeneousComponent_isHomogeneous n q
  obtain ⟨z, hz⟩ := grAeval_isHomogeneous (R := R) hp
  have hsum :
      (∑ i ∈ Finset.range (q.totalDegree + 1),
          grAeval (R := R) (MvPolynomial.homogeneousComponent i q)) =
        associatedGradedOf (m (R := R)) n x := by
    rw [← hq, ← map_sum, MvPolynomial.sum_homogeneousComponent]
  by_cases hn : n ∈ Finset.range (q.totalDegree + 1)
  · have hcomponent := congrArg
        (fun z : gr (R := R) ↦ z n) hsum
    rw [DirectSum.sum_apply, Finset.sum_eq_single n] at hcomponent
    · rw [hz] at hcomponent
      simp only [associatedGradedOf_apply] at hcomponent
      change (DirectSum.of (grPiece (R := R)) n z) n =
        (DirectSum.of (grPiece (R := R)) n x) n at hcomponent
      simp only [DirectSum.of_eq_same] at hcomponent
      exact ⟨p, hp, hz.trans (congrArg
        (associatedGradedOf (m (R := R)) n) hcomponent)⟩
    · intro i hi hin
      exact component_grAeval_eq_zero (R := R)
        (MvPolynomial.homogeneousComponent_isHomogeneous i q) hin
    · exact fun hnotmem ↦ (hnotmem hn).elim
  · have hcomponent := congrArg
        (fun z : gr (R := R) ↦ z n) hsum
    rw [DirectSum.sum_apply] at hcomponent
    have hleft :
        ∑ i ∈ Finset.range (q.totalDegree + 1),
            (grAeval (R := R) (MvPolynomial.homogeneousComponent i q)) n = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact component_grAeval_eq_zero (R := R)
        (MvPolynomial.homogeneousComponent_isHomogeneous i q)
        (fun hin ↦ hn (hin ▸ hi))
    rw [hleft] at hcomponent
    simp only [associatedGradedOf_apply] at hcomponent
    change 0 = (DirectSum.of (grPiece (R := R)) n x) n at hcomponent
    simp only [DirectSum.of_eq_same] at hcomponent
    subst x
    exact ⟨0, MvPolynomial.isHomogeneous_zero
      (Fin (embDim (R := R))) (k (R := R)) n, by simp⟩

private lemma embDim_le_spanFinrank :
    embDim (R := R) ≤ (m (R := R)).spanFinrank := by
  have hfg : Submodule.FG (m (R := R) : Submodule R R) :=
    IsNoetherian.noetherian _
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hs_mem (a : s) : (a : R) ∈ m (R := R) := by
    rw [← hspan]
    exact Submodule.subset_span a.property
  let f : s → grPiece (R := R) 1 := fun a ↦
    associatedGradedDegreeOneClass (m (R := R)) ⟨a, hs_mem a⟩
  have htop : Submodule.span (k (R := R)) (Set.range f) = ⊤ := by
    apply top_unique
    intro x _
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        have hx : (x : R) ∈ Submodule.span R (s : Set R) := by
          rw [hspan]
          simpa only [pow_one] using x.property
        refine Submodule.span_induction (s := (s : Set R))
          (p := fun y hy ↦
            associatedGradedDegreeOneClass (m (R := R))
                ⟨y, by rw [← hspan]; exact hy⟩ ∈
              Submodule.span (k (R := R)) (Set.range f)) ?_ ?_ ?_ ?_ hx
        · intro y hy
          apply Submodule.subset_span
          exact ⟨⟨y, hy⟩, rfl⟩
        · change (0 : grPiece (R := R) 1) ∈
            Submodule.span (k (R := R)) (Set.range f)
          exact Submodule.zero_mem _
        · intro y z hy hz ihy ihz
          change associatedGradedDegreeOneClass (m (R := R))
                ⟨y, by rw [← hspan]; exact hy⟩ +
              associatedGradedDegreeOneClass (m (R := R))
                ⟨z, by rw [← hspan]; exact hz⟩ ∈
            Submodule.span (k (R := R)) (Set.range f)
          exact Submodule.add_mem _ ihy ihz
        · intro r y hy ihy
          change Ideal.Quotient.mk (m (R := R)) r •
              associatedGradedDegreeOneClass (m (R := R))
                ⟨y, by rw [← hspan]; exact hy⟩ ∈
            Submodule.span (k (R := R)) (Set.range f)
          exact Submodule.smul_mem _ _ ihy
  calc
    embDim (R := R) = Module.finrank (k (R := R))
        (Submodule.span (k (R := R)) (Set.range f)) := by
      rw [htop, finrank_top]
    _ ≤ Fintype.card s := finrank_range_le_card f
    _ = s.card := Fintype.card_coe s
    _ = (m (R := R)).spanFinrank := hcard

private abbrev polyPiece (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule
    (Fin (embDim (R := R))) (k (R := R)) n

private noncomputable def grAevalPiece (n : ℕ) :
    polyPiece (R := R) n →ₗ[k (R := R)] grPiece (R := R) n :=
  (associatedGradedProjection (m (R := R)) n).comp
    ((grAeval (R := R)).toLinearMap.domRestrict (polyPiece (R := R) n))

private lemma grAevalPiece_surjective (n : ℕ) :
    Function.Surjective (grAevalPiece (R := R) n) := by
  intro x
  obtain ⟨p, hp, hmap⟩ := grAeval_homogeneous_surjective (R := R) n x
  refine ⟨⟨p, (MvPolynomial.mem_homogeneousSubmodule n p).mpr hp⟩, ?_⟩
  change associatedGradedProjection (m (R := R)) n
      (grAeval (R := R) p) = x
  rw [hmap, associatedGradedProjection_of]

private def polyPieceMul
    {r : MvPolynomial (Fin (embDim (R := R))) (k (R := R))} {e : ℕ}
    (hr : r.IsHomogeneous e) (t : ℕ) :
    polyPiece (R := R) t →ₗ[k (R := R)] polyPiece (R := R) (t + e) where
  toFun p := ⟨p * r, p.property.mul hr⟩
  map_add' p q := Subtype.ext (add_mul (p : MvPolynomial _ _) q r)
  map_smul' c p := Subtype.ext
    (smul_mul_assoc c (p : MvPolynomial _ _) r)

private lemma polyPieceMul_injective
    {r : MvPolynomial (Fin (embDim (R := R))) (k (R := R))} {e : ℕ}
    (hr : r.IsHomogeneous e) (hr0 : r ≠ 0) (t : ℕ) :
    Function.Injective (polyPieceMul (R := R) hr t) := by
  intro p q hpq
  apply Subtype.ext
  exact mul_right_cancel₀ hr0 (congrArg Subtype.val hpq)

private lemma polyPieceMul_range_le_ker
    {r : MvPolynomial (Fin (embDim (R := R))) (k (R := R))} {e : ℕ}
    (hr : r.IsHomogeneous e) (hker : grAeval (R := R) r = 0) (t : ℕ) :
    LinearMap.range (polyPieceMul (R := R) hr t) ≤
      LinearMap.ker (grAevalPiece (R := R) (t + e)) := by
  rintro _ ⟨p, rfl⟩
  rw [LinearMap.mem_ker]
  change associatedGradedProjection (m (R := R)) (t + e)
      (grAeval (R := R) (p * r)) = 0
  rw [map_mul, hker, mul_zero, map_zero]

private lemma graded_finrank_add_le_of_relation
    {r : MvPolynomial (Fin (embDim (R := R))) (k (R := R))} {e : ℕ}
    (hr : r.IsHomogeneous e) (hr0 : r ≠ 0)
    (hker : grAeval (R := R) r = 0) (t : ℕ) :
    Module.finrank (k (R := R)) (grPiece (R := R) (t + e)) +
        Module.finrank (k (R := R)) (polyPiece (R := R) t) ≤
      Module.finrank (k (R := R)) (polyPiece (R := R) (t + e)) := by
  letI : Module.Finite (k (R := R)) (grPiece (R := R) (t + e)) :=
    associatedGradedPiece_finite (m (R := R)) (t + e)
  letI : Module.Finite (k (R := R)) (polyPiece (R := R) t) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg
      (Fin (embDim (R := R))) (k (R := R)) t)
  letI : Module.Finite (k (R := R)) (polyPiece (R := R) (t + e)) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg
      (Fin (embDim (R := R))) (k (R := R)) (t + e))
  let μ := polyPieceMul (R := R) hr t
  have hμ : Function.Injective μ := polyPieceMul_injective (R := R) hr hr0 t
  have hφ : Function.Surjective (grAevalPiece (R := R) (t + e)) :=
    grAevalPiece_surjective (R := R) (t + e)
  obtain ⟨s, hs⟩ :=
    (grAevalPiece (R := R) (t + e)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hφ)
  have hφμ (x : polyPiece (R := R) t) :
      grAevalPiece (R := R) (t + e) (μ x) = 0 := by
    have hx := polyPieceMul_range_le_ker (R := R) hr hker t
      (show μ x ∈ LinearMap.range μ from ⟨x, rfl⟩)
    rw [LinearMap.mem_ker] at hx
    exact hx
  have hs_apply (x : grPiece (R := R) (t + e)) :
      grAevalPiece (R := R) (t + e) (s x) = x := by
    exact LinearMap.congr_fun hs x
  let F := LinearMap.coprod μ s
  have hF : Function.Injective F := by
    rintro x y hxy
    have hsecond : x.2 = y.2 := by
      have h := congrArg (grAevalPiece (R := R) (t + e)) hxy
      simp only [F, LinearMap.coprod_apply, map_add] at h
      rw [hφμ, hφμ, hs_apply, hs_apply, zero_add, zero_add] at h
      exact h
    have hfirst : x.1 = y.1 := by
      apply hμ
      have h := hxy
      simp only [F, LinearMap.coprod_apply] at h
      rw [hsecond] at h
      exact add_right_cancel h
    exact Prod.ext hfirst hsecond
  have hfinrank := LinearMap.finrank_le_finrank_of_injective hF
  have hprodRank := rank_add_rank_le_rank_prod (k (R := R))
    (polyPiece (R := R) t) (M₁ := grPiece (R := R) (t + e))
  have hprod : Module.finrank (k (R := R)) (polyPiece (R := R) t) +
      Module.finrank (k (R := R)) (grPiece (R := R) (t + e)) ≤
        Module.finrank (k (R := R))
          (polyPiece (R := R) t × grPiece (R := R) (t + e)) := by
    have hprodCard :
      (Module.finrank (k (R := R)) (polyPiece (R := R) t) : Cardinal) +
          Module.finrank (k (R := R)) (grPiece (R := R) (t + e)) ≤
        Module.finrank (k (R := R))
          (polyPiece (R := R) t × grPiece (R := R) (t + e)) := by
      rw [Module.finrank_eq_rank, Module.finrank_eq_rank,
        Module.finrank_eq_rank]
      exact hprodRank
    exact_mod_cast hprodCard
  omega

private lemma maximalIdealGradedLength_eq_finrank (n : ℕ) :
    maximalIdealGradedLength R n =
      (Module.finrank (k (R := R)) (grPiece (R := R) n) : ℤ) := by
  letI : Module.Finite (k (R := R)) (grPiece (R := R) n) :=
    associatedGradedPiece_finite (m (R := R)) n
  rw [maximalIdealGradedLength]
  change ((Module.length R (grPiece (R := R) n)).toNat : ℤ) = _
  rw [Module.length_eq_of_surjective
    (R := k (R := R)) (S := R) (M := grPiece (R := R) n)
    Ideal.Quotient.mk_surjective]
  rw [Module.length_eq_finrank]
  simp

private lemma grPiece_finrank_le_polyPiece_finrank (n : ℕ) :
    Module.finrank (k (R := R)) (grPiece (R := R) n) ≤
      Module.finrank (k (R := R)) (polyPiece (R := R) n) := by
  letI : Module.Finite (k (R := R)) (polyPiece (R := R) n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg
      (Fin (embDim (R := R))) (k (R := R)) n)
  exact LinearMap.finrank_le_finrank_of_surjective
    (grAevalPiece_surjective (R := R) n)

private lemma preHilbertPoly_eval_eq_polyPiece_finrank
    (hE : 0 < embDim (R := R)) (n : ℕ) :
    (Polynomial.preHilbertPoly ℚ (embDim (R := R) - 1) 0).eval (n : ℚ) =
      Module.finrank (k (R := R)) (polyPiece (R := R) n) := by
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le n),
    Nat.sub_zero, finrank_homogeneousSubmodule]
  norm_cast
  have htop : n + (embDim (R := R) - 1) =
      embDim (R := R) + n - 1 := by omega
  rw [← htop]
  exact Nat.choose_symm_add.symm

private lemma preHilbertPoly_ne_zero (E : ℕ) :
    Polynomial.preHilbertPoly ℚ E 0 ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mp
  rw [Polynomial.leadingCoeff_preHilbertPoly]
  exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero E)

private lemma embDim_eq_dimension_succ (d : ℕ)
    (hd : ringKrullDim R = d + 1) : embDim (R := R) = d + 1 := by
  have hspan : (m (R := R)).spanFinrank = d + 1 := by
    have hregular := (isRegularLocalRing_iff R).mp (inferInstance : IsRegularLocalRing R)
    rw [hd] at hregular
    exact_mod_cast hregular
  have hupper : embDim (R := R) ≤ d + 1 := by
    rw [← hspan]
    exact embDim_le_spanFinrank (R := R)
  obtain ⟨P, hP0, hPdegree, hPrep⟩ :=
    maximalIdealGradedLength_hasDegree_of_dimension_succ R d hd
  have hEpos : 0 < embDim (R := R) := by
    by_contra hE
    have hE0 : embDim (R := R) = 0 := Nat.eq_zero_of_not_pos hE
    have hgradedZero : ∀ᶠ n : ℕ in atTop,
        maximalIdealGradedLength R n = 0 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hle := grPiece_finrank_le_polyPiece_finrank (R := R) n
      rw [finrank_homogeneousSubmodule, hE0] at hle
      have hchoose : (n - 1).choose n = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp only [zero_add, hchoose] at hle
      rw [maximalIdealGradedLength_eq_finrank]
      exact_mod_cast (Nat.eq_zero_of_le_zero hle)
    have hzeroRep : NumericalPolynomial.EventuallyRepresents 0
        (maximalIdealGradedLength R) := by
      rw [NumericalPolynomial.EventuallyRepresents]
      filter_upwards [hgradedZero] with n hn
      rw [hn]
      simp
    exact hP0 (NumericalPolynomial.EventuallyRepresents.unique hPrep hzeroRep)
  let H := Polynomial.preHilbertPoly ℚ (embDim (R := R) - 1) 0
  have hH0 : H ≠ 0 := preHilbertPoly_ne_zero (embDim (R := R) - 1)
  have hbound : ∀ᶠ n : ℕ in atTop,
      |P.eval (n : ℚ)| ≤ H.eval (n : ℚ) := by
    filter_upwards [hPrep] with n hn
    rw [hn, maximalIdealGradedLength_eq_finrank]
    rw [abs_of_nonneg (by positivity)]
    change (Module.finrank (k (R := R)) (grPiece (R := R) n) : ℚ) ≤ _
    rw [show H = Polynomial.preHilbertPoly ℚ (embDim (R := R) - 1) 0 from rfl,
      preHilbertPoly_eval_eq_polyPiece_finrank (R := R) hEpos n]
    exact_mod_cast grPiece_finrank_le_polyPiece_finrank (R := R) n
  have hdegree := NumericalPolynomial.degree_le_of_eventually_abs_eval_le hH0 hbound
  have hlower : d ≤ embDim (R := R) - 1 := by
    have hlower' : (d : WithBot ℕ) ≤
        (embDim (R := R) - 1 : ℕ) := by
      calc
        (d : WithBot ℕ) = P.degree := by
          rw [Polynomial.degree_eq_natDegree hP0, hPdegree]
        _ ≤ H.degree := hdegree
        _ = (embDim (R := R) - 1 : ℕ) := by
          rw [Polynomial.degree_eq_natDegree hH0]
          rw [show H = Polynomial.preHilbertPoly ℚ
            (embDim (R := R) - 1) 0 from rfl,
            Polynomial.natDegree_preHilbertPoly]
    exact_mod_cast hlower'
  omega

private lemma grAeval_ne_zero_of_homogeneous_of_dimension_succ
    (d : ℕ) (hd : ringKrullDim R = d + 1)
    {r : MvPolynomial (Fin (embDim (R := R))) (k (R := R))} {e : ℕ}
    (hr : r.IsHomogeneous e) (hr0 : r ≠ 0) :
    grAeval (R := R) r ≠ 0 := by
  intro hker
  have hE : embDim (R := R) = d + 1 :=
    embDim_eq_dimension_succ (R := R) d hd
  have hEpos : 0 < embDim (R := R) := by omega
  obtain ⟨P, hP0, hPdegree, hPrep⟩ :=
    maximalIdealGradedLength_hasDegree_of_dimension_succ R d hd
  let H := Polynomial.preHilbertPoly ℚ (embDim (R := R) - 1) 0
  let Q := H.taylor (e : ℚ) - H
  have hH0 : H ≠ 0 := preHilbertPoly_ne_zero (embDim (R := R) - 1)
  have hQdegree : Q.degree < H.degree := by
    simpa [Q] using
      Polynomial.degree_sub_lt_left
        (Polynomial.degree_taylor H (e : ℚ))
        ((Polynomial.taylor_eq_zero (e : ℚ) H).not.mpr hH0)
        (Polynomial.leadingCoeff_taylor (e : ℚ) H)
  have hPrepShift : NumericalPolynomial.EventuallyRepresents
      (P.taylor (e : ℚ))
      (fun t ↦ maximalIdealGradedLength R (t + e)) := by
    rw [NumericalPolynomial.EventuallyRepresents, eventually_atTop] at hPrep ⊢
    obtain ⟨N, hN⟩ := hPrep
    refine ⟨N, fun t ht ↦ ?_⟩
    rw [Polynomial.taylor_eval,
      show (t : ℚ) + (e : ℚ) = ((t + e : ℕ) : ℚ) by norm_num,
      hN (t + e) (ht.trans (Nat.le_add_right t e))]
  have hbound : ∀ᶠ t : ℕ in atTop,
      |(P.taylor (e : ℚ)).eval (t : ℚ)| ≤ Q.eval (t : ℚ) := by
    filter_upwards [hPrepShift] with t ht
    rw [ht, maximalIdealGradedLength_eq_finrank]
    rw [abs_of_nonneg (by positivity)]
    change (Module.finrank (k (R := R))
      (grPiece (R := R) (t + e)) : ℚ) ≤ _
    rw [show Q = H.taylor (e : ℚ) - H from rfl,
      Polynomial.eval_sub, Polynomial.taylor_eval,
      show (t : ℚ) + (e : ℚ) = ((t + e : ℕ) : ℚ) by norm_num,
      show H = Polynomial.preHilbertPoly ℚ (embDim (R := R) - 1) 0 from rfl,
      preHilbertPoly_eval_eq_polyPiece_finrank (R := R) hEpos (t + e),
      preHilbertPoly_eval_eq_polyPiece_finrank (R := R) hEpos t]
    have hrel := graded_finrank_add_le_of_relation
      (R := R) hr hr0 hker t
    have hrelQ :
        (Module.finrank (k (R := R)) (grPiece (R := R) (t + e)) : ℚ) +
            Module.finrank (k (R := R)) (polyPiece (R := R) t) ≤
          Module.finrank (k (R := R)) (polyPiece (R := R) (t + e)) := by
      exact_mod_cast hrel
    linarith
  by_cases hQ0 : Q = 0
  · have hevalZero : ∀ᶠ t : ℕ in atTop,
        (P.taylor (e : ℚ)).eval (t : ℚ) = 0 := by
      filter_upwards [hbound] with t ht
      rw [hQ0, Polynomial.eval_zero] at ht
      exact abs_eq_zero.mp (le_antisymm ht (abs_nonneg _))
    have hzeroRep : NumericalPolynomial.EventuallyRepresents
        (P.taylor (e : ℚ)) (fun _ : ℕ ↦ 0) := by
      rw [NumericalPolynomial.EventuallyRepresents]
      filter_upwards [hevalZero] with t ht
      simpa using ht
    have hzeroRep' : NumericalPolynomial.EventuallyRepresents
        0 (fun _ : ℕ ↦ 0) := by
      simp [NumericalPolynomial.EventuallyRepresents]
    have htaylorZero : P.taylor (e : ℚ) = 0 :=
      NumericalPolynomial.EventuallyRepresents.unique hzeroRep hzeroRep'
    exact hP0 ((Polynomial.taylor_eq_zero (e : ℚ) P).mp htaylorZero)
  · have hdegree :=
      NumericalPolynomial.degree_le_of_eventually_abs_eval_le hQ0 hbound
    have hequal : (P.taylor (e : ℚ)).degree = H.degree := by
      rw [Polynomial.degree_taylor,
        Polynomial.degree_eq_natDegree hP0,
        Polynomial.degree_eq_natDegree hH0, hPdegree,
        show H = Polynomial.preHilbertPoly ℚ (embDim (R := R) - 1) 0 from rfl,
        Polynomial.natDegree_preHilbertPoly, hE]
      simp
    have hlt : (P.taylor (e : ℚ)).degree < H.degree :=
      hdegree.trans_lt hQdegree
    rw [hequal] at hlt
    exact (lt_irrefl H.degree) hlt

private lemma graded_nontrivial : Nontrivial (gr (R := R)) := by
  let unitClass : grPiece (R := R) 0 := Submodule.Quotient.mk ⟨1, by simp⟩
  have unitClass_ne : unitClass ≠ 0 := by
    intro equality
    have membership := (Submodule.Quotient.mk_eq_zero _).mp equality
    change (1 : R) ∈ maximalIdeal R ^ (0 + 1) at membership
    simp at membership
  exact ⟨⟨associatedGradedOf (m (R := R)) 0 unitClass, 0, fun equality ↦
    unitClass_ne (associatedGradedOf_injective _ _ (by simpa using equality))⟩⟩

private lemma eval_injective (d : ℕ) (hd : ringKrullDim R = d + 1) :
    Function.Injective (grAeval (R := R)) := by
  apply (injective_iff_map_eq_zero (grAeval (R := R))).mpr
  intro polynomial kernel
  rw [← MvPolynomial.sum_homogeneousComponent polynomial]
  apply Finset.sum_eq_zero
  intro degree membership
  by_contra nonzero
  apply grAeval_ne_zero_of_homogeneous_of_dimension_succ d hd
    (MvPolynomial.homogeneousComponent_isHomogeneous degree polynomial) nonzero
  obtain ⟨component, component_eq⟩ := grAeval_isHomogeneous
    (R := R) (MvPolynomial.homogeneousComponent_isHomogeneous degree polynomial)
  have sum_eq : (∑ index ∈ Finset.range (polynomial.totalDegree + 1),
      grAeval (R := R) (MvPolynomial.homogeneousComponent index polynomial)) = 0 := by
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent, kernel]
  have at_degree := congrArg (fun value : gr (R := R) ↦ value degree) sum_eq
  rw [DirectSum.sum_apply, Finset.sum_eq_single degree] at at_degree
  · rw [component_eq] at at_degree
    simp only [associatedGradedOf_apply, DirectSum.of_eq_same, DirectSum.zero_apply] at at_degree
    rw [component_eq, at_degree, map_zero]
  · intro index _ different
    exact component_grAeval_eq_zero
      (MvPolynomial.homogeneousComponent_isHomogeneous index polynomial) different
  · exact fun absent ↦ (absent membership).elim

public theorem regularLocal_associatedGraded_presentation :
    Nonempty (MvPolynomial (Fin (maximalIdeal R).spanFinrank)
      (R ⧸ maximalIdeal R) ≃+* AssociatedGraded (maximalIdeal R)) := by
  have dimension := (isRegularLocalRing_iff R).mp (inferInstance : IsRegularLocalRing R)
  have rank_eq : embDim (R := R) = (maximalIdeal R).spanFinrank := by
    by_cases zero : (maximalIdeal R).spanFinrank = 0
    · exact Nat.le_antisymm (embDim_le_spanFinrank (R := R)) (by omega)
    · obtain ⟨dimension, dimension_eq⟩ := Nat.exists_eq_succ_of_ne_zero zero
      have krull : ringKrullDim R = dimension + 1 := by
        rw [← ‹_ = ringKrullDim R›, dimension_eq]
        simp
      exact (embDim_eq_dimension_succ dimension krull).trans dimension_eq.symm
  suffices Nonempty (MvPolynomial (Fin (embDim (R := R))) (k (R := R)) ≃+*
      gr (R := R)) by
    change Nonempty (MvPolynomial (Fin (maximalIdeal R).spanFinrank) (k (R := R)) ≃+* gr (R := R))
    rwa [rank_eq] at this
  refine ⟨RingEquiv.ofBijective (grAeval (R := R)).toRingHom ⟨?_, grAeval_surjective⟩⟩
  by_cases zero : embDim (R := R) = 0
  · letI : Nontrivial (gr (R := R)) := graded_nontrivial
    letI : IsEmpty (Fin (embDim (R := R))) := by rw [zero]; infer_instance
    intro first second equality
    rw [MvPolynomial.eq_C_of_isEmpty first, MvPolynomial.eq_C_of_isEmpty second] at equality ⊢
    apply congrArg MvPolynomial.C
    apply (algebraMap (k (R := R)) (gr (R := R))).injective
    change grAeval (R := R) (MvPolynomial.C _) = grAeval (R := R) (MvPolynomial.C _) at equality
    simpa only [grAeval, MvPolynomial.aeval_C] using equality
  · obtain ⟨dimension, dimension_eq⟩ := Nat.exists_eq_succ_of_ne_zero zero
    apply eval_injective dimension
    rw [← ‹_ = ringKrullDim R›, ← rank_eq, dimension_eq]
    simp

end

end HilbertSamuel

namespace Theory.AlgebraicGroup

noncomputable section

open IsLocalRing

public theorem regularLocal_maximalIdeal_mul_not_mem
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {a b : R} {m n : ℕ}
    (ha : a ∈ maximalIdeal R ^ m)
    (haExact : a ∉ maximalIdeal R ^ (m + 1))
    (hb : b ∈ maximalIdeal R ^ n)
    (hbExact : b ∉ maximalIdeal R ^ (n + 1)) :
    a * b ∉ maximalIdeal R ^ (m + n + 1) := by
  let I : Ideal R := maximalIdeal R
  by_cases hspanZero : I.spanFinrank = 0
  · have hIbot : I = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot
        (IsNoetherian.noetherian I)).mp hspanZero
    have ha0 : a ≠ 0 := fun ha0 ↦ haExact (ha0 ▸ Ideal.zero_mem _)
    have hb0 : b ≠ 0 := fun hb0 ↦ hbExact (hb0 ▸ Ideal.zero_mem _)
    intro hab
    have habI : a * b ∈ I := by
      rw [hIbot]
      simpa [I, hIbot] using hab
    rcases (inferInstance : I.IsPrime).mem_or_mem habI with haI | hbI
    · exact ha0 (by simpa [hIbot] using haI)
    · exact hb0 (by simpa [hIbot] using hbI)
  · obtain ⟨d, hspan⟩ := Nat.exists_eq_succ_of_ne_zero hspanZero
    have hregular :=
      (isRegularLocalRing_iff R).mp (inferInstance : IsRegularLocalRing R)
    have hd : ringKrullDim R = d + 1 := by
      rw [← hregular, show maximalIdeal R = I from rfl, hspan]
      simp
    by_cases hdegree : 0 < m + n
    · let A : HilbertSamuel.AssociatedGradedPiece I m :=
        Submodule.Quotient.mk
          (⟨a, ha⟩ : (I ^ m : Submodule R R))
      let B : HilbertSamuel.AssociatedGradedPiece I n :=
        Submodule.Quotient.mk
          (⟨b, hb⟩ : (I ^ n : Submodule R R))
      have hA0 : A ≠ 0 := by
        intro hA
        apply haExact
        change a ∈ I ^ (m + 1)
        dsimp only [A] at hA
        rw [Submodule.Quotient.mk_eq_zero] at hA
        exact hA
      have hB0 : B ≠ 0 := by
        intro hB
        apply hbExact
        change b ∈ I ^ (n + 1)
        dsimp only [B] at hB
        rw [Submodule.Quotient.mk_eq_zero] at hB
        exact hB
      obtain ⟨p, hpHom, hp⟩ :=
        HilbertSamuel.grAeval_homogeneous_surjective (R := R) m A
      obtain ⟨q, hqHom, hq⟩ :=
        HilbertSamuel.grAeval_homogeneous_surjective (R := R) n B
      have hp0 : p ≠ 0 := by
        intro hpZero
        subst p
        apply hA0
        apply HilbertSamuel.associatedGradedOf_injective I m
        simpa using hp.symm
      have hq0 : q ≠ 0 := by
        intro hqZero
        subst q
        apply hB0
        apply HilbertSamuel.associatedGradedOf_injective I n
        simpa using hq.symm
      intro hab
      have hpieceZero :
          HilbertSamuel.associatedGradedPieceMul I m n A B = 0 := by
        dsimp [A, B]
        rw [HilbertSamuel.associatedGradedPieceMul_mk,
          Submodule.Quotient.mk_eq_zero]
        simpa [I] using hab
      apply HilbertSamuel.grAeval_ne_zero_of_homogeneous_of_dimension_succ
        (R := R) d hd (hpHom.mul hqHom) (mul_ne_zero hp0 hq0)
      rw [map_mul, hp, hq]
      rw [HilbertSamuel.associatedGradedOf_mul, hpieceZero, map_zero]
    · have hm : m = 0 := by omega
      have hn : n = 0 := by omega
      subst m
      subst n
      intro hab
      have haI : a ∉ I := by simpa [I] using haExact
      have hbI : b ∉ I := by simpa [I] using hbExact
      have habI : a * b ∈ I := by simpa [I] using hab
      rcases (inferInstance : I.IsPrime).mem_or_mem habI with haI' | hbI'
      · exact (haI haI').elim
      · exact (hbI hbI').elim

end

end Theory.AlgebraicGroup
