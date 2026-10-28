module

public import Theory.AlgebraicGroup.RootData.RankTwoPositiveMixedRootTable
public import Theory.AlgebraicGroup.RootData.ChevalleyCommutator

/-!
# Finite rank-two Chevalley parameter words

For a positive root `alpha`, a simple root `delta`, and a root
`gamma = alpha + delta`, this module writes every element of the `gamma` root
group as a finite product of simple-root elements and positive-root elements
of strictly smaller base height.  The finite calculation consumes a
base-independent certificate containing root-curve range and additivity, the
full commutator collection, and coroot-torus conjugation, together with the
realized root pairing.  A positive-chain base may therefore differ from the
certificate's presentation base; the original full-system theorem is retained
as a wrapper.

The proof classifies the positive roots in the plane spanned by `alpha` and
`delta` into the six finite reduced rank-two tables.  It collects every
commutator correction term explicitly.  The ordinary coefficient isolates
the `(1,1)` parameter directly; when coefficients `2` or `3` vanish, adjacent
root commutators and torus conjugation separate the remaining parameters.
Algebraic closedness supplies the square-root rescalings needed for this
separation, including characteristics two and three.

This is the local rank-two calculation underlying the positive-root
generation argument in GLS3, Section 1.12.  Its support predicate is kept
private and inline so the module remains below the later singular-isolation
assembly and introduces no upward import cycle.
-/

namespace Theory.AlgebraicGroup

universe u

open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
variable (D : RootGroupData K T) (C : ChevalleyData K D)
variable {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (P : RootPairing ι R M N) [P.IsRootSystem]
variable [P.IsCrystallographic] [P.IsReduced]
variable (e : D.Root ≃ ι) (base : P.Base)

/-! The finite rank-two calculation only uses the clauses below from a
Chevalley system.  Keeping them in a base-free certificate lets the positive
chain order come from a different root-system base than the certificate's
original presentation. -/

public structure RankTwoChevalleyParameterCertificate
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ ι) : Prop where
  rootCurve_range : ∀ α, Set.range (C.x α) = D.rootSubgroup α
  rootCurve_additive : ∀ α t u, C.x α t * C.x α u = C.x α (t + u)
  full_commutator : ∀ α β, AreLinearlyIndependentRoots D P e α β →
    ∃ order : List (ChevalleyCommutatorTerm D.Root),
    ∃ c : ChevalleyCommutatorTerm D.Root → k,
      order.Nodup ∧
      order.Pairwise (fun q r => q.i + q.j ≤ r.i + r.j) ∧
      (∀ q, q ∈ order ↔ IsValidChevalleyCommutatorTerm D P e α β q) ∧
      (∀ q ∈ order, HasExpectedChevalleyCoefficient D P e α β q (c q)) ∧
      ∀ t u,
        (C.x α t)⁻¹ * (C.x β u)⁻¹ * C.x α t * C.x β u =
          (order.map fun q => C.x q.root (c q * t ^ q.i * u ^ q.j)).prod
  coroot_conjugation : ∀ α β t u,
    (C.h β u)⁻¹ * C.x α t * C.h β u =
      C.x α ((u : k) ^ D.pairing α β * t)

public structure RankTwoRootPairingCertificate
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ ι) : Prop where
  pairing : ∀ α β, (D.pairing α β : R) = P.pairing (e α) (e β)

omit [IsAlgClosed k] in
public theorem RankTwoChevalleyParameterCertificate.of_system
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ ι)
    (base : P.Base) (hC : IsChevalleySystem D C P e base) :
    RankTwoChevalleyParameterCertificate D C P e := by
  refine ⟨fun α => (hC.1 α).2, hC.2.2.2.1, hC.2.2.2.2.1,
    hC.2.2.2.2.2.2.2.2.2.2.2.1⟩

omit [IsAlgClosed k] in
public theorem RankTwoRootPairingCertificate.of_realization
    (D : RootGroupData K T) (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ ι)
    (base : P.Base) (hRoot : IsRootSystemRealization D P e base) :
    RankTwoRootPairingCertificate D P e :=
  ⟨hRoot.1⟩

private def chainSupport (gamma : D.Root) : Set D.Root :=
  {rho | e rho ∈ base.support ∨
    (base.IsPos (e rho) ∧ base.height (e rho) < base.height (e gamma))}

private def HasChainWord (gamma : D.Root) (g : Variety.Point K) : Prop :=
  ∃ word : List (D.Root × k),
    (∀ q ∈ word, q.1 ∈ chainSupport D P e base gamma) ∧
    g = FilteredCollection.wordProduct C.x word

private def mixedCoordinateSet (alpha delta : D.Root) : Set (Nat × Nat) :=
  {ij | 0 < ij.1 ∧ 0 < ij.2 ∧
    ∃ rho : D.Root, P.root (e rho) =
      (ij.1 : R) • P.root (e alpha) +
        (ij.2 : R) • P.root (e delta)}

omit [IsAlgClosed k] in
private lemma chevalleyX_zero
    (hC : RankTwoChevalleyParameterCertificate D C P e) (rho : D.Root) :
    C.x rho 0 = 1 := by
  have h := hC.rootCurve_additive rho 0 0
  apply mul_left_cancel (a := C.x rho 0)
  simpa using h

omit [IsAlgClosed k] in
private lemma chevalleyX_neg
    (hC : RankTwoChevalleyParameterCertificate D C P e) (rho : D.Root) (t : k) :
    C.x rho (-t) = (C.x rho t)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [hC.rootCurve_additive rho (-t) t]
  simpa using chevalleyX_zero D C P e hC rho

omit [IsAlgClosed k] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] in
private lemma hasChainWord_one (gamma : D.Root) :
    HasChainWord D C P e base gamma 1 := by
  exact ⟨[], by simp, by simp [FilteredCollection.wordProduct]⟩

omit [IsAlgClosed k] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] in
private lemma hasChainWord_x
    (gamma rho : D.Root) (t : k)
    (hrho : rho ∈ chainSupport D P e base gamma) :
    HasChainWord D C P e base gamma (C.x rho t) := by
  exact ⟨[(rho, t)], by simpa, by simp [FilteredCollection.wordProduct]⟩

omit [IsAlgClosed k] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] in
private lemma HasChainWord.mul {gamma : D.Root} {g h : Variety.Point K}
    (hg : HasChainWord D C P e base gamma g)
    (hh : HasChainWord D C P e base gamma h) :
    HasChainWord D C P e base gamma (g * h) := by
  obtain ⟨wg, hwg, rfl⟩ := hg
  obtain ⟨wh, hwh, rfl⟩ := hh
  refine ⟨wg ++ wh, ?_, ?_⟩
  · intro q hq
    exact (List.mem_append.mp hq).elim (hwg q) (hwh q)
  · simp [FilteredCollection.wordProduct, List.map_append]

omit [IsAlgClosed k] in
private lemma wordProduct_inv_hasChainWord
    (hC : RankTwoChevalleyParameterCertificate D C P e) (gamma : D.Root)
    (word : List (D.Root × k))
    (hword : ∀ q ∈ word, q.1 ∈ chainSupport D P e base gamma) :
    HasChainWord D C P e base gamma
      (FilteredCollection.wordProduct C.x word)⁻¹ := by
  induction word with
  | nil => simpa [FilteredCollection.wordProduct] using
      hasChainWord_one D C P e base gamma
  | cons q tail ih =>
      have hq := hword q (by simp)
      have htail : ∀ r ∈ tail, r.1 ∈ chainSupport D P e base gamma := by
        intro r hr
        exact hword r (by simp [hr])
      have hqInv : HasChainWord D C P e base gamma (C.x q.1 q.2)⁻¹ := by
        rw [← chevalleyX_neg D C P e hC]
        exact hasChainWord_x D C P e base gamma q.1 (-q.2) hq
      simpa [FilteredCollection.wordProduct, mul_inv_rev] using
        (HasChainWord.mul D C P e base (ih htail) hqInv)

omit [IsAlgClosed k] in
private lemma HasChainWord.inv
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {gamma : D.Root} {g : Variety.Point K}
    (hg : HasChainWord D C P e base gamma g) :
    HasChainWord D C P e base gamma g⁻¹ := by
  obtain ⟨word, hword, rfl⟩ := hg
  exact wordProduct_inv_hasChainWord D C P e base hC gamma word hword

omit [IsAlgClosed k] in
private lemma HasChainWord.cancel_left
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {gamma : D.Root} {g h : Variety.Point K}
    (hg : HasChainWord D C P e base gamma g)
    (hgh : HasChainWord D C P e base gamma (g * h)) :
    HasChainWord D C P e base gamma h := by
  have := (hg.inv D C P e base hC).mul D C P e base hgh
  convert this using 1; group

private def corootPairScale (alpha beta gamma : D.Root) (u v : kˣ) : k :=
  (u : k) ^ D.pairing gamma beta * (v : k) ^ D.pairing gamma alpha

omit [IsAlgClosed k] in
private lemma corootPair_conjugates_root
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (alpha beta gamma : D.Root) (u v : kˣ) (t : k) :
    (C.h beta u * C.h alpha v)⁻¹ * C.x gamma t *
        (C.h beta u * C.h alpha v) =
      C.x gamma (corootPairScale D alpha beta gamma u v * t) := by
  have hconj := hC.coroot_conjugation
  calc
    (C.h beta u * C.h alpha v)⁻¹ * C.x gamma t *
        (C.h beta u * C.h alpha v) =
        (C.h alpha v)⁻¹ *
          ((C.h beta u)⁻¹ * C.x gamma t * C.h beta u) *
            C.h alpha v := by group
    _ = (C.h alpha v)⁻¹ *
          C.x gamma ((u : k) ^ D.pairing gamma beta * t) *
            C.h alpha v := by rw [hconj gamma beta t u]
    _ = C.x gamma
        ((v : k) ^ D.pairing gamma alpha *
          ((u : k) ^ D.pairing gamma beta * t)) :=
      hconj gamma alpha ((u : k) ^ D.pairing gamma beta * t) v
    _ = _ := by
      apply congrArg (C.x gamma)
      simp only [corootPairScale]
      ring

omit [IsAlgClosed k] in
private lemma corootPair_conjugates_word
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (alpha beta : D.Root) (u v : kˣ)
    (word : List (D.Root × k)) :
    (C.h beta u * C.h alpha v)⁻¹ *
        FilteredCollection.wordProduct C.x word *
          (C.h beta u * C.h alpha v) =
      FilteredCollection.wordProduct C.x
        (word.map fun q =>
          (q.1, corootPairScale D alpha beta q.1 u v * q.2)) := by
  induction word with
  | nil => simp [FilteredCollection.wordProduct]
  | cons q tail ih =>
      change (C.h beta u * C.h alpha v)⁻¹ *
          (C.x q.1 q.2 * FilteredCollection.wordProduct C.x tail) *
            (C.h beta u * C.h alpha v) = _
      change _ = C.x q.1 (corootPairScale D alpha beta q.1 u v * q.2) *
        FilteredCollection.wordProduct C.x
          (tail.map fun r =>
            (r.1, corootPairScale D alpha beta r.1 u v * r.2))
      calc
        _ = ((C.h beta u * C.h alpha v)⁻¹ * C.x q.1 q.2 *
              (C.h beta u * C.h alpha v)) *
            ((C.h beta u * C.h alpha v)⁻¹ *
              FilteredCollection.wordProduct C.x tail *
                (C.h beta u * C.h alpha v)) := by group
        _ = _ := by
          rw [corootPair_conjugates_root D C P e hC, ih]

omit [IsAlgClosed k] in
private lemma HasChainWord.conjugateCorootPair
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {gamma : D.Root} {g : Variety.Point K}
    (hg : HasChainWord D C P e base gamma g)
    (alpha beta : D.Root) (u v : kˣ) :
    HasChainWord D C P e base gamma
      ((C.h beta u * C.h alpha v)⁻¹ * g *
        (C.h beta u * C.h alpha v)) := by
  obtain ⟨word, hword, rfl⟩ := hg
  refine ⟨word.map fun q =>
      (q.1, corootPairScale D alpha beta q.1 u v * q.2), ?_, ?_⟩
  · intro q hq
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact hword r hr
  · exact corootPair_conjugates_word D C P e hC alpha beta u v word

private lemma exists_pairingSeparator
    (hRoot : RankTwoRootPairingCertificate D P e)
    (fixed moved : D.Root)
    (hLI : AreLinearlyIndependentRoots D P e fixed moved) :
    ∃ u v : kˣ,
      corootPairScale D fixed moved fixed u v = 1 ∧
      corootPairScale D fixed moved moved u v ≠ 1 := by
  have hlin : LinearIndependent R
      ![P.root (e fixed), P.root (e moved)] := by
    rw [LinearIndependent.pair_iff]
    simpa [AreLinearlyIndependentRoots] using hLI
  have hcox : P.coxeterWeight (e fixed) (e moved) ≠ 4 :=
    (P.linearIndependent_iff_coxeterWeight_ne_four).mp hlin
  let z : Int :=
    4 - D.pairing fixed moved * D.pairing moved fixed
  have hz : z ≠ 0 := by
    intro hz0
    apply hcox
    rw [RootPairing.coxeterWeight, ← hRoot.pairing fixed moved,
      ← hRoot.pairing moved fixed]
    have hzprod :
        D.pairing fixed moved * D.pairing moved fixed = 4 := by
      dsimp [z] at hz0
      omega
    exact_mod_cast hzprod
  obtain ⟨c, hc⟩ := exists_unit_zpow_ne_one (k := k) hz
  let a := D.pairing fixed moved
  let b := D.pairing moved fixed
  refine ⟨c ^ (2 : Int), c ^ (-a), ?_, ?_⟩
  · have hsame : D.pairing fixed fixed = 2 := by
      have hsameR : (D.pairing fixed fixed : R) = 2 := by
        rw [hRoot.pairing fixed fixed, P.pairing_same]
      exact_mod_cast hsameR
    simp only [corootPairScale, hsame]
    have hu :
        (c ^ (2 : Int)) ^ a * (c ^ (-a)) ^ (2 : Int) = 1 := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add]
      convert zpow_zero c using 1
      ring_nf
    simpa [a] using congrArg Units.val hu
  · have hsame : D.pairing moved moved = 2 := by
      have hsameR : (D.pairing moved moved : R) = 2 := by
        rw [hRoot.pairing moved moved, P.pairing_same]
      exact_mod_cast hsameR
    simp only [corootPairScale, hsame]
    intro heq
    apply hc
    have heqUnits :
        (c ^ (2 : Int)) ^ (2 : Int) * (c ^ (-a)) ^ b = 1 := by
      apply Units.ext
      simpa using heq
    rw [← zpow_mul, ← zpow_mul, ← zpow_add] at heqUnits
    convert heqUnits using 1
    dsimp [a, b, z]
    ring_nf

private lemma hasChainWord_all_parameters_of_nonzero
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    (gamma : D.Root) {s : k} (hs : s ≠ 0)
    (hword : HasChainWord D C P e base gamma (C.x gamma s)) :
    ∀ t : k, HasChainWord D C P e base gamma (C.x gamma t) := by
  intro t
  by_cases ht : t = 0
  · subst t
    rw [chevalleyX_zero D C P e hC]
    exact hasChainWord_one D C P e base gamma
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (t / s) (by omega : 0 < 2)
    have hr0 : r ≠ 0 := by
      intro hrzero
      subst r
      have hdiv : t / s ≠ 0 := div_ne_zero ht hs
      simp only [zero_pow (by omega : 2 ≠ 0)] at hr
      exact hdiv hr.symm
    let u : kˣ := Units.mk0 r hr0
    let v : kˣ := 1
    have hconj := hword.conjugateCorootPair D C P e base hC gamma gamma u v
    have hpair : D.pairing gamma gamma = 2 := by
      have hpairR : (D.pairing gamma gamma : R) = 2 := by
        rw [hRoot.pairing gamma gamma, P.pairing_same]
      exact_mod_cast hpairR
    have hscale : corootPairScale D gamma gamma gamma u v * s = t := by
      simp only [corootPairScale, hpair, v, Units.val_one, one_zpow, mul_one]
      change r ^ (2 : Int) * s = t
      rw [show r ^ (2 : Int) = r ^ (2 : Nat) by norm_num]
      rw [hr]
      field_simp
    rw [corootPair_conjugates_root D C P e hC, hscale] at hconj
    exact hconj

omit [IsAlgClosed k] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
private lemma positiveRoots_linearlyIndependent
    {rho sigma : D.Root} (hrho : base.IsPos (e rho))
    (hsigma : base.IsPos (e sigma)) (hne : rho ≠ sigma) :
    AreLinearlyIndependentRoots D P e rho sigma := by
  let _ := P.indexNeg
  have hnotopp : P.root (e rho) ≠ -P.root (e sigma) := by
    intro hneg
    have hidx : e rho = P.reflectionPerm (e sigma) (e sigma) :=
      P.root_eq_neg_iff.mp hneg
    have hrhoNeg : base.IsPos (-e sigma) := by
      simpa [hidx] using hrho
    exact ((RootPairing.Base.IsPos.neg_iff_not
      (P := P) (b := base) (i := e sigma)).mp hrhoNeg) hsigma
  have hrootNe : e rho ≠ e sigma := fun heq => hne (e.injective heq)
  have hlin : LinearIndependent R ![P.root (e rho), P.root (e sigma)] :=
    RootPairing.IsReduced.linearIndependent (P := P) hrootNe hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

omit [IsAlgClosed k] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] in
private lemma chainSupport_alpha_delta
    {alpha delta gamma : D.Root}
    (hdelta : e delta ∈ base.support) (halpha : base.IsPos (e alpha))
    (hadd : P.root (e gamma) = P.root (e alpha) + P.root (e delta)) :
    alpha ∈ chainSupport D P e base gamma ∧
      delta ∈ chainSupport D P e base gamma := by
  constructor
  · right
    refine ⟨halpha, ?_⟩
    rw [base.height_add hadd, base.height_one_of_mem_support hdelta]
    omega
  · exact Or.inl hdelta

omit [IsAlgClosed k] in
private lemma HasChainWord.chevalleyCommutator
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {gamma alpha beta : D.Root}
    (halpha : alpha ∈ chainSupport D P e base gamma)
    (hbeta : beta ∈ chainSupport D P e base gamma)
    (t u : k) :
    HasChainWord D C P e base gamma
      ((C.x alpha t)⁻¹ * (C.x beta u)⁻¹ * C.x alpha t * C.x beta u) := by
  have ha := hasChainWord_x D C P e base gamma alpha t halpha
  have hb := hasChainWord_x D C P e base gamma beta u hbeta
  exact (((ha.inv D C P e base hC).mul D C P e base
    (hb.inv D C P e base hC)).mul D C P e base ha).mul D C P e base hb

omit [IsAlgClosed k] in
private lemma validTerm_eq_of_coordinates
    {alpha beta rho : D.Root} {q : ChevalleyCommutatorTerm D.Root}
    {i j : Nat} (hq : IsValidChevalleyCommutatorTerm D P e alpha beta q)
    (hi : q.i = i) (hj : q.j = j)
    (hrho : P.root (e rho) =
      (i : R) • P.root (e alpha) + (j : R) • P.root (e beta)) :
    q = (⟨i, j, rho⟩ : ChevalleyCommutatorTerm D.Root) := by
  cases q with
  | mk qi qj qroot =>
      simp only at hi hj
      subst qi
      subst qj
      have hroot : qroot = rho := by
        apply e.injective
        apply P.root.injective
        exact hq.2.2.trans hrho.symm
      subst qroot
      rfl

omit [IsAlgClosed k] in
private lemma commutatorOrder_eq_of_valid_terms
    {alpha beta : D.Root}
    (order terms : List (ChevalleyCommutatorTerm D.Root))
    (horderNodup : order.Nodup)
    (horderPairwise : order.Pairwise
      (fun q r => q.i + q.j ≤ r.i + r.j))
    (hvalid : ∀ q, q ∈ order ↔
      IsValidChevalleyCommutatorTerm D P e alpha beta q)
    (htermsNodup : terms.Nodup)
    (htermsPairwise : terms.Pairwise
      (fun q r => q.i + q.j ≤ r.i + r.j))
    (hterms : ∀ q,
      IsValidChevalleyCommutatorTerm D P e alpha beta q ↔ q ∈ terms)
    (hdegreeInj : ∀ a ∈ terms, ∀ b ∈ terms,
      a.i + a.j = b.i + b.j → a = b) :
    order = terms := by
  have hperm : order.Perm terms :=
    (List.perm_ext_iff_of_nodup horderNodup htermsNodup).2 fun q =>
      (hvalid q).trans (hterms q)
  exact hperm.eq_of_pairwise
    (fun a b ha hb hab hba =>
      hdegreeInj a ((hterms a).mp ((hvalid a).mp ha)) b hb (by omega))
    horderPairwise htermsPairwise

omit [IsAlgClosed k] in
private lemma commutatorProduct_hasChainWord
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {gamma alpha beta : D.Root}
    (halpha : alpha ∈ chainSupport D P e base gamma)
    (hbeta : beta ∈ chainSupport D P e base gamma)
    (hLI : AreLinearlyIndependentRoots D P e alpha beta)
    (t u : k) :
    ∃ order : List (ChevalleyCommutatorTerm D.Root),
    ∃ c : ChevalleyCommutatorTerm D.Root → k,
      order.Nodup ∧
      order.Pairwise (fun q r => q.i + q.j ≤ r.i + r.j) ∧
      (∀ q, q ∈ order ↔ IsValidChevalleyCommutatorTerm D P e alpha beta q) ∧
      (∀ q ∈ order, HasExpectedChevalleyCoefficient D P e alpha beta q (c q)) ∧
      HasChainWord D C P e base gamma
        ((order.map fun q => C.x q.root
          (c q * t ^ q.i * u ^ q.j)).prod) := by
  obtain ⟨order, c, hnodup, hpairwise, hvalid, hcoeff, hformula⟩ :=
    hC.full_commutator alpha beta hLI
  refine ⟨order, c, hnodup, hpairwise, hvalid, hcoeff, ?_⟩
  rw [← hformula t u]
  exact HasChainWord.chevalleyCommutator D C P e base hC halpha hbeta t u

omit [IsAlgClosed k] in
private lemma mixedRoots_commute_of_no_positive_coordinate
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {alpha delta rho sigma : D.Root} {a b c d : Nat}
    (hrho : P.root (e rho) =
      (a : R) • P.root (e alpha) + (b : R) • P.root (e delta))
    (hsigma : P.root (e sigma) =
      (c : R) • P.root (e alpha) + (d : R) • P.root (e delta))
    (hLI : AreLinearlyIndependentRoots D P e rho sigma)
    (hNo : ∀ m n : Nat, 0 < m → 0 < n →
      ¬ ∃ tau : D.Root,
        P.root (e tau) =
          (m * a + n * c : Nat) • P.root (e alpha) +
            (m * b + n * d : Nat) • P.root (e delta)) :
    ∀ s t : k, Commute (C.x rho s) (C.x sigma t) := by
  have hEmpty : ChevalleyCommutatorRoots D P e rho sigma = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro tau htau
    rw [mem_chevalleyCommutatorRoots_iff] at htau
    obtain ⟨m, n, hm, hn, htau⟩ := htau
    apply hNo m n hm hn
    refine ⟨tau, ?_⟩
    rw [htau, hrho, hsigma]
    module
  intro s t
  obtain ⟨order, coefficient, _hnodup, _hpairwise, hvalid, _hcoeff, hformula⟩ :=
    hC.full_commutator rho sigma hLI
  have horder : order = [] := by
    cases order with
    | nil => rfl
    | cons q tail =>
        exfalso
        have hqvalid : IsValidChevalleyCommutatorTerm D P e rho sigma q :=
          (hvalid q).mp (by simp)
        have hqmem : q.root ∈ (ChevalleyCommutatorRoots D P e rho sigma) := by
          rw [mem_chevalleyCommutatorRoots_iff]
          exact ⟨q.i, q.j, hqvalid.1, hqvalid.2.1, hqvalid.2.2⟩
        rw [hEmpty] at hqmem
        exact hqmem
  have hcommInv : Commute (C.x rho s)⁻¹ (C.x sigma t)⁻¹ := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [commutatorElement_def, horder] using hformula s t
  exact (Commute.inv_inv_iff.mp hcommInv)

omit [IsAlgClosed k] in
private lemma mixedRoots_commute_of_table_exclusion
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {alpha delta rho sigma : D.Root} {a b c d : Nat}
    {S : Set (Nat × Nat)}
    (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d)
    (hrho : P.root (e rho) =
      (a : R) • P.root (e alpha) + (b : R) • P.root (e delta))
    (hsigma : P.root (e sigma) =
      (c : R) • P.root (e alpha) + (d : R) • P.root (e delta))
    (hLI : AreLinearlyIndependentRoots D P e rho sigma)
    (htable : mixedCoordinateSet D P e alpha delta = S)
    (hNo : ∀ m n : Nat, 0 < m → 0 < n →
      (m * a + n * c, m * b + n * d) ∉ S) :
    ∀ s t : k, Commute (C.x rho s) (C.x sigma t) := by
  apply mixedRoots_commute_of_no_positive_coordinate D C P e hC
    hrho hsigma hLI
  intro m n hm hn hex
  apply hNo m n hm hn
  rw [← htable]
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.add_pos_left (Nat.mul_pos hm ha) _
  · exact Nat.add_pos_left (Nat.mul_pos hm hb) _
  · simpa only [Nat.cast_smul_eq_nsmul R] using hex

omit [IsAlgClosed k] in
private lemma exact_commutatorProduct_hasChainWord
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {gamma alpha delta : D.Root}
    (halpha : alpha ∈ chainSupport D P e base gamma)
    (hdelta : delta ∈ chainSupport D P e base gamma)
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (terms : List (ChevalleyCommutatorTerm D.Root))
    (htermsNodup : terms.Nodup)
    (htermsPairwise : terms.Pairwise
      (fun q r => q.i + q.j ≤ r.i + r.j))
    (hterms : ∀ q,
      IsValidChevalleyCommutatorTerm D P e alpha delta q ↔ q ∈ terms)
    (hdegreeInj : ∀ a ∈ terms, ∀ b ∈ terms,
      a.i + a.j = b.i + b.j → a = b) :
    ∃ c : ChevalleyCommutatorTerm D.Root → k,
      (∀ q ∈ terms,
        HasExpectedChevalleyCoefficient D P e alpha delta q (c q)) ∧
      HasChainWord D C P e base gamma
        ((terms.map fun q => C.x q.root (c q)).prod) := by
  obtain ⟨order, c, hnodup, hpairwise, hvalid, hcoeff, hword⟩ :=
    commutatorProduct_hasChainWord D C P e base hC halpha hdelta hLI 1 1
  have horder : order = terms :=
    commutatorOrder_eq_of_valid_terms D P e order terms hnodup hpairwise
      hvalid htermsNodup htermsPairwise hterms hdegreeInj
  refine ⟨c, ?_, ?_⟩
  · intro q hq
    exact hcoeff q ((hvalid q).2 ((hterms q).2 hq))
  · rw [horder] at hword
    simpa using hword

omit [IsAlgClosed k] in
private lemma exact_commutatorProduct_hasChainWord_of_commuting_terms
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {gamma alpha delta : D.Root}
    (halpha : alpha ∈ chainSupport D P e base gamma)
    (hdelta : delta ∈ chainSupport D P e base gamma)
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (terms : List (ChevalleyCommutatorTerm D.Root))
    (htermsNodup : terms.Nodup)
    (hterms : ∀ q,
      IsValidChevalleyCommutatorTerm D P e alpha delta q ↔ q ∈ terms)
    (hcomm : ∀ a ∈ terms, ∀ b ∈ terms, a ≠ b →
      ∀ s t : k, Commute (C.x a.root s) (C.x b.root t)) :
    ∃ c : ChevalleyCommutatorTerm D.Root → k,
      (∀ q ∈ terms,
        HasExpectedChevalleyCoefficient D P e alpha delta q (c q)) ∧
      HasChainWord D C P e base gamma
        ((terms.map fun q => C.x q.root (c q)).prod) := by
  obtain ⟨order, c, hnodup, _hpairwise, hvalid, hcoeff, hword⟩ :=
    commutatorProduct_hasChainWord D C P e base hC halpha hdelta hLI 1 1
  have hperm : order.Perm terms :=
    (List.perm_ext_iff_of_nodup hnodup htermsNodup).2 fun q =>
      (hvalid q).trans (hterms q)
  let f := fun q : ChevalleyCommutatorTerm D.Root => C.x q.root (c q)
  have horderComm : order.Pairwise (fun a b => Commute (f a) (f b)) :=
    hnodup.pairwise_of_forall_ne fun a ha b hb hab => by
      apply hcomm a ((hterms a).1 ((hvalid a).1 ha))
        b ((hterms b).1 ((hvalid b).1 hb)) hab
  have hmapComm : (order.map f).Pairwise Commute := by
    simpa only [List.pairwise_map] using horderComm
  have hprod : (order.map f).prod = (terms.map f).prod :=
    (hperm.map f).prod_eq' hmapComm
  refine ⟨c, ?_, ?_⟩
  · intro q hq
    exact hcoeff q ((hvalid q).2 ((hterms q).2 hq))
  · have hword' : HasChainWord D C P e base gamma ((order.map f).prod) := by
      simpa [f] using hword
    rw [hprod] at hword'
    exact hword'

omit [IsAlgClosed k] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] in
private lemma roots_ne_of_distinct_coordinates
    {alpha delta rho sigma : D.Root} {a b c d : Nat}
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (hrho : P.root (e rho) =
      (a : R) • P.root (e alpha) + (b : R) • P.root (e delta))
    (hsigma : P.root (e sigma) =
      (c : R) • P.root (e alpha) + (d : R) • P.root (e delta))
    (hcoord : (a, b) ≠ (c, d)) : rho ≠ sigma := by
  intro hrs
  rw [hrs] at hrho
  have heq : (a : R) • P.root (e alpha) + (b : R) • P.root (e delta) =
      (c : R) • P.root (e alpha) + (d : R) • P.root (e delta) :=
    hrho.symm.trans hsigma
  have hzero : ((a : R) - c) • P.root (e alpha) +
      ((b : R) - d) • P.root (e delta) = 0 := by
    calc
      _ = ((a : R) • P.root (e alpha) + (b : R) • P.root (e delta)) -
          ((c : R) • P.root (e alpha) + (d : R) • P.root (e delta)) := by
        module
      _ = 0 := sub_eq_zero.mpr heq
  obtain ⟨ha, hb⟩ := hLI _ _ hzero
  apply hcoord
  congr
  · exact Nat.cast_injective (sub_eq_zero.mp ha)
  · exact Nat.cast_injective (sub_eq_zero.mp hb)

omit [IsAlgClosed k] [P.IsRootSystem] [P.IsReduced] in
private lemma pairingIn_eq_of_equal_lengths_root_sum
    {alpha delta gamma : D.Root} {z : Int}
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (hlen : RootSquaredLength P (e alpha) =
      RootSquaredLength P (e delta))
    (hgamma : RootSquaredLength P (e gamma) =
      (z : R) * RootSquaredLength P (e alpha)) :
    P.pairingIn ℤ (e alpha) (e delta) = z - 2 := by
  let _ := Fintype.ofFinite ι
  let L := P.RootForm (P.root (e alpha)) (P.root (e alpha))
  have hL : L ≠ 0 :=
    RootPairing.IsAnisotropic.rootForm_root_ne_zero (e alpha)
  have hlen' : P.RootForm (P.root (e delta)) (P.root (e delta)) = L := by
    simpa [RootSquaredLength, L] using hlen.symm
  have hcross :=
    ((P.posRootForm ℤ).toInvariantForm).two_mul_apply_root_root
      (e alpha) (e delta)
  have hcross' :
      2 * P.RootForm (P.root (e alpha)) (P.root (e delta)) =
        (P.pairingIn ℤ (e alpha) (e delta) : R) * L := by
    change 2 * P.RootForm (P.root (e alpha)) (P.root (e delta)) =
      P.pairing (e alpha) (e delta) *
        P.RootForm (P.root (e delta)) (P.root (e delta)) at hcross
    simpa [← P.algebraMap_pairingIn ℤ, hlen'] using hcross
  have hsum :
      P.RootForm (P.root (e gamma)) (P.root (e gamma)) =
        2 * L + (P.pairingIn ℤ (e alpha) (e delta) : R) * L := by
    rw [hadd]
    simp only [map_add, LinearMap.add_apply]
    rw [show P.RootForm (P.root (e delta)) (P.root (e alpha)) =
      P.RootForm (P.root (e alpha)) (P.root (e delta)) by
        exact P.rootForm_symmetric.eq _ _, hlen', ← hcross']
    ring
  have hgamma' :
      P.RootForm (P.root (e gamma)) (P.root (e gamma)) = (z : R) * L := by
    simpa [RootSquaredLength, L] using hgamma
  have hpCast : (P.pairingIn ℤ (e alpha) (e delta) : R) = (z - 2 : Int) := by
    apply mul_right_cancel₀ hL
    calc
      (P.pairingIn ℤ (e alpha) (e delta) : R) * L =
          (z : R) * L - 2 * L := by rw [← hgamma', hsum]; ring
      _ = (z - 2 : Int) * L := by push_cast; ring
  exact_mod_cast hpCast

omit [IsAlgClosed k] [P.IsRootSystem] [P.IsReduced] in
private lemma pairingIn_eq_of_equal_lengths
    {alpha delta : D.Root}
    (hlen : RootSquaredLength P (e alpha) =
      RootSquaredLength P (e delta)) :
    P.pairingIn ℤ (e alpha) (e delta) =
      P.pairingIn ℤ (e delta) (e alpha) := by
  let _ := Fintype.ofFinite ι
  let L := P.RootForm (P.root (e alpha)) (P.root (e alpha))
  have hL : L ≠ 0 :=
    RootPairing.IsAnisotropic.rootForm_root_ne_zero (e alpha)
  have hlen' : P.RootForm (P.root (e delta)) (P.root (e delta)) = L := by
    simpa [RootSquaredLength, L] using hlen.symm
  have had :=
    ((P.posRootForm ℤ).toInvariantForm).two_mul_apply_root_root
      (e alpha) (e delta)
  have hda :=
    ((P.posRootForm ℤ).toInvariantForm).two_mul_apply_root_root
      (e delta) (e alpha)
  have had' :
      (P.pairingIn ℤ (e alpha) (e delta) : R) * L =
        2 * P.RootForm (P.root (e alpha)) (P.root (e delta)) := by
    change 2 * P.RootForm (P.root (e alpha)) (P.root (e delta)) =
      P.pairing (e alpha) (e delta) *
        P.RootForm (P.root (e delta)) (P.root (e delta)) at had
    simpa [← P.algebraMap_pairingIn ℤ, hlen'] using had.symm
  have hda' :
      (P.pairingIn ℤ (e delta) (e alpha) : R) * L =
        2 * P.RootForm (P.root (e alpha)) (P.root (e delta)) := by
    change 2 * P.RootForm (P.root (e delta)) (P.root (e alpha)) =
      P.pairing (e delta) (e alpha) *
        P.RootForm (P.root (e alpha)) (P.root (e alpha)) at hda
    rw [show P.RootForm (P.root (e delta)) (P.root (e alpha)) =
      P.RootForm (P.root (e alpha)) (P.root (e delta)) by
        exact P.rootForm_symmetric.eq _ _] at hda
    simpa [← P.algebraMap_pairingIn ℤ] using hda.symm
  have hcast : (P.pairingIn ℤ (e alpha) (e delta) : R) =
      P.pairingIn ℤ (e delta) (e alpha) := by
    apply mul_right_cancel₀ hL
    rw [had', hda']
  exact_mod_cast hcast

private lemma isolate_moved_of_commuting_pair_pre
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    (gamma fixed moved : D.Root) (a b : k)
    (hword : HasChainWord D C P e base gamma
      (C.x fixed a * C.x moved b))
    (hcomm : ∀ s t : k, Commute (C.x fixed s) (C.x moved t))
    (hLI : AreLinearlyIndependentRoots D P e fixed moved)
    (hb : b ≠ 0) :
    ∃ z : k, z ≠ 0 ∧
      HasChainWord D C P e base gamma (C.x moved z) := by
  obtain ⟨u, v, hfix, hmove⟩ :=
    exists_pairingSeparator D P e hRoot fixed moved hLI
  let H := C.h moved u * C.h fixed v
  let scale := corootPairScale D fixed moved moved u v
  have hscaled :=
    hword.conjugateCorootPair D C P e base hC fixed moved u v
  have hscaledEq :
      H⁻¹ * (C.x fixed a * C.x moved b) * H =
        C.x fixed a * C.x moved (scale * b) := by
    calc
      H⁻¹ * (C.x fixed a * C.x moved b) * H =
          (H⁻¹ * C.x fixed a * H) *
            (H⁻¹ * C.x moved b * H) := by group
      _ = C.x fixed (corootPairScale D fixed moved fixed u v * a) *
            C.x moved (corootPairScale D fixed moved moved u v * b) := by
        rw [show H = C.h moved u * C.h fixed v by rfl,
          corootPair_conjugates_root D C P e hC,
          corootPair_conjugates_root D C P e hC]
      _ = C.x fixed a * C.x moved (scale * b) := by
        rw [hfix, one_mul]
  rw [hscaledEq] at hscaled
  have hdiff := hscaled.mul D C P e base
    (hword.inv D C P e base hC)
  let z := (scale - 1) * b
  have hz : z ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hmove) hb
  refine ⟨z, hz, ?_⟩
  have heq :
      (C.x fixed a * C.x moved (scale * b)) *
          (C.x fixed a * C.x moved b)⁻¹ = C.x moved z := by
    rw [mul_inv_rev, ← chevalleyX_neg D C P e hC,
      ← chevalleyX_neg D C P e hC]
    calc
      (C.x fixed a * C.x moved (scale * b)) *
          (C.x moved (-b) * C.x fixed (-a)) =
          C.x fixed a *
            (C.x moved (scale * b) * C.x moved (-b)) *
              C.x fixed (-a) := by group
      _ = C.x fixed a * C.x moved (scale * b + -b) *
            C.x fixed (-a) := by rw [hC.rootCurve_additive]
      _ = C.x moved (scale * b + -b) *
            (C.x fixed a * C.x fixed (-a)) := by
        rw [(hcomm a (scale * b + -b)).eq]
        group
      _ = C.x moved (scale * b + -b) * C.x fixed (a + -a) := by
        rw [hC.rootCurve_additive]
      _ = C.x moved z := by
        rw [add_neg_cancel, chevalleyX_zero D C P e hC, mul_one]
        apply congrArg (C.x moved)
        dsimp [z, scale]
        ring
  rw [← heq]
  exact hdiff

private lemma extract_q11_table_two
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {alpha delta gamma eta : D.Root} {p q : Nat}
    (halpha : alpha ∈ chainSupport D P e base gamma)
    (hdelta : delta ∈ chainSupport D P e base gamma)
    (hgammaPos : base.IsPos (e gamma))
    (hetaPos : base.IsPos (e eta))
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (heta : P.root (e eta) =
      (p : R) • P.root (e alpha) + (q : R) • P.root (e delta))
    (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 3)
    (hcoord : (p, q) ≠ (1, 1))
    (htable : mixedCoordinateSet D P e alpha delta =
      ({(1, 1), (p, q)} : Set (Nat × Nat))) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e alpha delta
        (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      (a ≠ 0 → ∃ z : k, z ≠ 0 ∧
        HasChainWord D C P e base gamma (C.x gamma z)) := by
  let q11 : ChevalleyCommutatorTerm D.Root := ⟨1, 1, gamma⟩
  let qpq : ChevalleyCommutatorTerm D.Root := ⟨p, q, eta⟩
  have hq11 : IsValidChevalleyCommutatorTerm D P e alpha delta q11 :=
    ⟨by norm_num [q11], by norm_num [q11], by simpa [q11] using hadd⟩
  have hqpq : IsValidChevalleyCommutatorTerm D P e alpha delta qpq :=
    ⟨by simpa [qpq] using hp, by simpa [qpq] using hq,
      by simpa [qpq] using heta⟩
  have hterms : ∀ r,
      IsValidChevalleyCommutatorTerm D P e alpha delta r ↔
        r ∈ [q11, qpq] := by
    intro r
    constructor
    · intro hr
      have hmem : (r.i, r.j) ∈ mixedCoordinateSet D P e alpha delta :=
        ⟨hr.1, hr.2.1, r.root, hr.2.2⟩
      rw [htable] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with hij | hij
      · have hrq : r = q11 :=
          validTerm_eq_of_coordinates D P e hr hij.1 hij.2
            (by simpa [q11] using hadd)
        simp [hrq]
      · have hrq : r = qpq :=
          validTerm_eq_of_coordinates D P e hr hij.1 hij.2
            (by simpa [qpq] using heta)
        simp [hrq]
    · intro hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hq11
      · exact hqpq
  have htermNe : q11 ≠ qpq := by
    intro heq
    apply hcoord
    have hi := congrArg ChevalleyCommutatorTerm.i heq
    have hj := congrArg ChevalleyCommutatorTerm.j heq
    exact Prod.ext (by simpa [q11, qpq] using hi.symm)
      (by simpa [q11, qpq] using hj.symm)
  have hne : gamma ≠ eta :=
    roots_ne_of_distinct_coordinates D P e (a := 1) (b := 1)
      (c := p) (d := q) hLI
      (by simpa only [Nat.cast_one, one_smul] using hadd) heta (by
        intro heq
        exact hcoord heq.symm)
  obtain ⟨c, hcoeff, hword⟩ :=
    exact_commutatorProduct_hasChainWord D C P e base hC halpha hdelta hLI
      [q11, qpq] (by simp [htermNe])
      (by simp [q11, qpq, hpq]) hterms (by
        intro a ha b hb hab
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        all_goals simp_all [q11, qpq])
  refine ⟨c q11, hcoeff q11 (by simp), ?_⟩
  intro hc
  have hLIge : AreLinearlyIndependentRoots D P e gamma eta :=
    positiveRoots_linearlyIndependent D P e base hgammaPos hetaPos hne
  have hLIeg : AreLinearlyIndependentRoots D P e eta gamma :=
    positiveRoots_linearlyIndependent D P e base hetaPos hgammaPos hne.symm
  have hcomm : ∀ s t : k, Commute (C.x gamma s) (C.x eta t) :=
    mixedRoots_commute_of_no_positive_coordinate D C P e hC
      (a := 1) (b := 1) (c := p) (d := q)
      (by simpa only [Nat.cast_one, one_smul] using hadd) heta hLIge
      (by
        intro m n hm hn hex
        have hmem : (m + n * p, m + n * q) ∈
            mixedCoordinateSet D P e alpha delta := by
          refine ⟨by positivity, by positivity, ?_⟩
          obtain ⟨tau, htau⟩ := hex
          refine ⟨tau, ?_⟩
          simpa only [Nat.mul_one, Nat.cast_smul_eq_nsmul R] using htau
        rw [htable] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        have hnp : p ≤ n * p := by nlinarith
        have hnq : q ≤ n * q := by nlinarith
        omega)
  have hreorder :
      C.x gamma (c q11) * C.x eta (c qpq) =
        C.x eta (c qpq) * C.x gamma (c q11) :=
    (hcomm (c q11) (c qpq)).eq
  have hword' : HasChainWord D C P e base gamma
      (C.x gamma (c q11) * C.x eta (c qpq)) := by
    simpa [q11, qpq] using hword
  rw [hreorder] at hword'
  exact isolate_moved_of_commuting_pair_pre D C P e base hC hRoot gamma
    eta gamma (c qpq) (c q11) hword'
      (fun s t => (hcomm t s).symm) hLIeg hc

omit [IsAlgClosed k] in
private lemma extract_q11_table_one
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {alpha delta gamma : D.Root}
    (halpha : alpha ∈ chainSupport D P e base gamma)
    (hdelta : delta ∈ chainSupport D P e base gamma)
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (htable : mixedCoordinateSet D P e alpha delta =
      ({(1, 1)} : Set (Nat × Nat))) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e alpha delta
        (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      HasChainWord D C P e base gamma (C.x gamma a) := by
  obtain ⟨order, c, hnodup, hpairwise, hvalid, hcoeff, hword⟩ :=
    commutatorProduct_hasChainWord D C P e base hC halpha hdelta hLI 1 1
  let q11 : ChevalleyCommutatorTerm D.Root := ⟨1, 1, gamma⟩
  have hq11 : IsValidChevalleyCommutatorTerm D P e alpha delta q11 := by
    exact ⟨by norm_num [q11], by norm_num [q11], by simpa [q11] using hadd⟩
  have hterms : ∀ q,
      IsValidChevalleyCommutatorTerm D P e alpha delta q ↔ q ∈ [q11] := by
    intro q
    constructor
    · intro hq
      have hmem : (q.i, q.j) ∈ mixedCoordinateSet D P e alpha delta :=
        ⟨hq.1, hq.2.1, q.root, hq.2.2⟩
      rw [htable] at hmem
      have hij : q.i = 1 ∧ q.j = 1 := by simpa using hmem
      have hqeq : q = q11 :=
        validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q11] using hadd)
      simp [hqeq]
    · intro hq
      have hqeq : q = q11 := by simpa using hq
      simpa [hqeq] using hq11
  have horder : order = [q11] :=
    commutatorOrder_eq_of_valid_terms D P e order [q11]
      hnodup hpairwise hvalid (by simp) (by simp) hterms (by simp)
  have hq11mem : q11 ∈ order := (hvalid q11).2 hq11
  refine ⟨c q11, hcoeff q11 hq11mem, ?_⟩
  rw [horder] at hword
  simpa [q11] using hword

private lemma isolate_moved_of_commuting_pair
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    (gamma fixed moved : D.Root) (a b : k)
    (hword : HasChainWord D C P e base gamma
      (C.x fixed a * C.x moved b))
    (hcomm : ∀ s t : k, Commute (C.x fixed s) (C.x moved t))
    (hLI : AreLinearlyIndependentRoots D P e fixed moved)
    (hb : b ≠ 0) :
    ∃ z : k, z ≠ 0 ∧
      HasChainWord D C P e base gamma (C.x moved z) := by
  obtain ⟨u, v, hfix, hmove⟩ :=
    exists_pairingSeparator D P e hRoot fixed moved hLI
  let H := C.h moved u * C.h fixed v
  let scale := corootPairScale D fixed moved moved u v
  have hscaled :=
    hword.conjugateCorootPair D C P e base hC fixed moved u v
  have hscaledEq :
      H⁻¹ * (C.x fixed a * C.x moved b) * H =
        C.x fixed a * C.x moved (scale * b) := by
    calc
      H⁻¹ * (C.x fixed a * C.x moved b) * H =
          (H⁻¹ * C.x fixed a * H) *
            (H⁻¹ * C.x moved b * H) := by group
      _ = C.x fixed (corootPairScale D fixed moved fixed u v * a) *
            C.x moved (corootPairScale D fixed moved moved u v * b) := by
        rw [show H = C.h moved u * C.h fixed v by rfl,
          corootPair_conjugates_root D C P e hC,
          corootPair_conjugates_root D C P e hC]
      _ = C.x fixed a * C.x moved (scale * b) := by
        rw [hfix, one_mul]
  rw [hscaledEq] at hscaled
  have hdiff := hscaled.mul D C P e base
    (hword.inv D C P e base hC)
  let z := (scale - 1) * b
  have hz : z ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hmove) hb
  refine ⟨z, hz, ?_⟩
  have heq :
      (C.x fixed a * C.x moved (scale * b)) *
          (C.x fixed a * C.x moved b)⁻¹ = C.x moved z := by
    rw [mul_inv_rev, ← chevalleyX_neg D C P e hC,
      ← chevalleyX_neg D C P e hC]
    calc
      (C.x fixed a * C.x moved (scale * b)) *
          (C.x moved (-b) * C.x fixed (-a)) =
          C.x fixed a *
            (C.x moved (scale * b) * C.x moved (-b)) *
              C.x fixed (-a) := by group
      _ = C.x fixed a * C.x moved (scale * b + -b) *
            C.x fixed (-a) := by rw [hC.rootCurve_additive]
      _ = C.x moved (scale * b + -b) *
            (C.x fixed a * C.x fixed (-a)) := by
        rw [(hcomm a (scale * b + -b)).eq]
        group
      _ = C.x moved (scale * b + -b) * C.x fixed (a + -a) := by
        rw [hC.rootCurve_additive]
      _ = C.x moved z := by
        rw [add_neg_cancel, chevalleyX_zero D C P e hC, mul_one]
        apply congrArg (C.x moved)
        dsimp [z, scale]
        ring
  rw [← heq]
  exact hdiff

private lemma isolate_target_of_commuting_triple
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    (gamma target fixed other : D.Root) (a b c : k)
    (hword : HasChainWord D C P e base gamma
      (C.x target a * C.x fixed b * C.x other c))
    (htf : ∀ s t : k, Commute (C.x target s) (C.x fixed t))
    (hto : ∀ s t : k, Commute (C.x target s) (C.x other t))
    (hfo : ∀ s t : k, Commute (C.x fixed s) (C.x other t))
    (hLIfixed : AreLinearlyIndependentRoots D P e fixed target)
    (hLIother : AreLinearlyIndependentRoots D P e other target)
    (ha : a ≠ 0) :
    ∃ z : k, z ≠ 0 ∧
      HasChainWord D C P e base gamma (C.x target z) := by
  obtain ⟨u, v, hfix, hmove⟩ :=
    exists_pairingSeparator D P e hRoot fixed target hLIfixed
  let H := C.h target u * C.h fixed v
  let st := corootPairScale D fixed target target u v
  let so := corootPairScale D fixed target other u v
  have hscaled :=
    hword.conjugateCorootPair D C P e base hC fixed target u v
  have hscaledEq :
      H⁻¹ * (C.x target a * C.x fixed b * C.x other c) * H =
        C.x target (st * a) * C.x fixed b * C.x other (so * c) := by
    calc
      H⁻¹ * (C.x target a * C.x fixed b * C.x other c) * H =
          (H⁻¹ * C.x target a * H) *
            (H⁻¹ * C.x fixed b * H) *
              (H⁻¹ * C.x other c * H) := by group
      _ = C.x target (corootPairScale D fixed target target u v * a) *
            C.x fixed (corootPairScale D fixed target fixed u v * b) *
              C.x other (corootPairScale D fixed target other u v * c) := by
        rw [show H = C.h target u * C.h fixed v by rfl,
          corootPair_conjugates_root D C P e hC,
          corootPair_conjugates_root D C P e hC,
          corootPair_conjugates_root D C P e hC]
      _ = C.x target (st * a) * C.x fixed b * C.x other (so * c) := by
        rw [hfix, one_mul]
  rw [hscaledEq] at hscaled
  have hdiff := hscaled.mul D C P e base
    (hword.inv D C P e base hC)
  let a' := (st - 1) * a
  let c' := (so - 1) * c
  have ha' : a' ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hmove) ha
  have hdiffEq :
      (C.x target (st * a) * C.x fixed b * C.x other (so * c)) *
          (C.x target a * C.x fixed b * C.x other c)⁻¹ =
        C.x target a' * C.x other c' := by
    rw [mul_inv_rev, mul_inv_rev,
      ← chevalleyX_neg D C P e hC,
      ← chevalleyX_neg D C P e hC,
      ← chevalleyX_neg D C P e hC]
    have hOtherFixedNeg :
        Commute (C.x other (so * c) * C.x other (-c))
          (C.x fixed (-b)) :=
      ((hfo (-b) (so * c)).symm.mul_left (hfo (-b) (-c)).symm)
    have hFixedTargetNeg :
        Commute (C.x fixed b * C.x fixed (-b)) (C.x target (-a)) :=
      ((htf (-a) b).symm.mul_left (htf (-a) (-b)).symm)
    have hOtherTargetNeg :
        Commute (C.x other (so * c) * C.x other (-c))
          (C.x target (-a)) :=
      ((hto (-a) (so * c)).symm.mul_left (hto (-a) (-c)).symm)
    have hRestTargetNeg :
        Commute
          ((C.x fixed b * C.x fixed (-b)) *
            (C.x other (so * c) * C.x other (-c)))
          (C.x target (-a)) :=
      hFixedTargetNeg.mul_left hOtherTargetNeg
    calc
      (C.x target (st * a) * C.x fixed b * C.x other (so * c)) *
          (C.x other (-c) * (C.x fixed (-b) * C.x target (-a))) =
          C.x target (st * a) *
            (C.x fixed b *
              (C.x other (so * c) * C.x other (-c)) * C.x fixed (-b)) *
                C.x target (-a) := by group
      _ = C.x target (st * a) *
            ((C.x fixed b * C.x fixed (-b)) *
              (C.x other (so * c) * C.x other (-c))) *
                C.x target (-a) := by
        rw [mul_assoc (C.x fixed b), hOtherFixedNeg.eq]
        group
      _ = C.x target (st * a) * C.x target (-a) *
            ((C.x fixed b * C.x fixed (-b)) *
              (C.x other (so * c) * C.x other (-c))) := by
        rw [mul_assoc (C.x target (st * a)), hRestTargetNeg.eq]
        group
      _ = C.x target (st * a + -a) *
            (C.x fixed (b + -b) * C.x other (so * c + -c)) := by
        rw [hC.rootCurve_additive, hC.rootCurve_additive, hC.rootCurve_additive]
      _ = C.x target a' * C.x other c' := by
        rw [add_neg_cancel, chevalleyX_zero D C P e hC, one_mul]
        congr 1 <;> dsimp [a', c', st, so] <;> ring
  rw [hdiffEq] at hdiff
  have hreorder :
      C.x target a' * C.x other c' = C.x other c' * C.x target a' :=
    (hto a' c').eq
  rw [hreorder] at hdiff
  exact isolate_moved_of_commuting_pair D C P e base hC hRoot gamma
    other target c' a' hdiff (fun s t => (hto t s).symm) hLIother ha'

private lemma isolate_target_of_linked_four
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    (gamma target fixed other top : D.Root) (a b c d : k)
    (hword : HasChainWord D C P e base gamma
      (C.x target a * C.x fixed b * C.x other c * C.x top d))
    (hto : ∀ s t : k, Commute (C.x target s) (C.x other t))
    (htt : ∀ s t : k, Commute (C.x target s) (C.x top t))
    (hfo : ∀ s t : k, Commute (C.x fixed s) (C.x other t))
    (hft : ∀ s t : k, Commute (C.x fixed s) (C.x top t))
    (hot : ∀ s t : k, Commute (C.x other s) (C.x top t))
    (hLIfixed : AreLinearlyIndependentRoots D P e fixed target)
    (hLIother : AreLinearlyIndependentRoots D P e other target)
    (hLItop : AreLinearlyIndependentRoots D P e top target)
    (ha : a ≠ 0) :
    ∃ z : k, z ≠ 0 ∧
      HasChainWord D C P e base gamma (C.x target z) := by
  obtain ⟨u, v, hfix, hmove⟩ :=
    exists_pairingSeparator D P e hRoot fixed target hLIfixed
  let H := C.h target u * C.h fixed v
  let st := corootPairScale D fixed target target u v
  let so := corootPairScale D fixed target other u v
  let sz := corootPairScale D fixed target top u v
  have hscaled :=
    hword.conjugateCorootPair D C P e base hC fixed target u v
  have hscaledEq :
      H⁻¹ * (C.x target a * C.x fixed b * C.x other c * C.x top d) * H =
        C.x target (st * a) * C.x fixed b *
          C.x other (so * c) * C.x top (sz * d) := by
    calc
      H⁻¹ * (C.x target a * C.x fixed b * C.x other c * C.x top d) * H =
          (H⁻¹ * C.x target a * H) * (H⁻¹ * C.x fixed b * H) *
            (H⁻¹ * C.x other c * H) * (H⁻¹ * C.x top d * H) := by group
      _ = C.x target (corootPairScale D fixed target target u v * a) *
            C.x fixed (corootPairScale D fixed target fixed u v * b) *
              C.x other (corootPairScale D fixed target other u v * c) *
                C.x top (corootPairScale D fixed target top u v * d) := by
        rw [show H = C.h target u * C.h fixed v by rfl,
          corootPair_conjugates_root D C P e hC,
          corootPair_conjugates_root D C P e hC,
          corootPair_conjugates_root D C P e hC,
          corootPair_conjugates_root D C P e hC]
      _ = C.x target (st * a) * C.x fixed b *
            C.x other (so * c) * C.x top (sz * d) := by
        rw [hfix, one_mul]
  rw [hscaledEq] at hscaled
  have hdiff := hscaled.mul D C P e base
    (hword.inv D C P e base hC)
  let a' := (st - 1) * a
  let c' := (so - 1) * c
  let d' := (sz - 1) * d
  let Y := (C.x other (so * c) * C.x top (sz * d)) *
    (C.x top (-d) * C.x other (-c))
  have ha' : a' ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hmove) ha
  have hYfixed : Commute Y (C.x fixed (-b)) := by
    dsimp [Y]
    exact (((hfo (-b) (so * c)).symm.mul_left
      (hft (-b) (sz * d)).symm).mul_left
        ((hft (-b) (-d)).symm.mul_left (hfo (-b) (-c)).symm))
  have hYtarget : Commute Y (C.x target (-a)) := by
    dsimp [Y]
    exact (((hto (-a) (so * c)).symm.mul_left
      (htt (-a) (sz * d)).symm).mul_left
        ((htt (-a) (-d)).symm.mul_left (hto (-a) (-c)).symm))
  have hTopPairOtherNeg :
      Commute (C.x top (sz * d) * C.x top (-d)) (C.x other (-c)) :=
    (hot (-c) (sz * d)).symm.mul_left (hot (-c) (-d)).symm
  have hYeq : Y = C.x other c' * C.x top d' := by
    dsimp [Y]
    calc
      (C.x other (so * c) * C.x top (sz * d)) *
          (C.x top (-d) * C.x other (-c)) =
          C.x other (so * c) *
            ((C.x top (sz * d) * C.x top (-d)) * C.x other (-c)) := by group
      _ = C.x other (so * c) *
            (C.x other (-c) * (C.x top (sz * d) * C.x top (-d))) := by
        rw [hTopPairOtherNeg.eq]
      _ = (C.x other (so * c) * C.x other (-c)) *
            (C.x top (sz * d) * C.x top (-d)) := by group
      _ = C.x other (so * c + -c) * C.x top (sz * d + -d) := by
        rw [hC.rootCurve_additive, hC.rootCurve_additive]
      _ = C.x other c' * C.x top d' := by
        congr 1 <;> dsimp [c', d', so, sz] <;> ring
  have hdiffEq :
      (C.x target (st * a) * C.x fixed b *
          C.x other (so * c) * C.x top (sz * d)) *
        (C.x target a * C.x fixed b * C.x other c * C.x top d)⁻¹ =
          C.x target a' * C.x other c' * C.x top d' := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev,
      ← chevalleyX_neg D C P e hC,
      ← chevalleyX_neg D C P e hC,
      ← chevalleyX_neg D C P e hC,
      ← chevalleyX_neg D C P e hC]
    calc
      (C.x target (st * a) * C.x fixed b *
          C.x other (so * c) * C.x top (sz * d)) *
          (C.x top (-d) * (C.x other (-c) *
            (C.x fixed (-b) * C.x target (-a)))) =
          C.x target (st * a) * C.x fixed b * Y *
            C.x fixed (-b) * C.x target (-a) := by
        dsimp [Y]
        group
      _ = C.x target (st * a) *
          (C.x fixed b * C.x fixed (-b)) * Y * C.x target (-a) := by
        calc
          C.x target (st * a) * C.x fixed b * Y *
              C.x fixed (-b) * C.x target (-a) =
              C.x target (st * a) * C.x fixed b *
                (Y * C.x fixed (-b)) * C.x target (-a) := by group
          _ = C.x target (st * a) * C.x fixed b *
                (C.x fixed (-b) * Y) * C.x target (-a) := by
            rw [hYfixed.eq]
          _ = C.x target (st * a) *
                (C.x fixed b * C.x fixed (-b)) * Y *
                  C.x target (-a) := by group
      _ = C.x target (st * a) * Y * C.x target (-a) := by
        rw [hC.rootCurve_additive, add_neg_cancel,
          chevalleyX_zero D C P e hC]
        group
      _ = C.x target (st * a) * (Y * C.x target (-a)) := by group
      _ = C.x target (st * a) * (C.x target (-a) * Y) := by
        rw [hYtarget.eq]
      _ = (C.x target (st * a) * C.x target (-a)) * Y := by group
      _ = C.x target (st * a + -a) * Y := by rw [hC.rootCurve_additive]
      _ = C.x target a' * Y := by
        congr 1
        dsimp [a', st]
        ring
      _ = C.x target a' * (C.x other c' * C.x top d') := by rw [hYeq]
      _ = C.x target a' * C.x other c' * C.x top d' := by group
  rw [hdiffEq] at hdiff
  exact isolate_target_of_commuting_triple D C P e base hC hRoot gamma
    target other top a' c' d' hdiff hto htt hot hLIother hLItop ha'

private lemma extract_q11_table_mixed
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {alpha delta gamma eta12 eta21 : D.Root}
    (halpha : alpha ∈ chainSupport D P e base gamma)
    (hdelta : delta ∈ chainSupport D P e base gamma)
    (hgammaPos : base.IsPos (e gamma))
    (heta12Pos : base.IsPos (e eta12))
    (heta21Pos : base.IsPos (e eta21))
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (heta12 : P.root (e eta12) =
      P.root (e alpha) + (2 : R) • P.root (e delta))
    (heta21 : P.root (e eta21) =
      (2 : R) • P.root (e alpha) + P.root (e delta))
    (htable : mixedCoordinateSet D P e alpha delta =
      ({(1, 1), (1, 2), (2, 1)} : Set (Nat × Nat))) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e alpha delta
        (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      (a ≠ 0 → ∃ z : k, z ≠ 0 ∧
        HasChainWord D C P e base gamma (C.x gamma z)) := by
  let q11 : ChevalleyCommutatorTerm D.Root := ⟨1, 1, gamma⟩
  let q12 : ChevalleyCommutatorTerm D.Root := ⟨1, 2, eta12⟩
  let q21 : ChevalleyCommutatorTerm D.Root := ⟨2, 1, eta21⟩
  have hq11 : IsValidChevalleyCommutatorTerm D P e alpha delta q11 :=
    ⟨by norm_num [q11], by norm_num [q11], by simpa [q11] using hadd⟩
  have hq12 : IsValidChevalleyCommutatorTerm D P e alpha delta q12 :=
    ⟨by norm_num [q12], by norm_num [q12], by simpa [q12] using heta12⟩
  have hq21 : IsValidChevalleyCommutatorTerm D P e alpha delta q21 :=
    ⟨by norm_num [q21], by norm_num [q21], by simpa [q21] using heta21⟩
  have hterms : ∀ r,
      IsValidChevalleyCommutatorTerm D P e alpha delta r ↔
        r ∈ [q11, q12, q21] := by
    intro r
    constructor
    · intro hr
      have hmem : (r.i, r.j) ∈ mixedCoordinateSet D P e alpha delta :=
        ⟨hr.1, hr.2.1, r.root, hr.2.2⟩
      rw [htable] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with hij | hij | hij
      · have : r = q11 :=
          validTerm_eq_of_coordinates D P e hr hij.1 hij.2
            (by simpa [q11] using hadd)
        simp [this]
      · have : r = q12 :=
          validTerm_eq_of_coordinates D P e hr hij.1 hij.2
            (by simpa [q12] using heta12)
        simp [this]
      · have : r = q21 :=
          validTerm_eq_of_coordinates D P e hr hij.1 hij.2
            (by simpa [q21] using heta21)
        simp [this]
    · intro hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hq11
      · exact hq12
      · exact hq21
  have hgamma12 : gamma ≠ eta12 :=
    roots_ne_of_distinct_coordinates D P e (a := 1) (b := 1)
      (c := 1) (d := 2) hLI
      (by simpa only [Nat.cast_one, one_smul] using hadd)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using heta12)
      (by decide)
  have hgamma21 : gamma ≠ eta21 :=
    roots_ne_of_distinct_coordinates D P e (a := 1) (b := 1)
      (c := 2) (d := 1) hLI
      (by simpa only [Nat.cast_one, one_smul] using hadd)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using heta21)
      (by decide)
  have hetaNe : eta12 ≠ eta21 :=
    roots_ne_of_distinct_coordinates D P e (a := 1) (b := 2)
      (c := 2) (d := 1) hLI
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using heta12)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using heta21)
      (by decide)
  have hLIgamma12 := positiveRoots_linearlyIndependent D P e base
    hgammaPos heta12Pos hgamma12
  have hLIgamma21 := positiveRoots_linearlyIndependent D P e base
    hgammaPos heta21Pos hgamma21
  have hLI1221 := positiveRoots_linearlyIndependent D P e base
    heta12Pos heta21Pos hetaNe
  have hcommGamma12 : ∀ s t : k, Commute (C.x gamma s) (C.x eta12 t) :=
    mixedRoots_commute_of_no_positive_coordinate D C P e hC
      (a := 1) (b := 1) (c := 1) (d := 2)
      (by simpa only [Nat.cast_one, one_smul] using hadd)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using heta12)
      hLIgamma12 (by
        intro m n hm hn hex
        have hmem : (m + n, m + 2 * n) ∈
            mixedCoordinateSet D P e alpha delta := by
          refine ⟨by omega, by omega, ?_⟩
          obtain ⟨tau, htau⟩ := hex
          exact ⟨tau, by
            simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm n 2,
              Nat.cast_smul_eq_nsmul R]
              using htau⟩
        rw [htable] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        omega)
  have hcommGamma21 : ∀ s t : k, Commute (C.x gamma s) (C.x eta21 t) :=
    mixedRoots_commute_of_no_positive_coordinate D C P e hC
      (a := 1) (b := 1) (c := 2) (d := 1)
      (by simpa only [Nat.cast_one, one_smul] using hadd)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using heta21)
      hLIgamma21 (by
        intro m n hm hn hex
        have hmem : (m + 2 * n, m + n) ∈
            mixedCoordinateSet D P e alpha delta := by
          refine ⟨by omega, by omega, ?_⟩
          obtain ⟨tau, htau⟩ := hex
          exact ⟨tau, by
            simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm n 2,
              Nat.cast_smul_eq_nsmul R]
              using htau⟩
        rw [htable] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        omega)
  have hcomm1221 : ∀ s t : k, Commute (C.x eta12 s) (C.x eta21 t) :=
    mixedRoots_commute_of_no_positive_coordinate D C P e hC
      (a := 1) (b := 2) (c := 2) (d := 1)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using heta12)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using heta21)
      hLI1221 (by
        intro m n hm hn hex
        have hmem : (m + 2 * n, 2 * m + n) ∈
            mixedCoordinateSet D P e alpha delta := by
          refine ⟨by omega, by omega, ?_⟩
          obtain ⟨tau, htau⟩ := hex
          exact ⟨tau, by
            simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm n 2,
              Nat.mul_comm m 2, Nat.cast_smul_eq_nsmul R]
              using htau⟩
        rw [htable] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        omega)
  obtain ⟨c, hcoeff, hword⟩ :=
    exact_commutatorProduct_hasChainWord_of_commuting_terms D C P e base hC
      halpha hdelta hLI [q11, q12, q21] (by simp [q11, q12, q21]) hterms
      (by
        intro a ha b hb hab s t
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl
        · exact (hab rfl).elim
        · exact hcommGamma12 s t
        · exact hcommGamma21 s t
        · exact (hcommGamma12 t s).symm
        · exact (hab rfl).elim
        · exact hcomm1221 s t
        · exact (hcommGamma21 t s).symm
        · exact (hcomm1221 t s).symm
        · exact (hab rfl).elim)
  refine ⟨c q11, hcoeff q11 (by simp), ?_⟩
  intro hc
  have hword' : HasChainWord D C P e base gamma
      (C.x gamma (c q11) * C.x eta12 (c q12) * C.x eta21 (c q21)) := by
    simpa [q11, q12, q21, mul_assoc] using hword
  exact isolate_target_of_commuting_triple D C P e base hC hRoot gamma
    gamma eta12 eta21 (c q11) (c q12) (c q21) hword'
    hcommGamma12 hcommGamma21 hcomm1221
    (positiveRoots_linearlyIndependent D P e base heta12Pos hgammaPos hgamma12.symm)
    (positiveRoots_linearlyIndependent D P e base heta21Pos hgammaPos hgamma21.symm)
    hc

private lemma extract_q11_table_four
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {alpha delta gamma linked other top : D.Root}
    {p q r s : Nat}
    (halpha : alpha ∈ chainSupport D P e base gamma)
    (hdelta : delta ∈ chainSupport D P e base gamma)
    (hgammaPos : base.IsPos (e gamma))
    (hlinkedPos : base.IsPos (e linked))
    (hotherPos : base.IsPos (e other))
    (htopPos : base.IsPos (e top))
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (hlinked : P.root (e linked) =
      (p : R) • P.root (e alpha) + (q : R) • P.root (e delta))
    (hother : P.root (e other) =
      (r : R) • P.root (e alpha) + (s : R) • P.root (e delta))
    (htop : P.root (e top) =
      (p + 1 : R) • P.root (e alpha) +
        (q + 1 : R) • P.root (e delta))
    (hshape : (p = 1 ∧ q = 2 ∧ r = 1 ∧ s = 3) ∨
      (p = 2 ∧ q = 1 ∧ r = 3 ∧ s = 1))
    (htable : mixedCoordinateSet D P e alpha delta =
      ({(1, 1), (p, q), (r, s), (p + 1, q + 1)} : Set (Nat × Nat))) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e alpha delta
        (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      (a ≠ 0 → ∃ z : k, z ≠ 0 ∧
        HasChainWord D C P e base gamma (C.x gamma z)) := by
  let q11 : ChevalleyCommutatorTerm D.Root := ⟨1, 1, gamma⟩
  let qpq : ChevalleyCommutatorTerm D.Root := ⟨p, q, linked⟩
  let qrs : ChevalleyCommutatorTerm D.Root := ⟨r, s, other⟩
  let qtop : ChevalleyCommutatorTerm D.Root := ⟨p + 1, q + 1, top⟩
  have hp : 0 < p := by rcases hshape with h | h <;> omega
  have hq : 0 < q := by rcases hshape with h | h <;> omega
  have hr : 0 < r := by rcases hshape with h | h <;> omega
  have hs : 0 < s := by rcases hshape with h | h <;> omega
  have hpq : p + q = 3 := by rcases hshape with h | h <;> omega
  have hrs : r + s = 4 := by rcases hshape with h | h <;> omega
  have hq11 : IsValidChevalleyCommutatorTerm D P e alpha delta q11 :=
    ⟨by norm_num [q11], by norm_num [q11], by simpa [q11] using hadd⟩
  have hqpq : IsValidChevalleyCommutatorTerm D P e alpha delta qpq :=
    ⟨by simpa [qpq] using hp, by simpa [qpq] using hq,
      by simpa [qpq] using hlinked⟩
  have hqrs : IsValidChevalleyCommutatorTerm D P e alpha delta qrs :=
    ⟨by simpa [qrs] using hr, by simpa [qrs] using hs,
      by simpa [qrs] using hother⟩
  have hqtop : IsValidChevalleyCommutatorTerm D P e alpha delta qtop :=
    ⟨by simp [qtop], by simp [qtop], by simpa [qtop] using htop⟩
  have hterms : ∀ u,
      IsValidChevalleyCommutatorTerm D P e alpha delta u ↔
        u ∈ [q11, qpq, qrs, qtop] := by
    intro u
    constructor
    · intro hu
      have hmem : (u.i, u.j) ∈ mixedCoordinateSet D P e alpha delta :=
        ⟨hu.1, hu.2.1, u.root, hu.2.2⟩
      rw [htable] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with hij | hij | hij | hij
      · have : u = q11 := validTerm_eq_of_coordinates D P e hu hij.1 hij.2
          (by simpa [q11] using hadd)
        simp [this]
      · have : u = qpq := validTerm_eq_of_coordinates D P e hu hij.1 hij.2
          (by simpa [qpq] using hlinked)
        simp [this]
      · have : u = qrs := validTerm_eq_of_coordinates D P e hu hij.1 hij.2
          (by simpa [qrs] using hother)
        simp [this]
      · have : u = qtop := validTerm_eq_of_coordinates D P e hu hij.1 hij.2
          (by simpa [qtop] using htop)
        simp [this]
    · intro hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact hq11
      · exact hqpq
      · exact hqrs
      · exact hqtop
  have htermsNodup : [q11, qpq, qrs, qtop].Nodup := by
    rcases hshape with h | h <;> rcases h with ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [q11, qpq, qrs, qtop]
  have htermsPairwise : [q11, qpq, qrs, qtop].Pairwise
      (fun a b => a.i + a.j ≤ b.i + b.j) := by
    simp [q11, qpq, qrs, qtop]
    omega
  have hdegreeInj : ∀ a ∈ [q11, qpq, qrs, qtop],
      ∀ b ∈ [q11, qpq, qrs, qtop], a.i + a.j = b.i + b.j → a = b := by
    intro a ha b hb hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl
    all_goals first | rfl | (exfalso; simp [q11, qpq, qrs, qtop] at hab; omega)
  have rootNe (rho sigma : D.Root) (a b c d : Nat)
      (hrho : P.root (e rho) =
        (a : R) • P.root (e alpha) + (b : R) • P.root (e delta))
      (hsigma : P.root (e sigma) =
        (c : R) • P.root (e alpha) + (d : R) • P.root (e delta))
      (hcoord : (a, b) ≠ (c, d)) : rho ≠ sigma :=
    roots_ne_of_distinct_coordinates D P e hLI hrho hsigma hcoord
  have hgammaOther : gamma ≠ other := rootNe gamma other 1 1 r s
    (by simpa only [Nat.cast_one, one_smul] using hadd) hother (by
      intro heq
      simp only [Prod.mk.injEq] at heq
      rcases hshape with ⟨hp, hq, hr, hs⟩ | ⟨hp, hq, hr, hs⟩ <;> omega)
  have hgammaTop : gamma ≠ top := rootNe gamma top 1 1 (p + 1) (q + 1)
    (by simpa only [Nat.cast_one, one_smul] using hadd)
    (by simpa only [Nat.cast_add, Nat.cast_one] using htop) (by
      intro heq
      simp only [Prod.mk.injEq] at heq
      rcases hshape with ⟨hp, hq, hr, hs⟩ | ⟨hp, hq, hr, hs⟩ <;> omega)
  have hlinkedOther : linked ≠ other := rootNe linked other p q r s
    hlinked hother (by
      intro heq
      simp only [Prod.mk.injEq] at heq
      rcases hshape with ⟨hp, hq, hr, hs⟩ | ⟨hp, hq, hr, hs⟩ <;> omega)
  have hlinkedTop : linked ≠ top := rootNe linked top p q (p + 1) (q + 1)
    hlinked (by simpa only [Nat.cast_add, Nat.cast_one] using htop) (by
      intro heq
      simp only [Prod.mk.injEq] at heq
      omega)
  have hotherTop : other ≠ top := rootNe other top r s (p + 1) (q + 1)
    hother (by simpa only [Nat.cast_add, Nat.cast_one] using htop) (by
      intro heq
      simp only [Prod.mk.injEq] at heq
      rcases hshape with ⟨hp, hq, hr, hs⟩ | ⟨hp, hq, hr, hs⟩ <;> omega)
  have hgammaLinked : gamma ≠ linked := rootNe gamma linked 1 1 p q
    (by simpa only [Nat.cast_one, one_smul] using hadd) hlinked (by
      intro heq
      simp only [Prod.mk.injEq] at heq
      rcases hshape with ⟨hp, hq, hr, hs⟩ | ⟨hp, hq, hr, hs⟩ <;> omega)
  have hLIgammaOther := positiveRoots_linearlyIndependent D P e base
    hgammaPos hotherPos hgammaOther
  have hLIgammaTop := positiveRoots_linearlyIndependent D P e base
    hgammaPos htopPos hgammaTop
  have hLIlinkedOther := positiveRoots_linearlyIndependent D P e base
    hlinkedPos hotherPos hlinkedOther
  have hLIlinkedTop := positiveRoots_linearlyIndependent D P e base
    hlinkedPos htopPos hlinkedTop
  have hLIotherTop := positiveRoots_linearlyIndependent D P e base
    hotherPos htopPos hotherTop
  have hNoGammaOther : ∀ m n : Nat, 0 < m → 0 < n →
      (m + n * r, m + n * s) ∉
        ({(1, 1), (p, q), (r, s), (p + 1, q + 1)} : Set (Nat × Nat)) := by
    intro m n hm hn hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hshape with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> omega
  have hNoGammaTop : ∀ m n : Nat, 0 < m → 0 < n →
      (m + n * (p + 1), m + n * (q + 1)) ∉
        ({(1, 1), (p, q), (r, s), (p + 1, q + 1)} : Set (Nat × Nat)) := by
    intro m n hm hn hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hshape with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> omega
  have hNoLinkedOther : ∀ m n : Nat, 0 < m → 0 < n →
      (m * p + n * r, m * q + n * s) ∉
        ({(1, 1), (p, q), (r, s), (p + 1, q + 1)} : Set (Nat × Nat)) := by
    intro m n hm hn hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hshape with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> omega
  have hNoLinkedTop : ∀ m n : Nat, 0 < m → 0 < n →
      (m * p + n * (p + 1), m * q + n * (q + 1)) ∉
        ({(1, 1), (p, q), (r, s), (p + 1, q + 1)} : Set (Nat × Nat)) := by
    intro m n hm hn hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hshape with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> omega
  have hNoOtherTop : ∀ m n : Nat, 0 < m → 0 < n →
      (m * r + n * (p + 1), m * s + n * (q + 1)) ∉
        ({(1, 1), (p, q), (r, s), (p + 1, q + 1)} : Set (Nat × Nat)) := by
    intro m n hm hn hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hshape with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> omega
  have hcommGammaOther : ∀ x y : k, Commute (C.x gamma x) (C.x other y) :=
    mixedRoots_commute_of_table_exclusion D C P e hC
      (a := 1) (b := 1) (c := r) (d := s) (by omega) (by omega) hr hs
      (by simpa only [Nat.cast_one, one_smul] using hadd) hother
      hLIgammaOther htable (by
        intro m n hm hn
        simpa only [Nat.mul_one] using hNoGammaOther m n hm hn)
  have hcommGammaTop : ∀ x y : k, Commute (C.x gamma x) (C.x top y) :=
    mixedRoots_commute_of_table_exclusion D C P e hC
      (a := 1) (b := 1) (c := p + 1) (d := q + 1)
      (by omega) (by omega) (by omega) (by omega)
      (by simpa only [Nat.cast_one, one_smul] using hadd)
      (by simpa only [Nat.cast_add, Nat.cast_one] using htop)
      hLIgammaTop htable (by
        intro m n hm hn
        simpa only [Nat.mul_one] using hNoGammaTop m n hm hn)
  have hcommLinkedOther : ∀ x y : k, Commute (C.x linked x) (C.x other y) :=
    mixedRoots_commute_of_table_exclusion D C P e hC
      hp hq hr hs hlinked hother hLIlinkedOther htable
      hNoLinkedOther
  have hcommLinkedTop : ∀ x y : k, Commute (C.x linked x) (C.x top y) :=
    mixedRoots_commute_of_table_exclusion D C P e hC
      hp hq (by omega) (by omega) hlinked
      (by simpa only [Nat.cast_add, Nat.cast_one] using htop)
      hLIlinkedTop htable hNoLinkedTop
  have hcommOtherTop : ∀ x y : k, Commute (C.x other x) (C.x top y) :=
    mixedRoots_commute_of_table_exclusion D C P e hC
      hr hs (by omega) (by omega) hother
      (by simpa only [Nat.cast_add, Nat.cast_one] using htop)
      hLIotherTop htable hNoOtherTop
  obtain ⟨c, hcoeff, hword⟩ :=
    exact_commutatorProduct_hasChainWord D C P e base hC halpha hdelta hLI
      [q11, qpq, qrs, qtop] htermsNodup htermsPairwise hterms hdegreeInj
  refine ⟨c q11, hcoeff q11 (by simp), ?_⟩
  intro hc
  have hword' : HasChainWord D C P e base gamma
      (C.x gamma (c q11) * C.x linked (c qpq) *
        C.x other (c qrs) * C.x top (c qtop)) := by
    simpa [q11, qpq, qrs, qtop, mul_assoc] using hword
  exact isolate_target_of_linked_four D C P e base hC hRoot gamma
    gamma linked other top (c q11) (c qpq) (c qrs) (c qtop) hword'
    hcommGammaOther hcommGammaTop hcommLinkedOther hcommLinkedTop hcommOtherTop
    (positiveRoots_linearlyIndependent D P e base hlinkedPos hgammaPos
      hgammaLinked.symm)
    (positiveRoots_linearlyIndependent D P e base hotherPos hgammaPos
      hgammaOther.symm)
    (positiveRoots_linearlyIndependent D P e base htopPos hgammaPos
      hgammaTop.symm) hc

private lemma extract_q11_from_rankTwoTable
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {alpha delta gamma : D.Root}
    (hdelta : e delta ∈ base.support)
    (halphaPos : base.IsPos (e alpha))
    (hgammaPos : base.IsPos (e gamma))
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta)) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e alpha delta
        (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      (a ≠ 0 → ∃ z : k, z ≠ 0 ∧
        HasChainWord D C P e base gamma (C.x gamma z)) := by
  have hdeltaPos : base.IsPos (e delta) := base.isPos_of_mem_support hdelta
  obtain ⟨halpha, hdeltaChain⟩ :=
    chainSupport_alpha_delta D P e base hdelta halphaPos hadd
  have htables := rankTwoPositiveMixedRootCoordinates_cases P base hdelta
    halphaPos hgammaPos hadd
  have hmixed :
      {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root (e alpha) +
            (ij.2 : R) • P.root (e delta)} =
        mixedCoordinateSet D P e alpha delta := by
    ext ij
    simp only [mixedCoordinateSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hi, hj, rho, hrho⟩
      exact ⟨hi, hj, e.symm rho, by simpa using hrho⟩
    · rintro ⟨hi, hj, rho, hrho⟩
      exact ⟨hi, hj, e rho, hrho⟩
  rw [hmixed] at htables
  rcases htables with htable | htable | htable | htable | htable | htable
  · obtain ⟨a, ha, hword⟩ :=
      extract_q11_table_one D C P e base hC halpha hdeltaChain hLI hadd htable
    exact ⟨a, ha, fun ha0 => ⟨a, ha0, hword⟩⟩
  · have hmem : (1, 2) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    obtain ⟨_, _, eta, heta⟩ := hmem
    have hetaPos : base.IsPos (e eta) :=
      hgammaPos.add hdeltaPos (by rw [heta, hadd]; module)
    exact extract_q11_table_two D C P e base hC hRoot halpha hdeltaChain
      hgammaPos hetaPos hLI hadd heta (p := 1) (q := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) htable
  · have hmem : (2, 1) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    obtain ⟨_, _, eta, heta⟩ := hmem
    have hetaPos : base.IsPos (e eta) :=
      hgammaPos.add halphaPos (by rw [heta, hadd]; module)
    exact extract_q11_table_two D C P e base hC hRoot halpha hdeltaChain
      hgammaPos hetaPos hLI hadd heta (p := 2) (q := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) htable
  · have hmem12 : (1, 2) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    have hmem13 : (1, 3) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    have hmem23 : (2, 3) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    obtain ⟨_, _, eta12, heta12⟩ := hmem12
    obtain ⟨_, _, eta13, heta13⟩ := hmem13
    obtain ⟨_, _, eta23, heta23⟩ := hmem23
    have heta12Pos : base.IsPos (e eta12) :=
      hgammaPos.add hdeltaPos (by rw [heta12, hadd]; module)
    have heta13Pos : base.IsPos (e eta13) :=
      heta12Pos.add hdeltaPos (by rw [heta13, heta12]; module)
    have heta23Pos : base.IsPos (e eta23) :=
      heta13Pos.add halphaPos (by rw [heta23, heta13]; module)
    exact extract_q11_table_four D C P e base hC hRoot halpha hdeltaChain
      hgammaPos heta12Pos heta13Pos heta23Pos hLI hadd heta12 heta13
      (by norm_num; exact heta23)
      (p := 1) (q := 2) (r := 1) (s := 3)
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by simpa using htable)
  · have hmem21 : (2, 1) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    have hmem31 : (3, 1) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    have hmem32 : (3, 2) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    obtain ⟨_, _, eta21, heta21⟩ := hmem21
    obtain ⟨_, _, eta31, heta31⟩ := hmem31
    obtain ⟨_, _, eta32, heta32⟩ := hmem32
    have heta21Pos : base.IsPos (e eta21) :=
      hgammaPos.add halphaPos (by rw [heta21, hadd]; module)
    have heta31Pos : base.IsPos (e eta31) :=
      heta21Pos.add halphaPos (by rw [heta31, heta21]; module)
    have heta32Pos : base.IsPos (e eta32) :=
      heta31Pos.add hdeltaPos (by rw [heta32, heta31]; module)
    exact extract_q11_table_four D C P e base hC hRoot halpha hdeltaChain
      hgammaPos heta21Pos heta31Pos heta32Pos hLI hadd heta21 heta31
      (by norm_num; exact heta32)
      (p := 2) (q := 1) (r := 3) (s := 1)
      (Or.inr ⟨rfl, rfl, rfl, rfl⟩) (by simpa using htable)
  · have hmem12 : (1, 2) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    have hmem21 : (2, 1) ∈ mixedCoordinateSet D P e alpha delta := by
      rw [htable]
      simp
    obtain ⟨_, _, eta12, heta12⟩ := hmem12
    obtain ⟨_, _, eta21, heta21⟩ := hmem21
    have heta12Pos : base.IsPos (e eta12) :=
      hgammaPos.add hdeltaPos (by rw [heta12, hadd]; module)
    have heta21Pos : base.IsPos (e eta21) :=
      hgammaPos.add halphaPos (by rw [heta21, hadd]; module)
    exact extract_q11_table_mixed D C P e base hC hRoot halpha hdeltaChain
      hgammaPos heta12Pos heta21Pos hLI hadd
      (by norm_num at heta12 ⊢; exact heta12)
      (by norm_num at heta21 ⊢; exact heta21) htable

omit [IsAlgClosed k] in
private lemma extract_q12_table_two
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    {beta delta eta target goal : D.Root}
    (hbeta : beta ∈ chainSupport D P e base goal)
    (hdelta : delta ∈ chainSupport D P e base goal)
    (hetaChain : eta ∈ chainSupport D P e base goal)
    (hLI : AreLinearlyIndependentRoots D P e beta delta)
    (heta : P.root (e eta) =
      P.root (e beta) + P.root (e delta))
    (htarget : P.root (e target) =
      P.root (e beta) + (2 : R) • P.root (e delta))
    (htable : mixedCoordinateSet D P e beta delta =
      ({(1, 1), (1, 2)} : Set (Nat × Nat))) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e beta delta
        (⟨1, 2, target⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      HasChainWord D C P e base goal (C.x target a) := by
  let q11 : ChevalleyCommutatorTerm D.Root := ⟨1, 1, eta⟩
  let q12 : ChevalleyCommutatorTerm D.Root := ⟨1, 2, target⟩
  have hq11 : IsValidChevalleyCommutatorTerm D P e beta delta q11 :=
    ⟨by norm_num [q11], by norm_num [q11], by simpa [q11] using heta⟩
  have hq12 : IsValidChevalleyCommutatorTerm D P e beta delta q12 :=
    ⟨by norm_num [q12], by norm_num [q12], by simpa [q12] using htarget⟩
  have hterms : ∀ q,
      IsValidChevalleyCommutatorTerm D P e beta delta q ↔
        q ∈ [q11, q12] := by
    intro q
    constructor
    · intro hq
      have hmem : (q.i, q.j) ∈ mixedCoordinateSet D P e beta delta :=
        ⟨hq.1, hq.2.1, q.root, hq.2.2⟩
      rw [htable] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with hij | hij
      · have : q = q11 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q11] using heta)
        simp [this]
      · have : q = q12 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q12] using htarget)
        simp [this]
    · intro hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hq11
      · exact hq12
  obtain ⟨c, hcoeff, hword⟩ :=
    exact_commutatorProduct_hasChainWord D C P e base hC hbeta hdelta hLI
      [q11, q12] (by simp [q11, q12]) (by simp [q11, q12]) hterms (by
        intro a ha b hb hab
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        all_goals simp_all [q11, q12])
  refine ⟨c q12, hcoeff q12 (by simp), ?_⟩
  have hword' : HasChainWord D C P e base goal
      (C.x eta (c q11) * C.x target (c q12)) := by
    simpa [q11, q12] using hword
  exact HasChainWord.cancel_left D C P e base hC
    (hasChainWord_x D C P e base goal eta (c q11) hetaChain) hword'

set_option maxHeartbeats 800000 in
private lemma extract_q12_table_four
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {beta delta eta target other top goal : D.Root}
    (hbeta : beta ∈ chainSupport D P e base goal)
    (hdelta : delta ∈ chainSupport D P e base goal)
    (hetaChain : eta ∈ chainSupport D P e base goal)
    (htargetPos : base.IsPos (e target))
    (hotherPos : base.IsPos (e other))
    (htopPos : base.IsPos (e top))
    (hLI : AreLinearlyIndependentRoots D P e beta delta)
    (heta : P.root (e eta) =
      P.root (e beta) + P.root (e delta))
    (htarget : P.root (e target) =
      P.root (e beta) + (2 : R) • P.root (e delta))
    (hother : P.root (e other) =
      P.root (e beta) + (3 : R) • P.root (e delta))
    (htop : P.root (e top) =
      (2 : R) • P.root (e beta) + (3 : R) • P.root (e delta))
    (htable : mixedCoordinateSet D P e beta delta =
      ({(1, 1), (1, 2), (1, 3), (2, 3)} : Set (Nat × Nat))) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e beta delta
        (⟨1, 2, target⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      (a ≠ 0 → ∃ z : k, z ≠ 0 ∧
        HasChainWord D C P e base goal (C.x target z)) := by
  let q11 : ChevalleyCommutatorTerm D.Root := ⟨1, 1, eta⟩
  let q12 : ChevalleyCommutatorTerm D.Root := ⟨1, 2, target⟩
  let q13 : ChevalleyCommutatorTerm D.Root := ⟨1, 3, other⟩
  let q23 : ChevalleyCommutatorTerm D.Root := ⟨2, 3, top⟩
  have hq11 : IsValidChevalleyCommutatorTerm D P e beta delta q11 :=
    ⟨by norm_num [q11], by norm_num [q11], by simpa [q11] using heta⟩
  have hq12 : IsValidChevalleyCommutatorTerm D P e beta delta q12 :=
    ⟨by norm_num [q12], by norm_num [q12], by simpa [q12] using htarget⟩
  have hq13 : IsValidChevalleyCommutatorTerm D P e beta delta q13 :=
    ⟨by norm_num [q13], by norm_num [q13], by simpa [q13] using hother⟩
  have hq23 : IsValidChevalleyCommutatorTerm D P e beta delta q23 :=
    ⟨by norm_num [q23], by norm_num [q23], by simpa [q23] using htop⟩
  have hterms : ∀ q,
      IsValidChevalleyCommutatorTerm D P e beta delta q ↔
        q ∈ [q11, q12, q13, q23] := by
    intro q
    constructor
    · intro hq
      have hmem : (q.i, q.j) ∈ mixedCoordinateSet D P e beta delta :=
        ⟨hq.1, hq.2.1, q.root, hq.2.2⟩
      rw [htable] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with hij | hij | hij | hij
      · have : q = q11 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q11] using heta)
        simp [this]
      · have : q = q12 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q12] using htarget)
        simp [this]
      · have : q = q13 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q13] using hother)
        simp [this]
      · have : q = q23 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q23] using htop)
        simp [this]
    · intro hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hq11
      · exact hq12
      · exact hq13
      · exact hq23
  have rootNe (rho sigma : D.Root) (a b c d : Nat)
      (hrho : P.root (e rho) =
        (a : R) • P.root (e beta) + (b : R) • P.root (e delta))
      (hsigma : P.root (e sigma) =
        (c : R) • P.root (e beta) + (d : R) • P.root (e delta))
      (hcoord : (a, b) ≠ (c, d)) : rho ≠ sigma :=
    roots_ne_of_distinct_coordinates D P e hLI hrho hsigma hcoord
  have htargetOther : target ≠ other := rootNe target other 1 2 1 3
    (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
    (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using hother) (by decide)
  have htargetTop : target ≠ top := rootNe target top 1 2 2 3
    (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
    (by simpa only [Nat.cast_ofNat] using htop) (by decide)
  have hotherTop : other ≠ top := rootNe other top 1 3 2 3
    (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using hother)
    (by simpa only [Nat.cast_ofNat] using htop) (by decide)
  have hcommTargetOther : ∀ s t : k,
      Commute (C.x target s) (C.x other t) :=
    mixedRoots_commute_of_table_exclusion D C P e hC
      (a := 1) (b := 2) (c := 1) (d := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using hother)
      (positiveRoots_linearlyIndependent D P e base htargetPos hotherPos htargetOther)
      htable (by
        intro m n hm hn hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        omega)
  have hcommTargetTop : ∀ s t : k,
      Commute (C.x target s) (C.x top t) :=
    mixedRoots_commute_of_table_exclusion D C P e hC
      (a := 1) (b := 2) (c := 2) (d := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
      (by simpa only [Nat.cast_ofNat] using htop)
      (positiveRoots_linearlyIndependent D P e base htargetPos htopPos htargetTop)
      htable (by
        intro m n hm hn hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        omega)
  have hcommOtherTop : ∀ s t : k,
      Commute (C.x other s) (C.x top t) :=
    mixedRoots_commute_of_table_exclusion D C P e hC
      (a := 1) (b := 3) (c := 2) (d := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using hother)
      (by simpa only [Nat.cast_ofNat] using htop)
      (positiveRoots_linearlyIndependent D P e base hotherPos htopPos hotherTop)
      htable (by
        intro m n hm hn hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        omega)
  obtain ⟨c, hcoeff, hword⟩ :=
    exact_commutatorProduct_hasChainWord D C P e base hC hbeta hdelta hLI
      [q11, q12, q13, q23] (by simp [q11, q12, q13, q23])
      (by simp [q11, q12, q13, q23]) hterms (by
        intro a ha b hb hab
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl | rfl
        all_goals simp_all [q11, q12, q13, q23])
  refine ⟨c q12, hcoeff q12 (by simp), ?_⟩
  intro hc
  have hword' : HasChainWord D C P e base goal
      (C.x eta (c q11) *
        (C.x target (c q12) * C.x other (c q13) * C.x top (c q23))) := by
    simpa [q11, q12, q13, q23, mul_assoc] using hword
  have htail := HasChainWord.cancel_left D C P e base hC
    (hasChainWord_x D C P e base goal eta (c q11) hetaChain) hword'
  exact isolate_target_of_commuting_triple D C P e base hC hRoot goal
    target other top (c q12) (c q13) (c q23) htail
    hcommTargetOther hcommTargetTop hcommOtherTop
    (positiveRoots_linearlyIndependent D P e base hotherPos htargetPos
      htargetOther.symm)
    (positiveRoots_linearlyIndependent D P e base htopPos htargetPos
      htargetTop.symm) hc

set_option maxHeartbeats 800000 in
private lemma extract_q12_table_mixed
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {beta delta eta target other goal : D.Root}
    (hbeta : beta ∈ chainSupport D P e base goal)
    (hdelta : delta ∈ chainSupport D P e base goal)
    (hetaChain : eta ∈ chainSupport D P e base goal)
    (hetaPos : base.IsPos (e eta))
    (htargetPos : base.IsPos (e target))
    (hotherPos : base.IsPos (e other))
    (hLI : AreLinearlyIndependentRoots D P e beta delta)
    (heta : P.root (e eta) =
      P.root (e beta) + P.root (e delta))
    (htarget : P.root (e target) =
      P.root (e beta) + (2 : R) • P.root (e delta))
    (hother : P.root (e other) =
      (2 : R) • P.root (e beta) + P.root (e delta))
    (htable : mixedCoordinateSet D P e beta delta =
      ({(1, 1), (1, 2), (2, 1)} : Set (Nat × Nat))) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e beta delta
        (⟨1, 2, target⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      (a ≠ 0 → ∃ z : k, z ≠ 0 ∧
        HasChainWord D C P e base goal (C.x target z)) := by
  let q11 : ChevalleyCommutatorTerm D.Root := ⟨1, 1, eta⟩
  let q12 : ChevalleyCommutatorTerm D.Root := ⟨1, 2, target⟩
  let q21 : ChevalleyCommutatorTerm D.Root := ⟨2, 1, other⟩
  have hq11 : IsValidChevalleyCommutatorTerm D P e beta delta q11 :=
    ⟨by norm_num [q11], by norm_num [q11], by simpa [q11] using heta⟩
  have hq12 : IsValidChevalleyCommutatorTerm D P e beta delta q12 :=
    ⟨by norm_num [q12], by norm_num [q12], by simpa [q12] using htarget⟩
  have hq21 : IsValidChevalleyCommutatorTerm D P e beta delta q21 :=
    ⟨by norm_num [q21], by norm_num [q21], by simpa [q21] using hother⟩
  have hterms : ∀ q,
      IsValidChevalleyCommutatorTerm D P e beta delta q ↔
        q ∈ [q11, q12, q21] := by
    intro q
    constructor
    · intro hq
      have hmem : (q.i, q.j) ∈ mixedCoordinateSet D P e beta delta :=
        ⟨hq.1, hq.2.1, q.root, hq.2.2⟩
      rw [htable] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with hij | hij | hij
      · have : q = q11 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q11] using heta)
        simp [this]
      · have : q = q12 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q12] using htarget)
        simp [this]
      · have : q = q21 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
          (by simpa [q21] using hother)
        simp [this]
    · intro hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hq11
      · exact hq12
      · exact hq21
  have hetaTarget : eta ≠ target :=
    roots_ne_of_distinct_coordinates D P e (a := 1) (b := 1)
      (c := 1) (d := 2) hLI
      (by simpa only [Nat.cast_one, one_smul] using heta)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
      (by decide)
  have hetaOther : eta ≠ other :=
    roots_ne_of_distinct_coordinates D P e (a := 1) (b := 1)
      (c := 2) (d := 1) hLI
      (by simpa only [Nat.cast_one, one_smul] using heta)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using hother)
      (by decide)
  have htargetOther : target ≠ other :=
    roots_ne_of_distinct_coordinates D P e (a := 1) (b := 2)
      (c := 2) (d := 1) hLI
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using hother)
      (by decide)
  have commOfCoords (rho sigma : D.Root) (a b c d : Nat)
      (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
      (hrho : P.root (e rho) =
        (a : R) • P.root (e beta) + (b : R) • P.root (e delta))
      (hsigma : P.root (e sigma) =
        (c : R) • P.root (e beta) + (d : R) • P.root (e delta))
      (hlin : AreLinearlyIndependentRoots D P e rho sigma)
      (hNo : ∀ m n : Nat, 0 < m → 0 < n →
        (m * a + n * c, m * b + n * d) ∉
          ({(1, 1), (1, 2), (2, 1)} : Set (Nat × Nat))) :
      ∀ s t : k, Commute (C.x rho s) (C.x sigma t) := by
    exact mixedRoots_commute_of_table_exclusion D C P e hC
      ha hb hc hd hrho hsigma hlin htable hNo
  have hcommEtaTarget : ∀ s t : k,
      Commute (C.x eta s) (C.x target t) :=
    commOfCoords eta target 1 1 1 2 (by omega) (by omega) (by omega) (by omega)
      (by simpa only [Nat.cast_one, one_smul] using heta)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
      (positiveRoots_linearlyIndependent D P e base hetaPos htargetPos hetaTarget)
      (by intro m n hm hn hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          omega)
  have hcommEtaOther : ∀ s t : k,
      Commute (C.x eta s) (C.x other t) :=
    commOfCoords eta other 1 1 2 1 (by omega) (by omega) (by omega) (by omega)
      (by simpa only [Nat.cast_one, one_smul] using heta)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using hother)
      (positiveRoots_linearlyIndependent D P e base hetaPos hotherPos hetaOther)
      (by intro m n hm hn hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          omega)
  have hcommTargetOther : ∀ s t : k,
      Commute (C.x target s) (C.x other t) :=
    commOfCoords target other 1 2 2 1 (by omega) (by omega) (by omega) (by omega)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
      (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using hother)
      (positiveRoots_linearlyIndependent D P e base htargetPos hotherPos htargetOther)
      (by intro m n hm hn hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          omega)
  obtain ⟨c, hcoeff, hword⟩ :=
    exact_commutatorProduct_hasChainWord_of_commuting_terms D C P e base hC
      hbeta hdelta hLI [q11, q12, q21] (by simp [q11, q12, q21]) hterms
      (by
        intro a ha b hb hab s t
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact (hab rfl).elim
        · exact hcommEtaTarget s t
        · exact hcommEtaOther s t
        · exact (hcommEtaTarget t s).symm
        · exact (hab rfl).elim
        · exact hcommTargetOther s t
        · exact (hcommEtaOther t s).symm
        · exact (hcommTargetOther t s).symm
        · exact (hab rfl).elim)
  refine ⟨c q12, hcoeff q12 (by simp), ?_⟩
  intro hc
  have hword' : HasChainWord D C P e base goal
      (C.x eta (c q11) *
        (C.x target (c q12) * C.x other (c q21))) := by
    simpa [q11, q12, q21, mul_assoc] using hword
  have htail := HasChainWord.cancel_left D C P e base hC
    (hasChainWord_x D C P e base goal eta (c q11) hetaChain) hword'
  have hreorder : C.x target (c q12) * C.x other (c q21) =
      C.x other (c q21) * C.x target (c q12) :=
    (hcommTargetOther (c q12) (c q21)).eq
  rw [hreorder] at htail
  exact isolate_moved_of_commuting_pair D C P e base hC hRoot goal
    other target (c q21) (c q12) htail
    (fun s t => (hcommTargetOther t s).symm)
    (positiveRoots_linearlyIndependent D P e base hotherPos htargetPos
      htargetOther.symm) hc

private lemma extract_q12_from_rankTwoTable
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {beta delta eta target goal : D.Root}
    (hdeltaBase : e delta ∈ base.support)
    (hbetaPos : base.IsPos (e beta))
    (hetaPos : base.IsPos (e eta))
    (htargetPos : base.IsPos (e target))
    (hbeta : beta ∈ chainSupport D P e base goal)
    (hdelta : delta ∈ chainSupport D P e base goal)
    (hetaChain : eta ∈ chainSupport D P e base goal)
    (hLI : AreLinearlyIndependentRoots D P e beta delta)
    (heta : P.root (e eta) =
      P.root (e beta) + P.root (e delta))
    (htarget : P.root (e target) =
      P.root (e beta) + (2 : R) • P.root (e delta)) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e beta delta
        (⟨1, 2, target⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      (a ≠ 0 → ∃ z : k, z ≠ 0 ∧
        HasChainWord D C P e base goal (C.x target z)) := by
  have htables := rankTwoPositiveMixedRootCoordinates_cases P base hdeltaBase
    hbetaPos hetaPos heta
  have hmixed :
      {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root (e beta) +
            (ij.2 : R) • P.root (e delta)} =
        mixedCoordinateSet D P e beta delta := by
    ext ij
    simp only [mixedCoordinateSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hi, hj, rho, hrho⟩
      exact ⟨hi, hj, e.symm rho, by simpa using hrho⟩
    · rintro ⟨hi, hj, rho, hrho⟩
      exact ⟨hi, hj, e rho, hrho⟩
  rw [hmixed] at htables
  have hmem12 : (1, 2) ∈ mixedCoordinateSet D P e beta delta :=
    ⟨by norm_num, by norm_num, target,
      by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget⟩
  rcases htables with htable | htable | htable | htable | htable | htable
  · rw [htable] at hmem12
    simp at hmem12
  · obtain ⟨a, ha, hword⟩ := extract_q12_table_two D C P e base hC
      hbeta hdelta hetaChain hLI heta htarget htable
    exact ⟨a, ha, fun ha0 => ⟨a, ha0, hword⟩⟩
  · rw [htable] at hmem12
    simp at hmem12
  · have hmem13 : (1, 3) ∈ mixedCoordinateSet D P e beta delta := by
      rw [htable]
      simp
    have hmem23 : (2, 3) ∈ mixedCoordinateSet D P e beta delta := by
      rw [htable]
      simp
    obtain ⟨_, _, other, hother⟩ := hmem13
    obtain ⟨_, _, top, htop⟩ := hmem23
    have hdeltaPos := base.isPos_of_mem_support hdeltaBase
    have hotherPos : base.IsPos (e other) :=
      htargetPos.add hdeltaPos (by rw [hother, htarget]; module)
    have htopPos : base.IsPos (e top) :=
      hotherPos.add hbetaPos (by rw [htop, hother]; module)
    exact extract_q12_table_four D C P e base hC hRoot
      hbeta hdelta hetaChain htargetPos hotherPos htopPos hLI heta htarget
      (by norm_num at hother ⊢; exact hother)
      (by norm_num at htop ⊢; exact htop) htable
  · rw [htable] at hmem12
    simp at hmem12
  · have hmem21 : (2, 1) ∈ mixedCoordinateSet D P e beta delta := by
      rw [htable]
      simp
    obtain ⟨_, _, other, hother⟩ := hmem21
    have hotherPos : base.IsPos (e other) :=
      hetaPos.add hbetaPos (by rw [hother, heta]; module)
    exact extract_q12_table_mixed D C P e base hC hRoot
      hbeta hdelta hetaChain hetaPos htargetPos hotherPos hLI heta htarget
      (by norm_num at hother ⊢; exact hother) htable

set_option maxHeartbeats 800000 in
private lemma extract_q13_from_rankTwoTable
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {beta delta eta alpha target goal : D.Root}
    (hdeltaBase : e delta ∈ base.support)
    (hbetaPos : base.IsPos (e beta))
    (hetaPos : base.IsPos (e eta))
    (htargetPos : base.IsPos (e target))
    (hbeta : beta ∈ chainSupport D P e base goal)
    (hdelta : delta ∈ chainSupport D P e base goal)
    (hetaChain : eta ∈ chainSupport D P e base goal)
    (halphaChain : alpha ∈ chainSupport D P e base goal)
    (hLI : AreLinearlyIndependentRoots D P e beta delta)
    (heta : P.root (e eta) =
      P.root (e beta) + P.root (e delta))
    (halpha : P.root (e alpha) =
      P.root (e beta) + (2 : R) • P.root (e delta))
    (htarget : P.root (e target) =
      P.root (e beta) + (3 : R) • P.root (e delta)) :
    ∃ a : k,
      HasExpectedChevalleyCoefficient D P e beta delta
        (⟨1, 3, target⟩ : ChevalleyCommutatorTerm D.Root) a ∧
      (a ≠ 0 → ∃ z : k, z ≠ 0 ∧
        HasChainWord D C P e base goal (C.x target z)) := by
  have htables := rankTwoPositiveMixedRootCoordinates_cases P base hdeltaBase
    hbetaPos hetaPos heta
  have hmixed :
      {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root (e beta) +
            (ij.2 : R) • P.root (e delta)} =
        mixedCoordinateSet D P e beta delta := by
    ext ij
    simp only [mixedCoordinateSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hi, hj, rho, hrho⟩
      exact ⟨hi, hj, e.symm rho, by simpa using hrho⟩
    · rintro ⟨hi, hj, rho, hrho⟩
      exact ⟨hi, hj, e rho, hrho⟩
  rw [hmixed] at htables
  have hmem13 : (1, 3) ∈ mixedCoordinateSet D P e beta delta :=
    ⟨by norm_num, by norm_num, target,
      by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget⟩
  rcases htables with htable | htable | htable | htable | htable | htable
  · rw [htable] at hmem13
    simp at hmem13
  · rw [htable] at hmem13
    simp at hmem13
  · rw [htable] at hmem13
    simp at hmem13
  · have hmem23 : (2, 3) ∈ mixedCoordinateSet D P e beta delta := by
      rw [htable]
      simp
    obtain ⟨_, _, top, htop⟩ := hmem23
    have htopPos : base.IsPos (e top) :=
      htargetPos.add hbetaPos (by rw [htop, htarget]; module)
    let q11 : ChevalleyCommutatorTerm D.Root := ⟨1, 1, eta⟩
    let q12 : ChevalleyCommutatorTerm D.Root := ⟨1, 2, alpha⟩
    let q13 : ChevalleyCommutatorTerm D.Root := ⟨1, 3, target⟩
    let q23 : ChevalleyCommutatorTerm D.Root := ⟨2, 3, top⟩
    have hq11 : IsValidChevalleyCommutatorTerm D P e beta delta q11 :=
      ⟨by norm_num [q11], by norm_num [q11], by simpa [q11] using heta⟩
    have hq12 : IsValidChevalleyCommutatorTerm D P e beta delta q12 :=
      ⟨by norm_num [q12], by norm_num [q12], by simpa [q12] using halpha⟩
    have hq13 : IsValidChevalleyCommutatorTerm D P e beta delta q13 :=
      ⟨by norm_num [q13], by norm_num [q13], by simpa [q13] using htarget⟩
    have hq23 : IsValidChevalleyCommutatorTerm D P e beta delta q23 :=
      ⟨by norm_num [q23], by norm_num [q23], by simpa [q23] using htop⟩
    have hterms : ∀ q,
        IsValidChevalleyCommutatorTerm D P e beta delta q ↔
          q ∈ [q11, q12, q13, q23] := by
      intro q
      constructor
      · intro hq
        have hmem : (q.i, q.j) ∈ mixedCoordinateSet D P e beta delta :=
          ⟨hq.1, hq.2.1, q.root, hq.2.2⟩
        rw [htable] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with hij | hij | hij | hij
        · have : q = q11 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
            (by simpa [q11] using heta)
          simp [this]
        · have : q = q12 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
            (by simpa [q12] using halpha)
          simp [this]
        · have : q = q13 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
            (by simpa [q13] using htarget)
          simp [this]
        · have : q = q23 := validTerm_eq_of_coordinates D P e hq hij.1 hij.2
            (by simpa [q23] using htop)
          simp [this]
      · intro hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hq11
        · exact hq12
        · exact hq13
        · exact hq23
    have htargetTop : target ≠ top :=
      roots_ne_of_distinct_coordinates D P e (a := 1) (b := 3)
        (c := 2) (d := 3) hLI
        (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
        (by norm_num at htop ⊢; exact htop) (by decide)
    have hcomm : ∀ s t : k, Commute (C.x target s) (C.x top t) :=
      mixedRoots_commute_of_table_exclusion D C P e hC
        (a := 1) (b := 3) (c := 2) (d := 3)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa only [Nat.cast_one, one_smul, Nat.cast_ofNat] using htarget)
        (by norm_num at htop ⊢; exact htop)
        (positiveRoots_linearlyIndependent D P e base htargetPos htopPos htargetTop)
        htable (by
          intro m n hm hn hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          omega)
    obtain ⟨c, hcoeff, hword⟩ :=
      exact_commutatorProduct_hasChainWord D C P e base hC hbeta hdelta hLI
        [q11, q12, q13, q23] (by simp [q11, q12, q13, q23])
        (by simp [q11, q12, q13, q23]) hterms (by
          intro a ha b hb hab
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
          rcases ha with rfl | rfl | rfl | rfl <;>
            rcases hb with rfl | rfl | rfl | rfl
          all_goals simp_all [q11, q12, q13, q23])
    refine ⟨c q13, hcoeff q13 (by simp), ?_⟩
    intro hc
    have hword' : HasChainWord D C P e base goal
        ((C.x eta (c q11) * C.x alpha (c q12)) *
          (C.x target (c q13) * C.x top (c q23))) := by
      simpa [q11, q12, q13, q23, mul_assoc] using hword
    have hlower : HasChainWord D C P e base goal
        (C.x eta (c q11) * C.x alpha (c q12)) :=
      (hasChainWord_x D C P e base goal eta (c q11) hetaChain).mul
        D C P e base
        (hasChainWord_x D C P e base goal alpha (c q12) halphaChain)
    have htail := HasChainWord.cancel_left D C P e base hC hlower hword'
    have hreorder : C.x target (c q13) * C.x top (c q23) =
        C.x top (c q23) * C.x target (c q13) :=
      (hcomm (c q13) (c q23)).eq
    rw [hreorder] at htail
    exact isolate_moved_of_commuting_pair D C P e base hC hRoot goal
      top target (c q23) (c q13) htail
      (fun s t => (hcomm t s).symm)
      (positiveRoots_linearlyIndependent D P e base htopPos htargetPos
        htargetTop.symm) hc
  · rw [htable] at hmem13
    simp at hmem13
  · rw [htable] at hmem13
    simp at hmem13

omit [IsAlgClosed k] in
private lemma previous_root_of_q11_exceptionalTwo
    {alpha delta gamma : D.Root}
    (halphaPos : base.IsPos (e alpha))
    (hdeltaBase : e delta ∈ base.support)
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (hex : IsChevalleyCoefficientExceptionalTwo D P e alpha delta
      (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root)) :
    ∃ beta : D.Root,
      P.root (e beta) = P.root (e alpha) - P.root (e delta) := by
  have hdeltaPos := base.isPos_of_mem_support hdeltaBase
  have hadNe : alpha ≠ delta := by
    intro had
    subst delta
    obtain ⟨hone, _⟩ := hLI 1 (-1) (by module)
    norm_num at hone
  have hLIDA := positiveRoots_linearlyIndependent D P e base
    hdeltaPos halphaPos hadNe.symm
  have hlinDA : LinearIndependent R
      ![P.root (e delta), P.root (e alpha)] := by
    rw [LinearIndependent.pair_iff]
    simpa [AreLinearlyIndependentRoots] using hLIDA
  have htopOne : 1 ≤ P.chainTopCoeff (e delta) (e alpha) := by
    rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlinDA]
    exact ⟨e gamma, by simpa only [one_smul] using hadd⟩
  rcases hex with ⟨_, hcase | hcase | hcase⟩
  · rcases hcase with ⟨_, _, hlen, hgammaLen⟩
    have hpair : P.pairingIn ℤ (e alpha) (e delta) = 0 := by
      apply pairingIn_eq_of_equal_lengths_root_sum D P e (z := 2)
        hadd hlen
      simpa using hgammaLen
    have hdiff := P.chainBotCoeff_sub_chainTopCoeff hlinDA
    rw [hpair] at hdiff
    have hbot : 1 ≤ P.chainBotCoeff (e delta) (e alpha) := by omega
    have hmem :=
      (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlinDA).2 hbot
    obtain ⟨rho, hrho⟩ := hmem
    exact ⟨e.symm rho, by
      simpa only [Equiv.apply_symm_apply, one_smul] using hrho⟩
  · rcases hcase with ⟨_, _, hlen, hgammaLen, r, hr, hrshape⟩
    have hpairAD : P.pairingIn ℤ (e alpha) (e delta) = -1 := by
      apply pairingIn_eq_of_equal_lengths_root_sum D P e (z := 1)
        hadd hlen
      simpa using hgammaLen
    rcases hrshape with hrshape | hrshape
    · have hpairDA : P.pairingIn ℤ (e delta) (e alpha) = -1 := by
        rw [← pairingIn_eq_of_equal_lengths D P e hlen]
        exact hpairAD
      have hlinAD : LinearIndependent R
          ![P.root (e alpha), P.root (e delta)] := by
        rw [LinearIndependent.pair_iff]
        simpa [AreLinearlyIndependentRoots] using hLI
      have htopTwo : 2 ≤ P.chainTopCoeff (e alpha) (e delta) := by
        rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlinAD]
        exact ⟨e r.root, by
          rw [hr.2.2]
          rcases hrshape with ⟨hi, hj⟩
          rw [hi, hj]
          simp only [Nat.cast_one, Nat.cast_ofNat, one_smul]
          module⟩
      have hdiff := P.chainBotCoeff_sub_chainTopCoeff hlinAD
      rw [hpairDA] at hdiff
      have hbot : 1 ≤ P.chainBotCoeff (e alpha) (e delta) := by omega
      have hmemDA :=
        (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlinAD).2 hbot
      have hmem : P.root (e alpha) - P.root (e delta) ∈ Set.range P.root := by
        rw [← P.neg_mem_range_root_iff]
        simpa only [one_smul, neg_sub] using hmemDA
      obtain ⟨rho, hrho⟩ := hmem
      exact ⟨e.symm rho, by
        simpa only [Equiv.apply_symm_apply] using hrho⟩
    · have htopTwo : 2 ≤ P.chainTopCoeff (e delta) (e alpha) := by
        rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlinDA]
        exact ⟨e r.root, by
          rw [hr.2.2]
          rcases hrshape with ⟨hi, hj⟩
          rw [hi, hj]
          simp only [Nat.cast_one, Nat.cast_ofNat, one_smul]
          module⟩
      have hdiff := P.chainBotCoeff_sub_chainTopCoeff hlinDA
      rw [hpairAD] at hdiff
      have hbot : 1 ≤ P.chainBotCoeff (e delta) (e alpha) := by omega
      have hmem :=
        (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlinDA).2 hbot
      obtain ⟨rho, hrho⟩ := hmem
      exact ⟨e.symm rho, by
        simpa only [Equiv.apply_symm_apply, one_smul] using hrho⟩
  · rcases hcase with ⟨hbad, _⟩
    norm_num at hbad

omit [IsAlgClosed k] in
private lemma two_previous_roots_of_q11_exceptionalThree
    {alpha delta gamma : D.Root}
    (halphaPos : base.IsPos (e alpha))
    (hdeltaBase : e delta ∈ base.support)
    (hLI : AreLinearlyIndependentRoots D P e alpha delta)
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (hex : IsChevalleyCoefficientExceptionalThree D P e alpha delta
      (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root)) :
    ∃ beta eta : D.Root,
      P.root (e beta) = P.root (e alpha) - (2 : R) • P.root (e delta) ∧
      P.root (e eta) = P.root (e alpha) - P.root (e delta) := by
  have hdeltaPos := base.isPos_of_mem_support hdeltaBase
  have hadNe : alpha ≠ delta := by
    intro had
    subst delta
    obtain ⟨hone, _⟩ := hLI 1 (-1) (by module)
    norm_num at hone
  have hLIDA := positiveRoots_linearlyIndependent D P e base
    hdeltaPos halphaPos hadNe.symm
  have hlinDA : LinearIndependent R
      ![P.root (e delta), P.root (e alpha)] := by
    rw [LinearIndependent.pair_iff]
    simpa [AreLinearlyIndependentRoots] using hLIDA
  have htopOne : 1 ≤ P.chainTopCoeff (e delta) (e alpha) := by
    rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlinDA]
    exact ⟨e gamma, by simpa only [one_smul] using hadd⟩
  rcases hex with ⟨_, hcase | hcase⟩
  · rcases hcase with ⟨_, _, hlen, hgammaLen⟩
    have hpair : P.pairingIn ℤ (e alpha) (e delta) = 1 := by
      apply pairingIn_eq_of_equal_lengths_root_sum D P e (z := 3)
        hadd hlen
      simpa using hgammaLen
    have hdiff := P.chainBotCoeff_sub_chainTopCoeff hlinDA
    rw [hpair] at hdiff
    have hbot : 2 ≤ P.chainBotCoeff (e delta) (e alpha) := by omega
    have hmemTwo :=
      (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlinDA).2 hbot
    have hmemOne :=
      (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlinDA).2
        (by omega : 1 ≤ P.chainBotCoeff (e delta) (e alpha))
    obtain ⟨rho, hrho⟩ := hmemTwo
    obtain ⟨sigma, hsigma⟩ := hmemOne
    exact ⟨e.symm rho, e.symm sigma, by
      rw [Equiv.apply_symm_apply]
      calc
        P.root rho = P.root (e alpha) - (2 : Nat) • P.root (e delta) := hrho
        _ = P.root (e alpha) - (2 : R) • P.root (e delta) := by
          exact congrArg (fun z : M => P.root (e alpha) - z)
            (Nat.cast_smul_eq_nsmul R 2 (P.root (e delta))).symm, by
      simpa only [Equiv.apply_symm_apply, one_smul] using hsigma⟩
  · rcases hcase with ⟨hbad, _⟩
    norm_num at hbad

omit [IsAlgClosed k] in
private lemma expected_q12_ne_zero_of_two_eq_zero
    {beta delta target : D.Root} {a : k}
    (htwo : (2 : k) = 0)
    (ha : HasExpectedChevalleyCoefficient D P e beta delta
      (⟨1, 2, target⟩ : ChevalleyCommutatorTerm D.Root) a) :
    a ≠ 0 := by
  have hnotTwo : ¬ IsChevalleyCoefficientExceptionalTwo D P e beta delta
      (⟨1, 2, target⟩ : ChevalleyCommutatorTerm D.Root) := by
    intro h
    rcases h with ⟨_, h | h | h⟩
    · rcases h with ⟨_, hj, _⟩
      norm_num at hj
    · rcases h with ⟨_, hj, _⟩
      norm_num at hj
    · rcases h with ⟨hi, _⟩
      norm_num at hi
  have hthreeNe : (3 : k) ≠ 0 := by
    have hthree : (3 : k) = 1 := by
      calc
        (3 : k) = 2 + 1 := by norm_num
        _ = 0 + 1 := by rw [htwo]
        _ = 1 := by ring
    rw [hthree]
    exact one_ne_zero
  by_cases hthree : IsChevalleyCoefficientExceptionalThree D P e beta delta
      (⟨1, 2, target⟩ : ChevalleyCommutatorTerm D.Root)
  · rcases ha.2.1 hthree with ha | ha
    · rw [ha]
      exact hthreeNe
    · rw [ha]
      exact neg_ne_zero.mpr hthreeNe
  · rcases ha.2.2 hnotTwo hthree with ha | ha
    · rw [ha]
      exact one_ne_zero
    · rw [ha]
      exact neg_ne_zero.mpr one_ne_zero

omit [IsAlgClosed k] in
private lemma expected_q13_ne_zero
    {beta delta target : D.Root} {a : k}
    (ha : HasExpectedChevalleyCoefficient D P e beta delta
      (⟨1, 3, target⟩ : ChevalleyCommutatorTerm D.Root) a) :
    a ≠ 0 := by
  have hnotTwo : ¬ IsChevalleyCoefficientExceptionalTwo D P e beta delta
      (⟨1, 3, target⟩ : ChevalleyCommutatorTerm D.Root) := by
    intro h
    rcases h with ⟨_, h | h | h⟩
    · rcases h with ⟨_, hj, _⟩
      norm_num at hj
    · rcases h with ⟨_, hj, _⟩
      norm_num at hj
    · rcases h with ⟨hi, _⟩
      norm_num at hi
  have hnotThree : ¬ IsChevalleyCoefficientExceptionalThree D P e beta delta
      (⟨1, 3, target⟩ : ChevalleyCommutatorTerm D.Root) := by
    intro h
    rcases h with ⟨_, h | h⟩
    · rcases h with ⟨_, hj, _⟩
      norm_num at hj
    · rcases h with ⟨hij, _⟩
      rcases hij with hij | hij
      · norm_num at hij
      · norm_num at hij
  rcases ha.2.2 hnotTwo hnotThree with ha | ha
  · rw [ha]
    exact one_ne_zero
  · rw [ha]
    exact neg_ne_zero.mpr one_ne_zero

public theorem rankTwoPositiveChain_parameter_word_of_certificate
    (hC : RankTwoChevalleyParameterCertificate D C P e)
    (hRoot : RankTwoRootPairingCertificate D P e)
    {alpha delta gamma : D.Root}
    (hdelta : e delta ∈ base.support)
    (halphaPos : base.IsPos (e alpha))
    (hgammaPos : base.IsPos (e gamma))
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (t : k) :
    ∃ word : List (D.Root × k),
      (∀ q ∈ word, e q.1 ∈ base.support ∨
        (base.IsPos (e q.1) ∧
          base.height (e q.1) < base.height (e gamma))) ∧
      C.x gamma t = FilteredCollection.wordProduct C.x word := by
  have hdeltaPos := base.isPos_of_mem_support hdelta
  let _ : IsAddTorsionFree M := .of_isTorsionFree R M
  have hadNe : alpha ≠ delta := by
    intro had
    apply P.nsmul_notMem_range_root (n := 2) (i := e alpha)
    refine ⟨e gamma, ?_⟩
    rw [hadd, had]
    simp only [two_smul]
  have hLI := positiveRoots_linearlyIndependent D P e base
    halphaPos hdeltaPos hadNe
  obtain ⟨a, haExpected, haWord⟩ :=
    extract_q11_from_rankTwoTable D C P e base hC hRoot hdelta
      halphaPos hgammaPos hLI hadd
  by_cases ha : a ≠ 0
  · obtain ⟨z, hz, hword⟩ := haWord ha
    exact hasChainWord_all_parameters_of_nonzero D C P e base hC hRoot
      gamma hz hword t
  · have haZero : a = 0 := not_ne_iff.mp ha
    by_cases htwo : IsChevalleyCoefficientExceptionalTwo D P e alpha delta
        (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root)
    · have htwoZero : (2 : k) = 0 := by
        rcases haExpected.1 htwo with h | h
        · calc
            (2 : k) = a := h.symm
            _ = 0 := haZero
        · have hneg : (-2 : k) = 0 := h.symm.trans haZero
          exact neg_eq_zero.mp hneg
      obtain ⟨beta, hbeta⟩ := previous_root_of_q11_exceptionalTwo
        D P e base halphaPos hdelta hLI hadd htwo
      have hbetaPos : base.IsPos (e beta) :=
        halphaPos.sub hdelta hbeta
      have hbetaNeDelta : beta ≠ delta := by
        intro hbd
        rw [hbd] at hbeta
        have hzero : (1 : R) • P.root (e alpha) +
            (-2 : R) • P.root (e delta) = 0 := by
          calc
            _ = -(P.root (e delta) -
                (P.root (e alpha) - P.root (e delta))) := by module
            _ = 0 := by rw [← hbeta]; simp
        obtain ⟨hone, _⟩ := hLI 1 (-2) hzero
        norm_num at hone
      have hLIbeta := positiveRoots_linearlyIndependent D P e base
        hbetaPos hdeltaPos hbetaNeDelta
      obtain ⟨halphaChain, hdeltaChain⟩ :=
        chainSupport_alpha_delta D P e base hdelta halphaPos hadd
      have hbetaChain : beta ∈ chainSupport D P e base gamma := by
        right
        refine ⟨hbetaPos, ?_⟩
        rw [base.height_sub hbeta, base.height_add hadd,
          base.height_one_of_mem_support hdelta]
        omega
      have hbetaDelta : P.root (e alpha) =
          P.root (e beta) + P.root (e delta) := by
        rw [hbeta]
        module
      have hbetaTwoDelta : P.root (e gamma) =
          P.root (e beta) + (2 : R) • P.root (e delta) := by
        rw [hadd, hbeta]
        module
      obtain ⟨b, hbExpected, hbWord⟩ :=
        extract_q12_from_rankTwoTable D C P e base hC hRoot hdelta
          hbetaPos halphaPos hgammaPos hbetaChain hdeltaChain halphaChain
          hLIbeta hbetaDelta hbetaTwoDelta
      have hb : b ≠ 0 :=
        expected_q12_ne_zero_of_two_eq_zero D P e htwoZero hbExpected
      obtain ⟨z, hz, hword⟩ := hbWord hb
      exact hasChainWord_all_parameters_of_nonzero D C P e base hC hRoot
        gamma hz hword t
    · have hthree : IsChevalleyCoefficientExceptionalThree D P e alpha delta
          (⟨1, 1, gamma⟩ : ChevalleyCommutatorTerm D.Root) := by
        by_contra hthree
        rcases haExpected.2.2 htwo hthree with h | h
        · have : (1 : k) = 0 := h.symm.trans haZero
          exact one_ne_zero this
        · have hneg : (-1 : k) = 0 := h.symm.trans haZero
          exact one_ne_zero (neg_eq_zero.mp hneg)
      obtain ⟨beta, eta, hbeta, heta⟩ :=
        two_previous_roots_of_q11_exceptionalThree D P e base
          halphaPos hdelta hLI hadd hthree
      have hetaPos : base.IsPos (e eta) :=
        halphaPos.sub hdelta heta
      have hbetaEta : P.root (e beta) =
          P.root (e eta) - P.root (e delta) := by
        rw [hbeta, heta]
        module
      have hbetaPos : base.IsPos (e beta) :=
        hetaPos.sub hdelta hbetaEta
      have hbetaNeDelta : beta ≠ delta := by
        intro hbd
        rw [hbd] at hbeta
        have hzero : (1 : R) • P.root (e alpha) +
            (-3 : R) • P.root (e delta) = 0 := by
          calc
            _ = -(P.root (e delta) -
                (P.root (e alpha) - (2 : R) • P.root (e delta))) := by module
            _ = 0 := by rw [← hbeta]; simp
        obtain ⟨hone, _⟩ := hLI 1 (-3) hzero
        norm_num at hone
      have hLIbeta := positiveRoots_linearlyIndependent D P e base
        hbetaPos hdeltaPos hbetaNeDelta
      obtain ⟨halphaChain, hdeltaChain⟩ :=
        chainSupport_alpha_delta D P e base hdelta halphaPos hadd
      have hetaChain : eta ∈ chainSupport D P e base gamma := by
        right
        refine ⟨hetaPos, ?_⟩
        rw [base.height_sub heta, base.height_add hadd,
          base.height_one_of_mem_support hdelta]
        omega
      have hbetaChain : beta ∈ chainSupport D P e base gamma := by
        right
        refine ⟨hbetaPos, ?_⟩
        rw [base.height_sub hbetaEta, base.height_sub heta,
          base.height_add hadd, base.height_one_of_mem_support hdelta]
        omega
      have hbetaDelta : P.root (e eta) =
          P.root (e beta) + P.root (e delta) := by
        rw [hbeta, heta]
        module
      have hbetaTwoDelta : P.root (e alpha) =
          P.root (e beta) + (2 : R) • P.root (e delta) := by
        rw [hbeta]
        module
      have hbetaThreeDelta : P.root (e gamma) =
          P.root (e beta) + (3 : R) • P.root (e delta) := by
        rw [hadd, hbeta]
        module
      obtain ⟨b, hbExpected, hbWord⟩ :=
        extract_q13_from_rankTwoTable D C P e base hC hRoot hdelta
          hbetaPos hetaPos hgammaPos hbetaChain hdeltaChain hetaChain
          halphaChain hLIbeta hbetaDelta hbetaTwoDelta hbetaThreeDelta
      have hb : b ≠ 0 := expected_q13_ne_zero D P e hbExpected
      obtain ⟨z, hz, hword⟩ := hbWord hb
      exact hasChainWord_all_parameters_of_nonzero D C P e base hC hRoot
        gamma hz hword t

/-! Compatibility wrapper for callers whose Chevalley and realization bases are
already the same as the positive-chain base. -/
public theorem rankTwoPositiveChain_parameter_word
    (hC : IsChevalleySystem D C P e base)
    (hRoot : IsRootSystemRealization D P e base)
    (_hAdd : IsRootAdditionRealization D P e)
    {alpha delta gamma : D.Root}
    (hdelta : e delta ∈ base.support)
    (halphaPos : base.IsPos (e alpha))
    (hgammaPos : base.IsPos (e gamma))
    (hadd : P.root (e gamma) =
      P.root (e alpha) + P.root (e delta))
    (t : k) :
    ∃ word : List (D.Root × k),
      (∀ q ∈ word, e q.1 ∈ base.support ∨
        (base.IsPos (e q.1) ∧
          base.height (e q.1) < base.height (e gamma))) ∧
      C.x gamma t = FilteredCollection.wordProduct C.x word := by
  exact rankTwoPositiveChain_parameter_word_of_certificate D C P e base
    (RankTwoChevalleyParameterCertificate.of_system D C P e base hC)
    (RankTwoRootPairingCertificate.of_realization D P e base hRoot)
    hdelta halphaPos hgammaPos hadd t

end Theory.AlgebraicGroup
