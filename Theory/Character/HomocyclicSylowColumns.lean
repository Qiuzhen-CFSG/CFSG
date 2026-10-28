module

public import Theory.Character.HomocyclicSylowLinearCharacters
public import Theory.Character.ModularBlock.NormalComplementDegree
public import Theory.Character.ModularBlock.RestrictionColumn
public import Theory.Character.ModularBlock.LocalColumnNorm
public import Theory.GroupTheory.HomocyclicSylowCentralizers

/-!
# Principal-block columns on a homocyclic Sylow subgroup

Each nonidentity element of a rank-two homocyclic Sylow two-subgroup has a
centralizer with a normal two-complement. The quotient has the order of the
original Sylow subgroup. Inflation identifies the local principal-block degree
sum with that order; the local column-norm theorem then computes the ambient
principal-block norm. The coefficient place and ordinary characters remain
those of the prescribed principal congruence datum throughout. Off-diagonal
orthogonality then identifies the pairing of integer restriction columns with
an ordinary scalar product against the ambient conjugacy-orbit sum on the
Sylow subgroup. The ordinary orbit system then constructs the genuine integer
columns, their Gram matrix, and the reconstruction of constant character
restrictions. Its distinguished order-two character gives the weighted zero
sums at the identity and all involutions. `ColumnSystem` retains the actual
orbit representatives and restriction coefficients for subsequent applications.

Source: Brauer, *Some applications of the theory of blocks of characters of
finite groups. II* (1964), §V Lemma 3 and §VI (6.1)–(6.6). See
`refs/original/brauer-homocyclic-sylow/README.md`.
-/

public section
noncomputable section
open scoped BigOperators
namespace HomocyclicSylowColumns
open ModularBlock PrincipalBlockConstruction CompatibleBrauerBlock RestrictionColumn
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- The normal two-complement in a nonidentity Sylow-element centralizer has
quotient order equal to the order of the original Sylow subgroup. -/
theorem exists_local_odd_quotient_card (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (s : S) (hs : s ≠ 1) :
    let C := Subgroup.centralizer ({(s : G)} : Set G)
    ∃ (N : Subgroup C) (_ : N.Normal), Odd (Nat.card N) ∧ IsPGroup 2 (C ⧸ N) ∧
      Nat.card (C ⧸ N) = Nat.card S := by
  obtain ⟨hSC, N, hN, hodd, hquot, hcomp⟩ :=
    S.exists_normal_two_complement_centralizer_of_equiv_prod_zmod hn e s hs
  refine ⟨N, hN, hodd, hquot, ?_⟩
  rw [← Subgroup.index_eq_card, hcomp.symm.index_eq_card]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv

/-- The local principal-block sum of squared degrees is the Sylow order. -/
theorem local_sum_degree_sq (d : PrincipalCongruenceBlockData G)
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (s : S) (hs : s ≠ 1) :
    let l := localData d (Subgroup.centralizer ({(s : G)} : Set G))
    ∑ i ∈ l.block, l.chi i (ConjClasses.mk 1) ^ 2 = (Nat.card S : ℂ) := by
  obtain ⟨N, hN, hodd, hquot, hcard⟩ := exists_local_odd_quotient_card S hn e s hs
  have := NormalComplementDegree.sum_degree_sq
    (localData d (Subgroup.centralizer ({(s : G)} : Set G))) N hodd hquot
  simpa only [hcard] using this

/-- Every nonidentity Sylow column has squared norm equal to the Sylow order.
The noncentralizing-normalizer hypothesis is unnecessary for this identity. -/
theorem principalBlock_column_norm (d : PrincipalCongruenceBlockData G)
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (s : S) (hs : s ≠ 1) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk (s : G)) *
      star (d.chi i (ConjClasses.mk (s : G))) = (Nat.card S : ℂ) := by
  have hp : ∃ m : ℕ, (s : G) ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := S.isPGroup'.exists_pow_pow_eq_one s
    exact ⟨m, by exact_mod_cast hm⟩
  exact (LocalColumnNorm.principalBlock_local_column_norm d s hp).trans
    (local_sum_degree_sq d S hn e s hs)


section ColumnKernel
attribute [local instance] Classical.propDecidable
/-- The actual principal-block kernel on Sylow elements, away from the identity
in its first argument. Fusion is ambient conjugacy. -/
theorem principalBlock_column_inner (d : PrincipalCongruenceBlockData G) (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (s t : S) (hs : s ≠ 1) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk (s:G)) * star (d.chi i (ConjClasses.mk (t:G))) =
      if IsConj (s:G) (t:G) then (Nat.card S : ℂ) else 0 := by
  classical
  by_cases hst : IsConj (s:G) (t:G)
  · rw [if_pos hst, ← ConjClasses.mk_eq_mk_iff_isConj.mpr hst]
    exact principalBlock_column_norm d S hn e s hs
  · rw [if_neg hst]
    have hp (u : S) : ∃ m : ℕ, (u:G) ^ (2^m) = 1 := by
      obtain ⟨m, hm⟩ := S.isPGroup'.exists_pow_pow_eq_one u
      exact ⟨m, by exact_mod_cast hm⟩
    exact ModularBlock.TwoElementColumnOrthogonality.principalBlock_column_orthogonal
      d s t (hp s) (hp t) hst

end ColumnKernel

/-- Sum a subgroup function over the elements ambient-conjugate to its argument.
Each element is counted once, rather than once per normalizer element. -/
@[expose] def conjugacySum (H : Subgroup G) (η : ClassFunction H) : ClassFunction H := by
  classical
  let : Fintype H := Fintype.ofFinite H
  exact fun s => ∑ t : H, if IsConj (s:G) (t:G) then η t else 0

/-- Brauer's restriction-column pairing, reduced to the ordinary conjugacy
orbit sum on the Sylow subgroup. Only the first function must vanish at one. -/
theorem restrictionColumn_pairing (d : PrincipalCongruenceBlockData G) (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (θ η : ClassFunction S) (hθ : IsGeneralizedCharacter θ) (hη : IsGeneralizedCharacter η)
    (hzero : θ 1 = 0) :
    ∑ i ∈ d.block, (coefficient d S θ hθ i : ℂ) * (coefficient d S η hη i : ℂ) =
      scalarProduct S (conjugacySum (S : Subgroup G) η) θ := by
  classical
  let : Fintype S := Fintype.ofFinite S
  rw [coefficient_pairing_eq_sum, scalarProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s = 1
  · simp [hs, hzero]
  rw [coefficient_sum_eq]
  have hsum : (∑ t : S, η t * (∑ i ∈ d.block,
      d.chi i (ConjClasses.mk (s:G)) * star (d.chi i (ConjClasses.mk (t:G))))) =
      (Nat.card S : ℂ) * conjugacySum (S : Subgroup G) η s := by
    simp_rw [principalBlock_column_inner d S hn e s _ hs]
    dsimp [conjugacySum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [mul_ite, mul_zero, mul_comm]
  rw [hsum, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.card_pos (α := S)).ne')]
  ring

open HomocyclicSylowLinearCharacters (OrbitSystem)

/-- Brauer's actual integer restriction columns, retaining the ordinary orbit
representatives and their coefficient identities for weighted applications. -/
structure ColumnSystem (d : PrincipalCongruenceBlockData G) (S : Sylow 2 G)
    (n : ℕ) extends OrbitSystem S n where
  b : Fin r → d.I → ℤ
  support : ∀ j k, k ∉ d.block → b j k = 0
  coefficient_eq : ∀ j k, k ∈ d.block →
    (b j k : ℂ) = scalarProduct S
      (fun s => d.chi k (ConjClasses.mk (s : G))) (ψ j - 1)
  principal : ∀ j, b j d.principal = -1
  gram : ∀ i j, ∑ k, b i k * b j k = 3 + if i = j then 1 else 0
  reconstruction : ∀ k, k ∈ d.block → ∀ δ : ℤ, (∀ j, b j k = δ) →
    ∀ s : S, s ≠ 1 → d.chi k (ConjClasses.mk (s : G)) = -(δ : ℂ)
  sum_degree : ∀ j, ∑ k ∈ d.block, (b j k : ℂ) * d.chi k (ConjClasses.mk 1) = 0
  sum_square_one : ∀ y : G, y ^ 2 = 1 →
    ∑ k ∈ d.block, (b ⟨0, by omega⟩ k : ℂ) * d.chi k (ConjClasses.mk y) = 0

/-- Differences of the orbit representatives from one are genuine generalized
characters, with no extra integrality hypothesis. -/
theorem orbit_sub_one_generalized {S : Sylow 2 G} {n : ℕ}
    (D : OrbitSystem S n) (j : Fin D.r) : IsGeneralizedCharacter (D.ψ j - 1) :=
by
  obtain ⟨m, ρ, _, hρ⟩ := (D.linear j).1
  exact IsCharacter.sub_one_isGeneralized ⟨m, ρ, hρ⟩

/-- The distinguished difference is zero on every element whose square is one. -/
theorem orbit_first_sub_one_eq_zero {S : Sylow 2 G} {n : ℕ}
    (D : OrbitSystem S n) (hn : 2 ≤ n) (s : S) (hs : s ^ 2 = 1) :
    (D.ψ ⟨0, by have := D.five_le; omega⟩ - 1) s = 0 := by
  have hψ : D.ψ ⟨0, by have := D.five_le; omega⟩ s = 1 := by
    by_contra hne
    have horder := D.first_support_order s hne
    have hle := orderOf_le_of_pow_eq_one (by omega : 0 < 2) hs
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn
    norm_num at hpow
    omega
  exact sub_eq_zero.mpr hψ

/-- Assemble Brauer's principal-block restriction columns from the actual
ordinary orbit system and the principal-block column kernel. -/
theorem exists_columnSystem (d : PrincipalCongruenceBlockData G)
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (h : ¬ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)) :
    Nonempty (ColumnSystem d S n) := by
  classical
  obtain ⟨D⟩ := HomocyclicSylowLinearCharacters.exists_orbitSystem S hn e h
  let b (j : Fin D.r) : d.I → ℤ :=
    coefficient d S (D.ψ j - 1) (orbit_sub_one_generalized D j)
  have hzero (j : Fin D.r) : (D.ψ j - 1) 1 = 0 := by
    exact sub_eq_zero.mpr (D.linear j).2
  refine ⟨{
    toOrbitSystem := D
    b := b
    support := fun j k hk => coefficient_eq_zero_of_not_mem d S _ _ hk
    coefficient_eq := fun j k hk => coefficient_cast d S _ _ hk
    principal := fun j => coefficient_principal_sub_one d S _ _ _
      (D.linear j).1 (D.nonprincipal j) rfl
    gram := ?_
    reconstruction := ?_
    sum_degree := fun j => coefficient_sum_degree_eq_zero d S S.isPGroup' _ _ (hzero j)
    sum_square_one := fun y hy => coefficient_sum_square_one_eq_zero d S S.isPGroup'
      _ _ (fun s hs => orbit_first_sub_one_eq_zero D hn s hs) y hy }⟩
  · intro i j
    change ∑ k, coefficient d S _ _ k * coefficient d S _ _ k = _
    rw [coefficient_pairing_eq_sum_block]
    have hp := restrictionColumn_pairing d S hn e (D.ψ i - 1) (D.ψ j - 1)
      (orbit_sub_one_generalized D i) (orbit_sub_one_generalized D j) (hzero i)
    have hd := D.pairing i j
    have heq : conjugacySum (S : Subgroup G) (D.ψ j - 1) =
        HomocyclicSylowLinearCharacters.conjugacySum S (D.ψ j - 1) := by
      funext s
      unfold conjugacySum HomocyclicSylowLinearCharacters.conjugacySum
      congr 1
      ext t
      simp
    have hp' : (∑ k ∈ d.block, (coefficient d S (D.ψ i - 1)
        (orbit_sub_one_generalized D i) k : ℂ) *
        (coefficient d S (D.ψ j - 1) (orbit_sub_one_generalized D j) k : ℂ)) =
        (3 : ℂ) + if i = j then 1 else 0 := by
      calc
        _ = scalarProduct S (conjugacySum (S : Subgroup G) (D.ψ j - 1))
            (D.ψ i - 1) := by
          convert hp using 1
          congr 1
          exact Subsingleton.elim _ _
        _ = _ := by rw [heq]; convert hd using 1
    exact_mod_cast hp'
  · intro k hk δ hδ s hs
    apply D.constant_of_coefficients
      (fun t => d.chi k (ConjClasses.mk (t : G))) ?_ (δ : ℂ) ?_ s hs
    · intro t u htu
      rw [ConjClasses.mk_eq_mk_iff_isConj.mpr htu]
    · intro j
      calc
        _ = (coefficient d S (D.ψ j - 1) (orbit_sub_one_generalized D j) k : ℂ) := by
          convert (coefficient_cast d S _ (orbit_sub_one_generalized D j) hk).symm using 1
          congr 1
          exact Subsingleton.elim _ _
        _ = _ := by exact_mod_cast hδ j

end HomocyclicSylowColumns
