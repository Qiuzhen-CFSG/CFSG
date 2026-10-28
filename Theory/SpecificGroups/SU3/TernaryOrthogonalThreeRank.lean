module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.OrthogonalOrder
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Three-rank of split ternary special orthogonal groups over prime fields

The group here is the determinant-one isometry group with Gram matrix
`!![0,0,1;0,1,0;1,0,0]`, as defined by `splitOrthogonalForm`.
For every odd prime field its three-rank is at most one, including the
characteristic-three case.

We construct the adjoint homomorphism from the actual SL₂ matrix group. In
coordinates `(x,y,z)` representing the trace-zero matrix `!![y,x;2*z,-y]`,
minus the determinant is `2*x*z+y^2`, exactly the quadratic form of this Gram
matrix. Direct matrix identities prove multiplicativity, form preservation,
and determinant one. The kernel is precisely the scalar center of SL₂, so
the image is isomorphic to the actual PSL₂ quotient. The two group-order
formulas show that this image has index two. Its cyclic Sylow three-subgroups
are therefore Sylow in the full orthogonal group. For field orders three
and five, the orthogonal orders are 24 and 120, respectively, with three-part
three, so the same rank bound follows directly.

Source: the ternary orthogonal structure in GLS, *The Classification of the
Finite Simple Groups*, Number 3, §§2.7 and 4.3. The cyclic-Sylow input is the
split/nonsplit torus calculation in Huppert II.8.2–5. This supplies the
orthogonal fixed-group rank calculation used in the inspection in
Aschbacher–Smith, *The Classification of Quasithin Groups*, E.6.18, printed
p.252, for the odd-prime unitary-three family in Theorem C, printed p.33.
-/

open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.TernaryOrthogonal
variable {F : Type*} [Field F]
private abbrev SO (F : Type*) [Field F] := (splitOrthogonalForm F).specialSubgroup
private abbrev SL (F : Type*) [Field F] := Matrix.SpecialLinearGroup (Fin 2) F

private def adjointMatrix (g : SL F) : Matrix (Fin 3) (Fin 3) F :=
  !![g 0 0 ^ 2, -2 * g 0 0 * g 0 1, -2 * g 0 1 ^ 2;
    -g 0 0 * g 1 0, g 0 0 * g 1 1 + g 0 1 * g 1 0, 2 * g 0 1 * g 1 1;
    -g 1 0 ^ 2 / 2, g 1 0 * g 1 1, g 1 1 ^ 2]

private theorem sl_det (g : SL F) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using g.det_coe

private theorem adjointMatrix_det (h2 : (2 : F) ≠ 0) (g : SL F) :
    (adjointMatrix g).det = 1 := by
  calc
    (adjointMatrix g).det = (g 0 0 * g 1 1 - g 0 1 * g 1 0)^3 := by
      simp [adjointMatrix, Matrix.det_fin_three]
      field_simp
      ring
    _ = 1 := by rw [sl_det]; simp

private theorem adjointMatrix_orth (h2 : (2 : F) ≠ 0) (g : SL F) :
    (adjointMatrix g).transpose * (splitOrthogonalForm F).form * adjointMatrix g =
      (splitOrthogonalForm F).form := by
  have hd := sl_det g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjointMatrix, splitOrthogonalForm, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals field_simp
  all_goals first | ring1 | linear_combination (g 0 0 * g 1 1 - g 0 1 * g 1 0 + 1) * hd

private def adjoint (h2 : (2 : F) ≠ 0) (g : SL F) : SO F :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (adjointMatrix g)
      (by rw [adjointMatrix_det h2]; exact one_ne_zero),
    ((splitOrthogonalForm F).mem_specialSubgroup_iff _).mpr
      ⟨adjointMatrix_orth h2 g, Units.ext (adjointMatrix_det h2 g)⟩⟩

private def adjointHom (h2 : (2 : F) ≠ 0) : SL F →* SO F where
  toFun := adjoint h2
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [adjoint, adjointMatrix]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    change adjointMatrix (g * h) = adjointMatrix g * adjointMatrix h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adjointMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals field_simp
    all_goals ring

private theorem adjointHom_ker (h2 : (2 : F) ≠ 0) :
    (adjointHom h2).ker = Subgroup.center (SL F) := by
  ext g
  change adjointHom h2 g = 1 ↔ _
  constructor
  · intro h
    have hm : adjointMatrix g = 1 := congrArg (fun x : SO F => x.val.val) h
    have hb : g 0 1 = 0 := by
      have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) hm
      have : (g 0 1)^2 = 0 := by
        simpa [adjointMatrix, h2] using he
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp this
    have hc : g 1 0 = 0 := by
      have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 2 0) hm
      have : (g 1 0)^2 = 0 := by
        simpa [adjointMatrix, h2] using he
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp this
    have ha : (g 0 0)^2 = 1 := by
      simpa [adjointMatrix] using congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hm
    have hd : g 1 1 = g 0 0 := by
      have he := sl_det g
      simp only [hb, hc, zero_mul, sub_zero] at he
      calc
        g 1 1 = (g 0 0)^2 * g 1 1 := by rw [ha, one_mul]
        _ = g 0 0 * (g 0 0 * g 1 1) := by ring
        _ = g 0 0 := by rw [he, mul_one]
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨g 0 0, by simpa using ha, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, hc, hd]
  · intro h
    obtain ⟨a, ha, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have hm : adjointMatrix g = 1 := by
      unfold adjointMatrix
      have he' : g.val = Matrix.scalar (Fin 2) a := he.symm
      simp only [Fintype.card_fin] at ha
      ext i j
      fin_cases i <;> fin_cases j <;> simp [he', Matrix.scalar_apply, ← pow_two, ha]
    apply Subtype.ext
    apply Units.ext
    exact hm

private noncomputable def pslEquivRange (h2 : (2 : F) ≠ 0) :
    ProjectiveSpecialLinearGroup (Fin 2) F ≃* (adjointHom h2).range :=
  (QuotientGroup.quotientMulEquivOfEq (adjointHom_ker h2).symm).trans
    (QuotientGroup.quotientKerEquivRange (adjointHom h2))

private theorem adjoint_range_index [Finite F] (h2 : (2 : F) ≠ 0)
    (ho : Odd (Nat.card F)) : (adjointHom h2).range.index = 2 := by
  have hc : Nat.card (adjointHom h2).range = Nat.card (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Nat.card_congr (pslEquivRange h2).symm.toEquiv
  have h := (adjointHom h2).range.card_mul_index
  rw [hc, card_splitOrthogonal_specialSubgroup h2,
    ← ProjectiveSpecialLinearGroup.psl2_card_twice ho] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

private theorem rank_of_square_not_dvd {G : Type*} [Group G] [Finite G]
    (h : ¬ 3 ^ 2 ∣ Nat.card G) : primeRank 3 G ≤ 1 := by
  let P : Sylow 3 G := default
  apply P.primeRank_le_one_of_isCyclic
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have hsmall : a ≤ 1 := by
    by_contra! hlarge
    exact h ((ha ▸ pow_dvd_pow 3 (by omega : 2 ≤ a)).trans
      (P : Subgroup G).card_subgroup_dvd_card)
  apply isCyclic_of_card_dvd_prime (p := 3)
  rw [ha]
  simpa using pow_dvd_pow 3 hsmall

private theorem rank_of_large_prime [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : Nat.card F = p) (hlarge : 7 ≤ p) (h2 : (2 : F) ≠ 0) :
    primeRank 3 (SO F) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let H := (adjointHom h2).range
  let e := pslEquivRange h2
  let P : Sylow 3 (ProjectiveSpecialLinearGroup (Fin 2) F) := default
  have hP : IsCyclic P :=
    GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
      (f := 1) (by simpa using hc) (by omega) 3 (by decide)
      (by rw [hc]; exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)) P
  let Q : Sylow 3 H := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : IsCyclic Q := by
    let := hP
    exact isCyclic_of_surjective (e.toMonoidHom.subgroupMap (P : Subgroup _))
      (e.toMonoidHom.subgroupMap_surjective (P : Subgroup _))
  let R : Subgroup (SO F) := (Q : Subgroup H).map H.subtype
  have hR : IsPGroup 3 R := Q.isPGroup'.map H.subtype
  have hi : ¬ 3 ∣ R.index := by
    rw [show R.index = (Q : Subgroup H).index * H.index from Subgroup.index_map_subtype _]
    apply Nat.prime_three.not_dvd_mul Q.not_dvd_index
    rw [show H.index = 2 from adjoint_range_index h2 (hc ▸ ho)]
    decide
  let S : Sylow 3 (SO F) := hR.toSylow hi
  have hS : IsCyclic S := by
    let := hQ
    let eQ : Q ≃* R := (Q : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
    exact isCyclic_of_surjective eQ.toMonoidHom eQ.surjective
  exact S.primeRank_le_one_of_isCyclic hS

/-- The actual split ternary special orthogonal group over any odd prime
field has three-rank at most one, also in characteristic three. -/
public theorem primeRank_three_le_one [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : Nat.card F = p) : primeRank 3 (splitOrthogonalForm F).specialSubgroup ≤ 1 := by
  let := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := by
    apply Ring.two_ne_zero
    intro he
    have hh := FiniteField.even_card_of_char_two he
    rw [← Nat.card_eq_fintype_card, hc] at hh
    obtain ⟨k, hk⟩ := ho
    omega
  by_cases hs : p < 7
  · have hp2 := hp.two_le
    have hcases : p = 3 ∨ p = 5 := by
      obtain ⟨k, hk⟩ := ho
      omega
    apply rank_of_square_not_dvd
    rw [card_splitOrthogonal_specialSubgroup h2, hc]
    rcases hcases with rfl | rfl <;> norm_num
  · exact rank_of_large_prime hp ho hc (by omega) h2

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.TernaryOrthogonal
