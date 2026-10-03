module

public import Theory.Representation.CyclicPermutationSummand
public import Theory.LinearAlgebra.Matrix.IdempotentLift
public import Theory.Character.ModularBlock.PGroupInvariantSum

/-!
# Integral traces of cyclic permutation summands

For a permutation of prime-power order, an equivariant integral idempotent has
trace against the permutation equal to the trace of any idempotent lifting
its restriction to the fixed basis vectors in characteristic `p`.

The modular summand decomposition selects whole permutation orbits. Lift its
equivariant change of basis entrywise along a section of the residue map;
unit detection makes this lift invertible. Congruent idempotents then have
exactly equal integral traces. On fixed basis vectors, restriction preserves
products by cancellation of nontrivial `p`-group orbits, so the same selected
fixed diagonal projector computes the trace of the given fixed-point lift.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), p. 71, equation (6), citing Brauer--Suzuki, Section I.
-/

public section
noncomputable section

namespace Matrix

variable {R k X : Type*} [CommRing R] [Field k]
  [Fintype X] [DecidableEq X]

/-- Commuting with a permutation matrix means invariance of entries under
simultaneous permutation of the two indices. -/
theorem commute_permMatrix_iff_entries (σ : Equiv.Perm X) (A : Matrix X X R) :
    Commute (σ.permMatrix R) A ↔ ∀ i j, A (σ i) (σ j) = A i j := by
  change (σ.permMatrix R) * A = A * (σ.permMatrix R) ↔ _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  constructor
  · intro h i j
    simpa using congrArg (fun M : Matrix X X R => M i (σ j)) h
  · intro h
    ext i j
    simpa using h i (σ.symm j)

/-- An equivariant matrix unit over the residue field lifts to an equivariant
unit whenever the surjective coefficient map detects units. -/
theorem exists_commuting_unit_lift (f : R →+* k)
    (hsurj : Function.Surjective f) (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (σ : Equiv.Perm X) (U : (Matrix X X k)ˣ)
    (hU : Commute (σ.permMatrix k) (U : Matrix X X k)) :
    ∃ V : (Matrix X X R)ˣ,
      f.mapMatrix (V : Matrix X X R) = U ∧
      Commute (σ.permMatrix R) (V : Matrix X X R) := by
  obtain ⟨g, hg⟩ := hsurj.hasRightInverse
  let A : Matrix X X R := fun i j => g ((U : Matrix X X k) i j)
  have hA : f.mapMatrix A = U := by ext i j; exact hg _
  have hu : IsUnit A := isUnit_of_map_det_ne_zero f hf A (by
    rw [hA]
    exact ((isUnit_iff_isUnit_det _).mp U.isUnit).ne_zero)
  refine ⟨hu.unit, ?_, ?_⟩
  · simpa only [hu.unit_spec] using hA
  · rw [hu.unit_spec, commute_permMatrix_iff_entries]
    intro i j
    exact congrArg g ((commute_permMatrix_iff_entries σ _).mp hU i j)

omit [Fintype X] [DecidableEq X] in
private theorem fixedPoints_zpowers (σ : Equiv.Perm X) :
    MulAction.fixedPoints (Subgroup.zpowers σ) X = {x | σ x = x} := by
  ext x
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h g
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (Equiv.Perm X) x :=
      Subgroup.zpowers_le.mpr h
    exact hle g.property

/-- Restriction to fixed indices is multiplicative on equivariant matrices
in characteristic `p`. Nonfixed orbits in the matrix product cancel. -/
theorem submatrix_fixed_mul_of_prime {p : ℕ} [Fact p.Prime] [CharP k p] (σ : Equiv.Perm X)
    {n : ℕ} (hσ : σ ^ (p ^ n) = 1) (A C : Matrix X X k)
    (hA : Commute (σ.permMatrix k) A) (hC : Commute (σ.permMatrix k) C) :
    (A * C).submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) =
      A.submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) *
      C.submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) := by
  classical
  have hp : IsPGroup p (Subgroup.zpowers σ) := IsPGroup.of_card_dvd_pow (n := n)
    (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hσ)
  ext i j
  change (∑ x : X, A i.val x * C x j.val) =
    ∑ x : {x // σ x = x}, A i.val x.val * C x.val j.val
  have hinv (x : X) : A i.val (σ x) * C (σ x) j.val = A i.val x * C x j.val := by
    have ha := (commute_permMatrix_iff_entries σ A).mp hA i.val x
    have hc := (commute_permMatrix_iff_entries σ C).mp hC x j.val
    rw [i.property] at ha
    rw [j.property] at hc
    rw [ha, hc]
  have hsum := ModularBlock.SubgroupBrauerMap.sum_eq_sum_fixedPoints_of_smul_invariant
    hp (fun x => A i.val x * C x j.val)
    (Representation.perm_invariant_zpowers σ (fun x => A i.val x * C x j.val) hinv)
  let e : MulAction.fixedPoints (Subgroup.zpowers σ) X ≃ {x // σ x = x} :=
    Equiv.setCongr (fixedPoints_zpowers σ)
  have he := @Fintype.sum_equiv _ _ k (Fintype.ofFinite _) inferInstance _ e
    (fun x => A i.val x.val * C x.val j.val)
    (fun x => A i.val x.val * C x.val j.val) (fun _ => rfl)
  convert! hsum.trans he using 1
  congr 1
  ext x
  simp

private theorem map_permMatrix (f : R →+* k) (σ : Equiv.Perm X) :
    f.mapMatrix (σ.permMatrix R) = σ.permMatrix k :=
  PEquiv.map_toMatrix f σ.toPEquiv

private theorem map_unit_inv (f : R →+* k) (V : (Matrix X X R)ˣ)
    (U : (Matrix X X k)ˣ) (h : f.mapMatrix (V : Matrix X X R) = U) :
    f.mapMatrix (↑V⁻¹ : Matrix X X R) = (↑U⁻¹ : Matrix X X k) := by
  have hu : Units.map f.mapMatrix.toMonoidHom V = U := Units.ext h
  exact congrArg (fun W : (Matrix X X k)ˣ => (↑(W⁻¹) : Matrix X X k)) hu

private theorem trace_mul_eq_of_lifted_conj (f : R →+* k)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (P D T : Matrix X X R) (hP : IsIdempotentElem P) (hD : IsIdempotentElem D)
    (hTP : Commute T P) (hTD : Commute T D) (V : (Matrix X X R)ˣ)
    (hTV : Commute T (V : Matrix X X R))
    (heq : f.mapMatrix P = f.mapMatrix ((V : Matrix X X R) * D * (↑(V⁻¹) : Matrix X X R))) :
    trace (T * P) = trace (T * D) := by
  have hQ : IsIdempotentElem ((V : Matrix X X R) * D * (↑(V⁻¹) : Matrix X X R)) := by
    change ((V : Matrix X X R) * D * (↑(V⁻¹) : Matrix X X R)) * ((V : Matrix X X R) * D * (↑(V⁻¹) : Matrix X X R)) = _
    calc
      _ = (V : Matrix X X R) * (D * D) * (↑(V⁻¹) : Matrix X X R) := by simp [mul_assoc]
      _ = _ := by rw [hD.eq]
  rw [trace_mul_eq_of_idempotent_map_eq f hf P _ T hP hQ heq hTP
    ((hTV.mul_right hTD).mul_right hTV.units_inv_right)]
  have hconj : T * ((V : Matrix X X R) * D * (↑(V⁻¹) : Matrix X X R)) =
      (V : Matrix X X R) * (T * D) * (↑(V⁻¹) : Matrix X X R) := by
    simp only [← mul_assoc, hTV.eq]
  rw [hconj, trace_units_conj]

private theorem diagonal_indicator_idempotent (s : Set X) :
    IsIdempotentElem (diagonal (s.indicator (fun _ => (1 : R)))) := by
  classical
  change diagonal _ * diagonal _ = _
  rw [diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

private theorem commute_diagonal_indicator (σ : Equiv.Perm X) (s : Set X)
    (hs : ∀ x, σ x ∈ s ↔ x ∈ s) :
    Commute (σ.permMatrix R) (diagonal (s.indicator (fun _ => (1 : R)))) := by
  classical
  rw [commute_permMatrix_iff_entries]
  intro i j
  by_cases hij : i = j
  · subst j
    simp [hs, Set.indicator]
  · have hij' : σ i ≠ σ j := fun h => hij (σ.injective h)
    simp [hij, hij']

private theorem map_diagonal_indicator (f : R →+* k) (s : Set X) :
    f.mapMatrix (diagonal (s.indicator (fun _ => (1 : R)))) =
      diagonal (s.indicator (fun _ => (1 : k))) := by
  classical
  ext i j
  by_cases hij : i = j <;>
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Set.indicator, hij]

private theorem trace_permMatrix_diagonal (σ : Equiv.Perm X) (d : X → R) :
    trace (σ.permMatrix R * diagonal d) =
      trace (diagonal (fun x : {x // σ x = x} => d x.val)) := by
  rw [PEquiv.toMatrix_toPEquiv_mul, trace, trace_diagonal]
  change (∑ x, diagonal d (σ x) x) = ∑ x : {x // σ x = x}, d x.val
  have hdiag (x : X) : diagonal d (σ x) x = if σ x = x then d x else 0 := by
    by_cases hx : σ x = x <;> simp [hx]
  simp_rw [hdiag]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun x => σ x = x)) (by simp) d

/-- Exact integral permutation-summand trace comparison. The residue map is
surjective and detects units; no completeness or Henselian hypothesis is needed.
The fixed-index idempotent only has to lift the fixed-index residue of `P`. -/
theorem trace_permMatrix_mul_eq_trace_fixed_lift_of_prime {p : ℕ} [Fact p.Prime] [CharP k p]
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (σ : Equiv.Perm X) {n : ℕ} (hσ : σ ^ (p ^ n) = 1)
    (P : Matrix X X R) (hP : IsIdempotentElem P)
    (hTP : Commute (σ.permMatrix R) P)
    (B : Matrix {x // σ x = x} {x // σ x = x} R) (hB : IsIdempotentElem B)
    (hBmap : f.mapMatrix B = (f.mapMatrix P).submatrix Subtype.val Subtype.val) :
    trace (σ.permMatrix R * P) = trace B := by
  classical
  let F := {x // σ x = x}
  let e : F → X := Subtype.val
  have hPk := hP.map f.mapMatrix
  have hTk : Commute (σ.permMatrix k) (f.mapMatrix P) := by
    simpa only [map_permMatrix] using hTP.map f.mapMatrix
  obtain ⟨s, U, hs, hU, hconj⟩ :=
    CyclicPermutation.exists_unit_conj_diagonal_of_prime σ hσ (f.mapMatrix P) hPk hTk
  let D : Matrix X X R := diagonal (s.indicator (fun _ => 1))
  let Dk : Matrix X X k := diagonal (s.indicator (fun _ => 1))
  have hD : IsIdempotentElem D := diagonal_indicator_idempotent s
  have hTD : Commute (σ.permMatrix R) D := commute_diagonal_indicator σ s hs
  have hTDk : Commute (σ.permMatrix k) Dk := commute_diagonal_indicator σ s hs
  have hDmap : f.mapMatrix D = Dk := map_diagonal_indicator f s
  obtain ⟨V, hV, hTV⟩ := exists_commuting_unit_lift f hsurj hf σ U hU
  have hVi := map_unit_inv f V U hV
  have htraceP : trace (σ.permMatrix R * P) = trace (σ.permMatrix R * D) := by
    apply trace_mul_eq_of_lifted_conj f hf P D _ hP hD hTP hTD V hTV
    rw [map_mul, map_mul, hV, hVi, hDmap]
    exact hconj
  let t : Set F := {x | x.val ∈ s}
  let E : Matrix F F R := diagonal (t.indicator (fun _ => 1))
  have hE : IsIdempotentElem E := diagonal_indicator_idempotent t
  have hDfix : Dk.submatrix e e = f.mapMatrix E := by
    rw [show E = diagonal (t.indicator (fun _ => (1 : R))) from rfl,
      map_diagonal_indicator]
    rw [show Dk = diagonal (s.indicator (fun _ => (1 : k))) from rfl,
      submatrix_diagonal _ e Subtype.val_injective]
    rfl
  let U₀ : (Matrix F F k)ˣ :=
    { val := (U : Matrix X X k).submatrix e e
      inv := (↑(U⁻¹) : Matrix X X k).submatrix e e
      val_inv := by
        rw [← submatrix_fixed_mul_of_prime σ hσ _ _ hU hU.units_inv_right, Units.mul_inv]
        exact submatrix_one e Subtype.val_injective
      inv_val := by
        rw [← submatrix_fixed_mul_of_prime σ hσ _ _ hU.units_inv_right hU, Units.inv_mul]
        exact submatrix_one e Subtype.val_injective }
  have hBconj : f.mapMatrix B =
      (U₀ : Matrix F F k) * f.mapMatrix E * (↑(U₀⁻¹) : Matrix F F k) := by
    rw [hBmap, hconj,
      submatrix_fixed_mul_of_prime σ hσ _ _ (hU.mul_right hTDk) hU.units_inv_right,
      submatrix_fixed_mul_of_prime σ hσ _ _ hU hTDk]
    change (U : Matrix X X k).submatrix e e * Dk.submatrix e e *
      (↑(U⁻¹) : Matrix X X k).submatrix e e = _
    rw [hDfix]
    rfl
  obtain ⟨W, hW, _⟩ := exists_commuting_unit_lift f hsurj hf (1 : Equiv.Perm F) U₀
    (by simpa only [permMatrix_one] using Commute.one_left (U₀ : Matrix F F k))
  have hWi := map_unit_inv f W U₀ hW
  have htraceB : trace B = trace E := by
    have h := trace_mul_eq_of_lifted_conj f hf B E 1 hB hE
      (Commute.one_left _) (Commute.one_left _) W (Commute.one_left _) (by
        rw [map_mul, map_mul, hW, hWi]
        exact hBconj)
    simpa only [one_mul] using h
  rw [htraceP, htraceB]
  exact trace_permMatrix_diagonal σ (s.indicator (fun _ => (1 : R)))

/-- Characteristic-two specialization, retaining the original API. -/
theorem submatrix_fixed_mul [CharP k 2] (σ : Equiv.Perm X)
    {n : ℕ} (hσ : σ ^ (2 ^ n) = 1) (A C : Matrix X X k)
    (hA : Commute (σ.permMatrix k) A) (hC : Commute (σ.permMatrix k) C) :
    (A * C).submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) =
      A.submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) *
      C.submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) := by
  exact submatrix_fixed_mul_of_prime (p := 2) σ hσ A C hA hC

/-- Characteristic-two specialization, retaining the original API. -/
theorem trace_permMatrix_mul_eq_trace_fixed_lift [CharP k 2]
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (σ : Equiv.Perm X) {n : ℕ} (hσ : σ ^ (2 ^ n) = 1)
    (P : Matrix X X R) (hP : IsIdempotentElem P)
    (hTP : Commute (σ.permMatrix R) P)
    (B : Matrix {x // σ x = x} {x // σ x = x} R) (hB : IsIdempotentElem B)
    (hBmap : f.mapMatrix B = (f.mapMatrix P).submatrix Subtype.val Subtype.val) :
    trace (σ.permMatrix R * P) = trace B := by
  exact trace_permMatrix_mul_eq_trace_fixed_lift_of_prime (p := 2) f hsurj hf σ hσ P hP hTP B hB hBmap

end Matrix
