module
public import Theory.SpecificGroups.SymplecticFour.RootCoreTori.Quotients
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.GroupTheory.PCoreRestriction

/-!
# Fixed-point-free scalar tori on symplectic parabolic radicals

In characteristic two, every nonidentity scalar in the point torus
`diag(s,1,s⁻¹,1)` fixes only the identity in the point radical: its three
coordinates have weights s, s and s². The plane scalar `diag(s,s,s⁻¹,s⁻¹)`
has weight s² on all symmetric-matrix coordinates and has the same property.
The existing full-parabolic quotient calculations put both tori in the
centralizer of their local factor modulo its two-core. Over a field of order
four, these give elements of order three with both properties simultaneously.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751. The statement retains
the full elementary radical, including its central coordinates; it does not
replace that radical by its natural four-dimensional central quotient.
-/

public section
noncomputable section
open Matrix Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.ScalarRadical
variable {F : Type*} [Field F] [CharP F 2]

private theorem scalar_ne_inverse (s : Fˣ) (hs : s ≠ 1) :
    (s : F) ≠ (↑s⁻¹ : F) := by
  intro he
  apply hs
  apply Units.ext
  apply CharTwo.sq_injective
  simpa [pow_two, ← he] using s.val_inv

/-- A nontrivial point scalar fixes no nonidentity radical element. -/
theorem point_fixed_eq_one (s : Fˣ) (hs : s ≠ 1)
    (q : Sp F) (hq : q ∈ pointRadicalAmbient)
    (hc : Commute q (diagonalTorus s 1)) : q = 1 := by
  obtain ⟨q, hq, rfl⟩ := hq
  rw [pointRadical_eq_element q hq] at hc ⊢
  let u := q.val.val (.inl 1) (.inr 0)
  let v := q.val.val (.inr 1) (.inr 0)
  let z := q.val.val (.inl 0) (.inr 0)
  have hentry (i j : Fin 2 ⊕ Fin 2) :=
    congrArg (fun a : Sp F => a.val i j) hc.eq
  have hu := hentry (.inl 0) (.inr 1)
  have hv := hentry (.inl 0) (.inl 1)
  have hz := hentry (.inl 0) (.inr 0)
  change ((pointRadicalMatrix u v z) * (diagonalTorus s 1).val) (.inl 0) (.inr 1) =
    ((diagonalTorus s 1).val * (pointRadicalMatrix u v z)) (.inl 0) (.inr 1) at hu
  change ((pointRadicalMatrix u v z) * (diagonalTorus s 1).val) (.inl 0) (.inl 1) =
    ((diagonalTorus s 1).val * (pointRadicalMatrix u v z)) (.inl 0) (.inl 1) at hv
  change ((pointRadicalMatrix u v z) * (diagonalTorus s 1).val) (.inl 0) (.inr 0) =
    ((diagonalTorus s 1).val * (pointRadicalMatrix u v z)) (.inl 0) (.inr 0) at hz
  simp only [diagonalTorus, Matrix.mul_diagonal, Matrix.diagonal_mul] at hu hv hz
  change u * 1 = (s : F) * u at hu
  change v * 1 = (s : F) * v at hv
  change z * (↑s⁻¹ : F) = (s : F) * z at hz
  have hs' : (s : F) ≠ 1 := fun h => hs (Units.ext h)
  have hu0 : u = 0 := by
    have hh : ((s : F) - 1) * u = 0 := by linear_combination -hu
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hs')
  have hv0 : v = 0 := by
    have hh : ((s : F) - 1) * v = 0 := by linear_combination -hv
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hs')
  have hz0 : z = 0 := by
    have hh : ((s : F) - (↑s⁻¹ : F)) * z = 0 := by linear_combination -hz
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (scalar_ne_inverse s hs))
  change (pointRadicalElement u v z).val = 1
  rw [hu0, hv0, hz0, pointRadicalElement_zero]
  rfl

/-- A nontrivial plane scalar fixes no nonidentity radical element. -/
theorem plane_fixed_eq_one (s : Fˣ) (hs : s ≠ 1)
    (q : Sp F) (hq : q ∈ planeRadicalAmbient)
    (hc : Commute q (diagonalTorus s s)) : q = 1 := by
  obtain ⟨q, hq, rfl⟩ := hq
  have hm := Plane.radical_matrix (⟨q, hq⟩ : Plane.radical)
  have hz (i j : Fin 2) : q.val.val (.inl i) (.inr j) = 0 := by
    have hh := congrArg (fun a : Sp F => a.val (.inl i) (.inr j)) hc.eq
    change (q.val.val * (diagonalTorus s s).val) (.inl i) (.inr j) =
      ((diagonalTorus s s).val * q.val.val) (.inl i) (.inr j) at hh
    simp only [diagonalTorus, Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    have hh' : q.val.val (.inl i) (.inr j) * (↑s⁻¹ : F) =
        (s : F) * q.val.val (.inl i) (.inr j) := by
      fin_cases i <;> fin_cases j <;> exact hh
    have he : ((s : F) - (↑s⁻¹ : F)) * q.val.val (.inl i) (.inr j) = 0 := by
      linear_combination -hh'
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (scalar_ne_inverse s hs))
  apply Subtype.ext
  change q.val.val = 1
  change q.val.val = _ at hm
  rw [hm]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.toBlocks₁₂, Matrix.one_apply, hz]

private def planeScalar : Fˣ →* Sp F where
  toFun s := diagonalTorus s s
  map_one' := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> simp [diagonalTorus, Matrix.diagonal]
  map_mul' s t := by
    apply Subtype.ext
    change (diagonalTorus (s * t) (s * t)).val =
      (diagonalTorus s s).val * (diagonalTorus t t).val
    simp only [diagonalTorus, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [mul_comm]

omit [CharP F 2] in
private theorem planeScalar_injective : Function.Injective (planeScalar (F := F)) := by
  intro s t h
  apply Units.ext
  have he := congrArg (fun g : Sp F => g.val (.inl 0) (.inl 0)) h
  simpa [planeScalar, diagonalTorus, Matrix.diagonal] using he

variable [Finite F]

omit [CharP F 2] in
private theorem scalar_exists (hF : Nat.card F = 4) :
    ∃ s : Fˣ, orderOf s = 3 := by
  apply exists_prime_orderOf_dvd_card' 3
  rw [Nat.card_units, hF]

omit [CharP F 2] [Finite F] in
private theorem local_core_commutator (P B : Subgroup (Sp F))
    (hBP : B ≤ P) (hN : P ≤ normalizer (B : Set (Sp F)))
    {x : Sp F} (hx : x ∈ P.coreCenterIn 2) :
    x ∈ normalizer (B : Set (Sp F)) ∧ ∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2 := by
  obtain ⟨hxP,hc⟩ := (mem_coreCenterIn_iff 2 P x).mp hx
  refine ⟨hN hxP, fun b hb => inf_pCoreIn_le_of_le 2 hBP ⟨?_,hc b (hBP hb)⟩⟩
  exact le_normalizer_iff_commutator_le_right.mp (zpowers_le.mpr (hN hxP))
    (commutator_mem_commutator (mem_zpowers x) hb)

/-- The point-local row supplies a cubic scalar, trivial on its core quotient
and fixed-point-free on its full elementary core. -/
theorem point_cubic_scalar (hF : Nat.card F = 4) :
    ∃ x : Sp F, orderOf x = 3 ∧ x ∈ normalizer (pointLocal (F := F) : Set (Sp F)) ∧
      (∀ (b : Sp F) (_ : b ∈ pointLocal), ⁅x,b⁆ ∈ pointLocal.pCoreIn 2) ∧
      ∀ (q : Sp F) (_ : q ∈ pointLocal.pCoreIn 2), Commute q x → q = 1 := by
  obtain ⟨s,hs⟩ := scalar_exists hF
  have hcore : (pointLocal (F := F)).pCoreIn 2 = pointRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [pointLocal_core_eq (n := 2) hF (by decide)]
  have hN : pointParabolic (F := F) ≤ normalizer (pointLocal (F := F) : Set (Sp F)) :=
    (DiagramAutomorphisms.pointLocal_normalizer (n := 2) hF (by decide)).ge
  obtain ⟨hn,hc⟩ := local_core_commutator pointParabolic pointLocal pointLocal_le hN
    (RootCoreTori.point_scalar_mem_coreCenter (n := 2) hF (by decide) s)
  refine ⟨diagonalTorus s 1, ?_, hn, hc, ?_⟩
  · exact (orderOf_injective (RootTori.parameter 0) (RootTori.parameter_injective 0) s).trans hs
  · intro q hq hcomm
    exact point_fixed_eq_one s (fun he => by simp [he] at hs) q (hcore ▸ hq) hcomm

/-- The plane-local row has the same cubic scalar conclusion on its actual core. -/
theorem plane_cubic_scalar (hF : Nat.card F = 4) :
    ∃ x : Sp F, orderOf x = 3 ∧ x ∈ normalizer (planeLocal (F := F) : Set (Sp F)) ∧
      (∀ (b : Sp F) (_ : b ∈ planeLocal), ⁅x,b⁆ ∈ planeLocal.pCoreIn 2) ∧
      ∀ (q : Sp F) (_ : q ∈ planeLocal.pCoreIn 2), Commute q x → q = 1 := by
  obtain ⟨s,hs⟩ := scalar_exists hF
  have hcore : (planeLocal (F := F)).pCoreIn 2 = planeRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [planeLocal_core_eq (n := 2) hF (by decide)]
  have hN : planeParabolic (F := F) ≤ normalizer (planeLocal (F := F) : Set (Sp F)) :=
    (DiagramAutomorphisms.planeLocal_normalizer (n := 2) hF (by decide)).ge
  obtain ⟨hn,hc⟩ := local_core_commutator planeParabolic planeLocal planeLocal_le hN
    (RootCoreTori.plane_scalar_mem_coreCenter (n := 2) hF (by decide) s)
  refine ⟨diagonalTorus s s, ?_, hn, hc, ?_⟩
  · exact (orderOf_injective planeScalar planeScalar_injective s).trans hs
  · intro q hq hcomm
    exact plane_fixed_eq_one s (fun he => by simp [he] at hs) q (hcore ▸ hq) hcomm

end Theory.SpecificGroups.SymplecticFour.ScalarRadical
