module
public import Theory.SpecificGroups.SymplecticFour.ScalarRadical
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# Arbitrary prime scalars on the two symplectic local radicals

The point and plane scalar tori centralize their SL₂ quotients and
have no nonidentity fixed point on the full elementary radical. The
prime may be any divisor of |F|-1; the original module need only be a
nonzero subgroup of that radical.
Source: Aschbacher--Smith, 10.2.9, printed pp.750--751.
-/

public section
noncomputable section
open Matrix Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

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

omit [CharP F 2] [Finite F] in
private theorem local_core_commutator (P B : Subgroup (Sp F))
    (hBP : B ≤ P) (hN : P ≤ normalizer (B : Set (Sp F)))
    {x : Sp F} (hx : x ∈ P.coreCenterIn 2) :
    x ∈ normalizer (B : Set (Sp F)) ∧ ∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2 := by
  obtain ⟨hxP,hc⟩ := (mem_coreCenterIn_iff 2 P x).mp hx
  refine ⟨hN hxP, fun b hb => inf_pCoreIn_le_of_le 2 hBP ⟨?_,hc b (hBP hb)⟩⟩
  exact le_normalizer_iff_commutator_le_right.mp (zpowers_le.mpr (hN hxP))
    (commutator_mem_commutator (mem_zpowers x) hb)


/-- A chosen prime divisor of the field-unit order supplies a point scalar. -/
theorem point_prime_scalar {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hp : p ∣ 2 ^ n - 1) :
    ∃ x : Sp F, orderOf x = p ∧ x ∈ normalizer (pointLocal (F := F) : Set (Sp F)) ∧
      (∀ (b : Sp F) (_ : b ∈ pointLocal), ⁅x,b⁆ ∈ pointLocal.pCoreIn 2) ∧
      ∀ (q : Sp F) (_ : q ∈ pointLocal.pCoreIn 2), Commute q x → q = 1 := by
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card Fˣ by rwa [Nat.card_units,hF])
  have hcore : (pointLocal (F := F)).pCoreIn 2 = pointRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [pointLocal_core_eq hF hn]
  have hN : pointParabolic (F := F) ≤ normalizer (pointLocal (F := F) : Set (Sp F)) :=
    (DiagramAutomorphisms.pointLocal_normalizer hF hn).ge
  obtain ⟨hnorm,hc⟩ := local_core_commutator pointParabolic pointLocal pointLocal_le hN
    (RootCoreTori.point_scalar_mem_coreCenter hF hn s)
  refine ⟨diagonalTorus s 1,
    (orderOf_injective (RootTori.parameter 0) (RootTori.parameter_injective 0) s).trans hs,
    hnorm,hc,?_⟩
  intro q hq hcomm
  apply ScalarRadical.point_fixed_eq_one s ?_ q (hcore ▸ hq) hcomm
  intro he
  have hh : 1 = p := by simpa [he] using hs
  exact (Fact.out : p.Prime).ne_one hh.symm

/-- The same prime supplies a scalar on the plane radical. -/
theorem plane_prime_scalar {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hp : p ∣ 2 ^ n - 1) :
    ∃ x : Sp F, orderOf x = p ∧ x ∈ normalizer (planeLocal (F := F) : Set (Sp F)) ∧
      (∀ (b : Sp F) (_ : b ∈ planeLocal), ⁅x,b⁆ ∈ planeLocal.pCoreIn 2) ∧
      ∀ (q : Sp F) (_ : q ∈ planeLocal.pCoreIn 2), Commute q x → q = 1 := by
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card Fˣ by rwa [Nat.card_units,hF])
  have hcore : (planeLocal (F := F)).pCoreIn 2 = planeRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [planeLocal_core_eq hF hn]
  have hN : planeParabolic (F := F) ≤ normalizer (planeLocal (F := F) : Set (Sp F)) :=
    (DiagramAutomorphisms.planeLocal_normalizer hF hn).ge
  obtain ⟨hnorm,hc⟩ := local_core_commutator planeParabolic planeLocal planeLocal_le hN
    (RootCoreTori.plane_scalar_mem_coreCenter hF hn s)
  refine ⟨diagonalTorus s s,
    (orderOf_injective planeScalar planeScalar_injective s).trans hs,hnorm,hc,?_⟩
  intro q hq hcomm
  apply ScalarRadical.plane_fixed_eq_one s ?_ q (hcore ▸ hq) hcomm
  intro he
  have hh : 1 = p := by simpa [he] using hs
  exact (Fact.out : p.Prime).ne_one hh.symm

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
