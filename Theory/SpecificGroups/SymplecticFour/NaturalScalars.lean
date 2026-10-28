module
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic

/-!
# Arbitrary-prime natural scalars for the symplectic four-group

The actual point and plane two-cores fix precisely the corresponding natural
subspaces. Their diagonal tori act there by a nonidentity field scalar and
centralize the local quotient by its two-core. Cauchy supplies every prime
dividing the field-unit order, as required by the source's outer-order argument.

Source: Aschbacher--Smith, 10.2.9, printed p.751. This extends the cubic scalar
calculation without imposing divisibility by three on the field-unit group.
-/

@[expose] public section
open Matrix Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.NaturalScalars
open NaturalScalarCubic
variable {F : Type*} [Field F] [CharP F 2]
omit [CharP F 2] in
private theorem scalar_moves {s : Fˣ} (hs : s ≠ 1) {v : Vector F} (hv : v ≠ 0)
    {x : Sp F} (ha : x • v = (s : F) • v) : x • v ≠ v := by
  intro he
  have hz : ((s : F) - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← ha, he, sub_self]
  exact hs (Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv)))

omit [CharP F 2] in
private theorem point_scalar_action (s : Fˣ) (v : Vector F) (hv : v ∈ point F) :
    diagonalTorus s 1 • v = (s : F) • v := by
  obtain ⟨hv1, hvr⟩ := (mem_point_iff v).mp hv
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [diagonalTorus, Matrix.mulVec_diagonal, hv1, hvr]

omit [CharP F 2] in
private theorem plane_scalar_action (s : Fˣ) (v : Vector F) (hv : v ∈ plane F) :
    diagonalTorus s s • v = (s : F) • v := by
  have hvr : ∀ i, v (.inr i) = 0 := hv
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [diagonalTorus, Matrix.mulVec_diagonal, hvr]

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


/-- A prime-order normalizer element moves every nonzero natural vector fixed by
the point-local two-core and acts trivially on the local two-core quotient. -/
theorem point_prime_moves_fixed {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hn : 1 < n) (hp : p ∣ Nat.card F - 1) (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ q ∈ (pointLocal (F := F)).pCoreIn 2, q • v = v) :
    ∃ x : Sp F, orderOf x = p ∧ x ∈ normalizer (pointLocal (F := F) : Set (Sp F)) ∧
      (∀ (b : Sp F) (_ : b ∈ pointLocal), ⁅x,b⁆ ∈ pointLocal.pCoreIn 2) ∧ x • v ≠ v := by
  have hcore : (pointLocal (F := F)).pCoreIn 2 = pointRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [pointLocal_core_eq hF hn]
  have hvp : v ∈ point F := point_radical_fixed v (by rwa [hcore] at hfix)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    simpa only [Nat.card_units] using hp)
  have hne : s ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hs
    exact (Fact.out : p.Prime).ne_one hs.symm
  have hN : pointParabolic (F := F) ≤ normalizer (pointLocal (F := F) : Set (Sp F)) :=
    (DiagramAutomorphisms.pointLocal_normalizer hF hn).ge
  obtain ⟨hn,hc⟩ := local_core_commutator pointParabolic pointLocal pointLocal_le hN
    (RootCoreTori.point_scalar_mem_coreCenter hF hn s)
  refine ⟨diagonalTorus s 1, ?_, hn, hc, ?_⟩
  · exact (orderOf_injective (RootTori.parameter 0) (RootTori.parameter_injective 0) s).trans hs
  · exact scalar_moves hne hv (point_scalar_action s v hvp)

/-- The prime-order plane scalar moves every nonzero natural vector fixed by the plane
radical, while acting trivially on the plane-local two-core quotient. -/
theorem plane_prime_moves_fixed {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hn : 1 < n) (hp : p ∣ Nat.card F - 1) (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ q ∈ (planeLocal (F := F)).pCoreIn 2, q • v = v) :
    ∃ x : Sp F, orderOf x = p ∧ x ∈ normalizer (planeLocal (F := F) : Set (Sp F)) ∧
      (∀ (b : Sp F) (_ : b ∈ planeLocal), ⁅x,b⁆ ∈ planeLocal.pCoreIn 2) ∧ x • v ≠ v := by
  have hcore : (planeLocal (F := F)).pCoreIn 2 = planeRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [planeLocal_core_eq hF hn]
  have hvp : v ∈ plane F := plane_radical_fixed v (by rwa [hcore] at hfix)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    simpa only [Nat.card_units] using hp)
  have hne : s ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hs
    exact (Fact.out : p.Prime).ne_one hs.symm
  have hN : planeParabolic (F := F) ≤ normalizer (planeLocal (F := F) : Set (Sp F)) :=
    (DiagramAutomorphisms.planeLocal_normalizer hF hn).ge
  obtain ⟨hn,hc⟩ := local_core_commutator planeParabolic planeLocal planeLocal_le hN
    (RootCoreTori.plane_scalar_mem_coreCenter hF hn s)
  refine ⟨diagonalTorus s s, ?_, hn, hc, ?_⟩
  · exact (orderOf_injective planeScalar planeScalar_injective s).trans hs
  · exact scalar_moves hne hv (plane_scalar_action s v hvp)

end Theory.SpecificGroups.SymplecticFour.NaturalScalars
