module
public import Theory.SpecificGroups.SymplecticFour.ScalarRadical

/-!
# Cubic scalar movement on the natural symplectic module

The common fixed vectors of the point radical form the distinguished point;
those of the plane radical form the distinguished plane. The corresponding
diagonal torus acts as a nonidentity scalar on that entire fixed space.
Over a field of order four it supplies an element of order three, normalizing
the local factor and centralizing its quotient by the actual two-core, that
moves every specified nonzero vector fixed by the radical.

These are calculations in the ordinary natural four-dimensional module.
They are separate from the conjugation action on the parabolic radical.
The consumer is the constrained-action step in Aschbacher–Smith 10.2.9,
printed pp.751–752, using the local matrices of F.1.12, pp.262–264.
-/

public section
noncomputable section
open Matrix Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
variable {F : Type*} [Field F] [CharP F 2]

/-- The point radical fixes only its distinguished line in the natural module. -/
theorem point_radical_fixed (v : Vector F)
    (h : ∀ q ∈ pointRadicalAmbient (F := F), q • v = v) : v ∈ point F := by
  have hm (u w z : F) : (pointRadicalElement u w z).val ∈ pointRadicalAmbient :=
    mem_map_of_mem _ (pointRadicalElement_mem u w z)
  have h₀ := congrFun (h _ (hm 0 0 (1 : F))) (.inl 0)
  have h₁ := congrFun (h _ (hm 1 0 (0 : F))) (.inl 0)
  have h₂ := congrFun (h _ (hm 0 1 (0 : F))) (.inl 0)
  simp [pointRadicalElement, pointRadicalMatrix, mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_two] at h₀ h₁ h₂
  exact (mem_point_iff v).mpr ⟨h₂, by intro i; fin_cases i <;> assumption⟩

omit [CharP F 2] in
/-- The plane radical fixes only its distinguished plane in the natural module. -/
theorem plane_radical_fixed (v : Vector F)
    (h : ∀ q ∈ planeRadicalAmbient (F := F), q • v = v) : v ∈ plane F := by
  intro i
  let B : Plane.symmetricMatrices F :=
    ⟨Matrix.diagonal (Pi.single i 1), Matrix.isSymm_diagonal _⟩
  have hm : (Plane.shear B).val ∈ planeRadicalAmbient :=
    mem_map_of_mem planeLocal.subtype
      (show Plane.shear B ∈ Plane.radical from Plane.quotientMap_shear B)
  have hi := congrFun (h _ hm) (.inl i)
  fin_cases i <;>
    simpa [smul_eq_mulVec, Plane.shear, Plane.shearSp, B, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, diagonal, Pi.single_apply] using hi

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


/-- A cubic normalizer element moves every nonzero natural vector fixed by
the point-local two-core and acts trivially on the local two-core quotient. -/
theorem point_cubic_moves_fixed (hF : Nat.card F = 4) (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ q ∈ (pointLocal (F := F)).pCoreIn 2, q • v = v) :
    ∃ x : Sp F, orderOf x = 3 ∧ x ∈ normalizer (pointLocal (F := F) : Set (Sp F)) ∧
      (∀ (b : Sp F) (_ : b ∈ pointLocal), ⁅x,b⁆ ∈ pointLocal.pCoreIn 2) ∧ x • v ≠ v := by
  have hcore : (pointLocal (F := F)).pCoreIn 2 = pointRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [pointLocal_core_eq (n := 2) hF (by decide)]
  have hvp : v ∈ point F := point_radical_fixed v (by rwa [hcore] at hfix)
  obtain ⟨s, hs⟩ := scalar_exists hF
  have hN : pointParabolic (F := F) ≤ normalizer (pointLocal (F := F) : Set (Sp F)) :=
    (DiagramAutomorphisms.pointLocal_normalizer (n := 2) hF (by decide)).ge
  obtain ⟨hn,hc⟩ := local_core_commutator pointParabolic pointLocal pointLocal_le hN
    (RootCoreTori.point_scalar_mem_coreCenter (n := 2) hF (by decide) s)
  refine ⟨diagonalTorus s 1, ?_, hn, hc, ?_⟩
  · exact (orderOf_injective (RootTori.parameter 0) (RootTori.parameter_injective 0) s).trans hs
  · exact scalar_moves (fun he => by simp [he] at hs) hv (point_scalar_action s v hvp)

/-- The plane scalar moves every nonzero natural vector fixed by the plane
radical, while acting trivially on the plane-local two-core quotient. -/
theorem plane_cubic_moves_fixed (hF : Nat.card F = 4) (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ q ∈ (planeLocal (F := F)).pCoreIn 2, q • v = v) :
    ∃ x : Sp F, orderOf x = 3 ∧ x ∈ normalizer (planeLocal (F := F) : Set (Sp F)) ∧
      (∀ (b : Sp F) (_ : b ∈ planeLocal), ⁅x,b⁆ ∈ planeLocal.pCoreIn 2) ∧ x • v ≠ v := by
  have hcore : (planeLocal (F := F)).pCoreIn 2 = planeRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [planeLocal_core_eq (n := 2) hF (by decide)]
  have hvp : v ∈ plane F := plane_radical_fixed v (by rwa [hcore] at hfix)
  obtain ⟨s, hs⟩ := scalar_exists hF
  have hN : planeParabolic (F := F) ≤ normalizer (planeLocal (F := F) : Set (Sp F)) :=
    (DiagramAutomorphisms.planeLocal_normalizer (n := 2) hF (by decide)).ge
  obtain ⟨hn,hc⟩ := local_core_commutator planeParabolic planeLocal planeLocal_le hN
    (RootCoreTori.plane_scalar_mem_coreCenter (n := 2) hF (by decide) s)
  refine ⟨diagonalTorus s s, ?_, hn, hc, ?_⟩
  · exact (orderOf_injective planeScalar planeScalar_injective s).trans hs
  · exact scalar_moves (fun he => by simp [he] at hs) hv (plane_scalar_action s v hvp)

end Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
