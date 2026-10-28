module

public import Theory.Representation.G2OrthogonalCover
public import Theory.Representation.FirstCohomologyG2Natural
public import Theory.Representation.FirstCohomologyG2Natural.BinaryBound
public import Theory.Representation.FirstCohomologyG2Natural.NonbinaryBound

/-!
# The trace-zero model is the universal binary G₂′ cover

The norm polar pairing descends nondegenerately to the natural six-space.
Composing it with a binary functional on the coefficient field taking 1 to 1
produces a nondegenerate invariant binary pairing: field rescaling detects
any nonzero paired value. Thus the actual binary natural module is self-dual.
The proved binary and nonbinary cocycle bounds give the required dual H¹
kernel dimension. Cover duality then supplies an equivariant isomorphism
from the universal binary cover to the trace-zero space, commuting with the
literal natural quotient projection, and compatible quotients to every cover.

Source: Aschbacher–Smith, I.2.3(1), printed p.413 / PDF p.424, using I.1.5–6.
No ambient G-action extending the derived L-action is asserted here.
-/

@[expose] public section
noncomputable section
open Atlas.SplitOctonion Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover
variable (K : Type*) [Field K] [CharP K 2]

/-- The norm polar form induced on the literal trace-zero quotient. -/
def naturalPairing : Space K →ₗ[K] Space K →ₗ[K] K :=
  (form K).polarBilin.liftQ₂ (scalarLine K) (scalarLine K)
    (by rw [polar_ker]) (by
      intro x hx
      apply LinearMap.ext
      intro y
      change (form K).polarBilin y x = 0
      rw [polar_apply, normPolar_symm, ← polar_apply]
      exact LinearMap.congr_fun (show (form K).polarBilin x = 0 from (show x ∈ (form K).polarBilin.ker from (polar_ker K).symm ▸ hx)) y)

@[simp] theorem naturalPairing_mk (x y : TraceZero K) :
    naturalPairing K (mk K x) (mk K y) = normPolar x.val y.val := polar_apply K x y

/-- The induced natural pairing has zero radical. -/
theorem naturalPairing_injective : Function.Injective (naturalPairing K) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨x, rfl⟩ := mk_surjective K v
  apply (mk_eq_zero_iff K x).mpr
  apply (orthogonal_traceZero_iff K x.val).mp
  intro y
  simpa only [naturalPairing_mk, LinearMap.zero_apply] using
    LinearMap.congr_fun hv (mk K y)

theorem naturalPairing_invariant (g : commutator (Model K)) (v w : Space K) :
    naturalPairing K (derivedAction K g v) (derivedAction K g w) = naturalPairing K v w := by
  obtain ⟨x, rfl⟩ := mk_surjective K v
  obtain ⟨y, rfl⟩ := mk_surjective K w
  simp only [derivedAction_mk, naturalPairing_mk, traceZeroAction_val, automorphism_normPolar]

variable [Algebra (ZMod 2) K]

/-- A binary functional on the coefficient field normalized at 1. -/
def coefficient : K →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : K) ≠ 0))

omit [CharP K 2] in
@[simp] theorem coefficient_one : coefficient K 1 = 1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : K) ≠ 0))

/-- The invariant binary pairing obtained from the natural field pairing. -/
def binaryPairing : Space K →ₗ[ZMod 2] Space K →ₗ[ZMod 2] ZMod 2 :=
  ((naturalPairing K).restrictScalars₁₂ (ZMod 2) (ZMod 2)).compr₂ (coefficient K)

@[simp] theorem binaryPairing_apply (v w : Space K) :
    binaryPairing K v w = coefficient K (naturalPairing K v w) := rfl

/-- Field rescaling proves nondegeneracy after scalar restriction. -/
theorem binaryPairing_injective : Function.Injective (binaryPairing K) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  apply naturalPairing_injective K
  rw [map_zero]
  apply LinearMap.ext
  intro w
  change naturalPairing K v w = 0
  by_contra hn
  have h := LinearMap.congr_fun hv ((naturalPairing K v w)⁻¹ • w)
  change coefficient K (naturalPairing K v ((naturalPairing K v w)⁻¹ • w)) = 0 at h
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hn, coefficient_one] at h
  exact one_ne_zero h

/-- The genuine derived natural action over the binary prime field. -/
def binaryNatural : Representation (ZMod 2) (commutator (Model K)) (Space K) :=
  restrictScalars (k := ZMod 2) (derivedAction K)

/-- The trace-zero orthogonal action over the binary prime field. -/
def binaryAction : Representation (ZMod 2) (commutator (Model K)) (TraceZero K) :=
  restrictScalars (k := ZMod 2) (action K)

/-- The literal quotient projection with scalars restricted to F₂. -/
def binaryProjection : (binaryAction K).IntertwiningMap (binaryNatural K) :=
  restrictCoverMap (k := ZMod 2) (projection K)

theorem binaryProjection_isCover : IsCover (binaryProjection K) :=
  isCover_restrictScalars (projection K) (projection_isCover K)

variable [Finite K]

/-- Self-duality of the actual binary natural representation, including G₂(2)′. -/
def binarySelfDual : Space K ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Space K) :=
  LinearEquiv.ofBijective (binaryPairing K)
    ⟨binaryPairing_injective K,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        Subspace.dual_finrank_eq.symm).mp (binaryPairing_injective K)⟩

theorem binarySelfDual_equivariant (g : commutator (Model K)) (v : Space K) :
    binarySelfDual K (binaryNatural K g v) = (binaryNatural K).dual g (binarySelfDual K v) := by
  apply LinearMap.ext
  intro w
  change coefficient K (naturalPairing K (derivedAction K g v) w) =
    coefficient K (naturalPairing K v (derivedAction K g⁻¹ w))
  congr 1
  have h := naturalPairing_invariant K g v (derivedAction K g⁻¹ w)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h

omit [Algebra (ZMod 2) K] in
/-- The two completed cocycle bounds give field cohomology dimension one. -/
theorem natural_H1_finrank : Module.finrank K (H1 (derivedAction K)) = 1 := by
  apply finrank_H1_eq_one_of_finrank_cocycles_le
  by_cases h : Nat.card K = 2
  · exact finrank_cocycles_le_seven_binary K h
  · exact finrank_cocycles_le_seven_nonbinary K (by have hc := Finite.one_lt_card (α := K); omega)

/-- The dual binary cohomology has dimension equal to the field degree. -/
theorem binary_dual_H1_finrank :
    Module.finrank (ZMod 2) (H1 (binaryNatural K).dual) = Module.finrank (ZMod 2) K := by
  let e := H1Congr (binaryNatural K) (binaryNatural K).dual
    (MulEquiv.refl _) (binarySelfDual K) (binarySelfDual_equivariant K)
  rw [← e.finrank_eq]
  change Module.finrank (ZMod 2) (H1 (restrictScalars (k := ZMod 2) (derivedAction K))) = _
  rw [finrank_restrictScalars, natural_H1_finrank, mul_one]

/-- The kernel of the literal binary projection has the expected field degree. -/
theorem binaryProjection_kernel_finrank :
    Module.finrank (ZMod 2) (binaryProjection K).toLinearMap.ker =
      Module.finrank (ZMod 2) K := by
  have h := (binaryProjection K).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (binaryProjection_isCover K).1, finrank_top] at h
  rw [← Module.finrank_mul_finrank (ZMod 2) K (Space K),
    ← Module.finrank_mul_finrank (ZMod 2) K (TraceZero K),
    finrank_space, finrank_traceZero] at h
  omega

/-- The universal binary cover is the trace-zero seven-space, compatibly with projection. -/
theorem universal_equiv :
    ∃ e : Module.Dual (ZMod 2) (cocycles (binaryNatural K).dual) ≃ₗ[ZMod 2] TraceZero K,
      (∀ g u, e ((universalAction (binaryNatural K).dual).dual g u) = binaryAction K g (e u)) ∧
      ∀ u, binaryProjection K (e u) = universalCoverProjection (binaryNatural K) u := by
  apply exists_equiv_universalCover_of_finrank_ker_eq
    (binaryProjection K) (binaryProjection_isCover K)
  rw [binaryProjection_kernel_finrank, binary_dual_H1_finrank]

/-- Every binary cover is a quotient of the orthogonal model over the original natural projection. -/
theorem exists_quotient {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (commutator (Model K)) W}
    (p : σ.IntertwiningMap (binaryNatural K)) (hp : IsCover p) :
    ∃ f : (binaryAction K).IntertwiningMap σ, Function.Surjective f ∧
      ∀ w, p (f w) = mk K w := by
  exact exists_quotient_of_finrank_ker_eq (binaryProjection K) (binaryProjection_isCover K)
    (by rw [binaryProjection_kernel_finrank, binary_dual_H1_finrank]) p hp

end Atlas.G2.Natural.OrthogonalCover
