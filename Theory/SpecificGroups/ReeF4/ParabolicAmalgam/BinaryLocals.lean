module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.Radicals
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.TargetCores
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry

/-!
# Binary Ree local quotients and Sylow geometry

For the full fixed group ²F₄(2), the two root-defined seeds are the parabolics.
Their root radicals are two-groups, and the actual targets Sz(2) and PSL₂(2)
have trivial two-cores. The constructed surjective projections have exactly
these root kernels, so the kernels are O₂. The induced quotient isomorphisms
retain the formulas on representatives. The conditional projection lemmas are
preserved, and the unconditional results below discharge all their inputs.

Fixed-point Bruhat factorization proves odd index of the positive subgroup and
generation by the two seeds. Together with the positive two-group theorem,
this gives a Sylow two-subgroup whose underlying subgroup is exactly the
specified positive subgroup. Normality of each radical is relative to its seed;
the ambient group is the full `Model 0`. Radical cardinalities and the remaining
source amalgam clauses are separate from these local quotient and geometry facts.

Source: Aschbacher–Smith F.1.12(I)(5) and its q=2 discussion, printed
pp.263–264 of `refs/quasithin.pdf`. The Tits case F.1.12(I)(9) has a different
Suzuki-side quotient and a different linear radical order.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.Binary
open LargeLocalSeeds Subgroup BenderSuzuki.MatrixGroups

/-- An exact binary Suzuki projection identifies the intrinsic two-core. -/
theorem suzuki_radical_eq_pCore_of_projection
    (π : seed 0 .suzuki →* SuzukiMatrixGroup 0)
    (hπ : Function.Surjective π) (hker : π.ker = radicalInSeed 0 .suzuki) :
    radicalInSeed 0 .suzuki = pCore 2 (seed 0 .suzuki) := by
  have hP : IsPGroup 2 π.ker := hker ▸ radicalInSeed_isPGroup 0 .suzuki
  have h := π.comap_pCore_of_ker_isPGroup hπ hP
  simpa only [suzuki_twoCore_eq_bot, MonoidHom.comap_bot, hker] using h

/-- An exact binary linear projection identifies the intrinsic two-core. -/
theorem linear_radical_eq_pCore_of_projection
    (π : seed 0 .linear →* LinearQuotient 0)
    (hπ : Function.Surjective π) (hker : π.ker = radicalInSeed 0 .linear) :
    radicalInSeed 0 .linear = pCore 2 (seed 0 .linear) := by
  have hP : IsPGroup 2 π.ker := hker ▸ radicalInSeed_isPGroup 0 .linear
  have h := π.comap_pCore_of_ker_isPGroup hπ hP
  simpa only [linear_twoCore_eq_bot, MonoidHom.comap_bot, hker] using h

/-- The quotient equivalence induced by the binary Suzuki projection. -/
def suzukiCoreQuotientEquivOfProjection
    (π : seed 0 .suzuki →* SuzukiMatrixGroup 0)
    (hπ : Function.Surjective π) (hker : π.ker = radicalInSeed 0 .suzuki) :
    (seed 0 .suzuki ⧸ pCore 2 (seed 0 .suzuki)) ≃* SuzukiMatrixGroup 0 :=
  (QuotientGroup.quotientMulEquivOfEq
    ((suzuki_radical_eq_pCore_of_projection π hπ hker).symm.trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)

@[simp] theorem suzukiCoreQuotientEquivOfProjection_mk
    (π : seed 0 .suzuki →* SuzukiMatrixGroup 0)
    (hπ : Function.Surjective π) (hker : π.ker = radicalInSeed 0 .suzuki)
    (x : seed 0 .suzuki) :
    suzukiCoreQuotientEquivOfProjection π hπ hker
      (QuotientGroup.mk' (pCore 2 (seed 0 .suzuki)) x) = π x := rfl

/-- The quotient equivalence induced by the binary linear projection. -/
def linearCoreQuotientEquivOfProjection
    (π : seed 0 .linear →* LinearQuotient 0)
    (hπ : Function.Surjective π) (hker : π.ker = radicalInSeed 0 .linear) :
    (seed 0 .linear ⧸ pCore 2 (seed 0 .linear)) ≃* LinearQuotient 0 :=
  (QuotientGroup.quotientMulEquivOfEq
    ((linear_radical_eq_pCore_of_projection π hπ hker).symm.trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)

@[simp] theorem linearCoreQuotientEquivOfProjection_mk
    (π : seed 0 .linear →* LinearQuotient 0)
    (hπ : Function.Surjective π) (hker : π.ker = radicalInSeed 0 .linear)
    (x : seed 0 .linear) :
    linearCoreQuotientEquivOfProjection π hπ hker
      (QuotientGroup.mk' (pCore 2 (seed 0 .linear)) x) = π x := rfl

/-- The specified Suzuki root radical is the intrinsic two-core of its seed. -/
theorem suzuki_radical_eq_pCore :
    radicalInSeed 0 .suzuki = pCore 2 (seed 0 .suzuki) :=
  suzuki_radical_eq_pCore_of_projection BinarySuzuki.projection
    BinarySuzuki.projection_surjective BinarySuzuki.projection_ker

/-- The specified linear root radical is the intrinsic two-core of its seed. -/
theorem linear_radical_eq_pCore :
    radicalInSeed 0 .linear = pCore 2 (seed 0 .linear) :=
  linear_radical_eq_pCore_of_projection BinaryLinear.projection
    BinaryLinear.projection_surjective BinaryLinear.projection_ker

/-- Both binary root radicals agree with the intrinsic relative two-cores. -/
theorem radicalInSeed_eq_pCore (s : Side) :
    radicalInSeed 0 s = pCore 2 (seed 0 s) := by
  cases s
  · exact suzuki_radical_eq_pCore
  · exact linear_radical_eq_pCore

/-- Normality is inside the containing seed, not in the ambient fixed group. -/
theorem radicalInSeed_normal (s : Side) : (radicalInSeed 0 s).Normal := by
  rw [radicalInSeed_eq_pCore]
  infer_instance

/-- Embedding either local two-core in the full group gives its root radical. -/
theorem pCore_map_seed_subtype (s : Side) :
    (pCore 2 (seed 0 s)).map (seed 0 s).subtype = radical 0 s := by
  rw [← radicalInSeed_eq_pCore]
  exact radicalInSeed_map 0 s

/-- The actual Suzuki projection has the intrinsic two-core as its kernel. -/
theorem suzuki_projection_ker_pCore :
    BinarySuzuki.projection.ker = pCore 2 (seed 0 .suzuki) :=
  BinarySuzuki.projection_ker.trans suzuki_radical_eq_pCore

/-- The actual linear projection has the intrinsic two-core as its kernel. -/
theorem linear_projection_ker_pCore :
    BinaryLinear.projection.ker = pCore 2 (seed 0 .linear) :=
  BinaryLinear.projection_ker.trans linear_radical_eq_pCore

/-- The Suzuki local quotient in the full binary Ree group is the actual Sz(2). -/
def suzukiCoreQuotientEquiv :
    (seed 0 .suzuki ⧸ pCore 2 (seed 0 .suzuki)) ≃* SuzukiMatrixGroup 0 :=
  suzukiCoreQuotientEquivOfProjection BinarySuzuki.projection
    BinarySuzuki.projection_surjective BinarySuzuki.projection_ker

@[simp] theorem suzukiCoreQuotientEquiv_mk (x : seed 0 .suzuki) :
    suzukiCoreQuotientEquiv (QuotientGroup.mk' (pCore 2 (seed 0 .suzuki)) x) =
      BinarySuzuki.projection x := rfl

/-- The linear local quotient is PSL₂ over the exact binary Ree coefficient field. -/
def linearCoreQuotientEquiv :
    (seed 0 .linear ⧸ pCore 2 (seed 0 .linear)) ≃* LinearQuotient 0 :=
  linearCoreQuotientEquivOfProjection BinaryLinear.projection
    BinaryLinear.projection_surjective BinaryLinear.projection_ker

@[simp] theorem linearCoreQuotientEquiv_mk (x : seed 0 .linear) :
    linearCoreQuotientEquiv (QuotientGroup.mk' (pCore 2 (seed 0 .linear)) x) =
      BinaryLinear.projection x := rfl

/-- The positive fixed subgroup has odd index in the full binary Ree group. -/
theorem unipotent_index_odd : Odd (unipotent 0).index :=
  FixedGeometry.unipotent_index_odd

/-- The Sylow witness with exactly the root-defined positive subgroup. -/
def sylow : Sylow 2 (Model 0) := sylowOfOddIndex 0 unipotent_index_odd

@[simp] theorem sylow_coe : (sylow : Subgroup (Model 0)) = unipotent 0 := rfl

/-- The two fixed root seeds generate the full binary Ree group. -/
theorem seed_sup_eq_top : seed 0 .suzuki ⊔ seed 0 .linear = ⊤ :=
  FixedGeometry.seed_sup_eq_top

/-- Equivalently, the two binary parabolics generate the full fixed group. -/
theorem parabolic_sup_eq_top : parabolic 0 .suzuki ⊔ parabolic 0 .linear = ⊤ := by
  simpa only [parabolic_zero] using seed_sup_eq_top

end ReeF4.Parabolics.Binary
