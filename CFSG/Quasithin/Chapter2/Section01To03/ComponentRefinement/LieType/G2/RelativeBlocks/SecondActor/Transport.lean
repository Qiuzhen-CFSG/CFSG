module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.Sections
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry
public import Theory.AtlasPort.LinearGroups.G2.BinaryException
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Transport for second-parabolic actor rigidity

Coefficientwise field transport preserves the distinguished singular line,
its stabilizer, and the derived subgroup. It therefore identifies the actual
second parabolics inside the derived G₂ models. Over a two-element field this
gives the existing binary derived parabolic; above order two, perfectness of
G₂ identifies the restriction with the full parabolic.

Multiplicative equivalences preserve subnormality, two-perfection, and the
square condition on the intrinsic two-core. The reduction explicitly transports
the whole actor subgroup and the whole core.

Source: the second-parabolic case in Aschbacher–Smith 2.3.9(7), printed p.526.
The octonion coefficient transport is from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.SplitOctonion Atlas.G2.LieParabolicSetup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor

/-- Transport the square condition on the actual ambient two-core. -/
theorem square_condition_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (X : Subgroup G)
    (hsq : ∀ q ∈ pCore 2 G, ∀ x ∈ X, (⁅q,x⁆ : G)^2 = 1) :
    ∀ q ∈ pCore 2 H, ∀ x ∈ X.map e.toMonoidHom, (⁅q,x⁆ : H)^2 = 1 := by
  intro q hq x hx
  rw [← pCore_map_iso 2 e] at hq
  obtain ⟨q,hq,rfl⟩ := hq
  obtain ⟨x,hx,rfl⟩ := hx
  simpa only [map_pow, map_commutatorElement, map_one] using congrArg e.toMonoidHom (hsq q hq x hx)

/-- Actor rigidity transfers along an actual group equivalence. -/
theorem eq_bot_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hrigid : ∀ Y : Subgroup H, Y.IsSubnormal → IsPPerfect 2 Y →
      (∀ q ∈ pCore 2 H, ∀ x ∈ Y, (⁅q,x⁆ : H)^2 = 1) → Y = ⊥)
    (X : Subgroup G) (hX : X.IsSubnormal) (hp : IsPPerfect 2 X)
    (hsq : ∀ q ∈ pCore 2 G, ∀ x ∈ X, (⁅q,x⁆ : G)^2 = 1) : X = ⊥ := by
  have hm : X.map e.toMonoidHom = ⊥ := hrigid _ (hX.map e.surjective)
    (hp.of_surjective (e.toMonoidHom.subgroupMap X) (e.toMonoidHom.subgroupMap_surjective X))
    (square_condition_map e X hsq)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [Subgroup.map_bot] using hm

private lemma map_first_basis {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) : mapCoefficients e (basisVector 0) = basisVector 0 := by
  funext i
  simp [mapCoefficients, basisVector, Pi.single_apply, apply_ite e]

private theorem field_parabolic_mem {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) {g : Model F} (hg : g ∈ parabolic₂) : fieldEquiv e g ∈ parabolic₂ := by
  change g ∈ parabolic at hg
  rw [parabolic_eq_pointStabilizer, mem_pointStabilizer_iff] at hg
  change fieldEquiv e g ∈ parabolic
  rw [parabolic_eq_pointStabilizer, mem_pointStabilizer_iff]
  obtain ⟨a,ha⟩ := hg
  refine ⟨Units.map e.toRingHom.toMonoidHom a, ?_⟩
  rw [← map_first_basis e, fieldEquiv_action, ha]
  simp [Units.smul_def]

private theorem field_commutator_mem {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) {g : Model F} (hg : g ∈ commutator (Model F)) :
    fieldEquiv e g ∈ commutator (Model K) := by
  have he : (commutator (Model F)).map (fieldEquiv e).toMonoidHom =
      commutator (Model K) := by
    rw [map_commutator_eq, (fieldEquiv e).toMonoidHom.range_eq_top_of_surjective
      (fieldEquiv e).surjective]
    rfl
  rw [← he]
  exact mem_map_of_mem _ hg

/-- Coefficientwise equivalence of the parabolics inside the derived groups. -/
def secondModelFieldEquiv {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) : secondModel F ≃* secondModel K where
  toFun x := ⟨⟨fieldEquiv e x.val.val, by exact field_commutator_mem e x.val.property⟩,
    by exact field_parabolic_mem e x.property⟩
  invFun x := ⟨⟨fieldEquiv e.symm x.val.val, by exact field_commutator_mem e.symm x.val.property⟩,
    by exact field_parabolic_mem e.symm x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (fieldEquiv e).symm_apply_apply x.val.val
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (fieldEquiv e).apply_symm_apply x.val.val
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (fieldEquiv e) x.val.val y.val.val

/-- Every two-element field gives the existing second parabolic of G₂(2)′. -/
noncomputable def secondModelBinaryEquiv {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : secondModel F ≃* BinaryParabolicPair.derivedSecond :=
  secondModelFieldEquiv (binaryFieldEquiv hF)

/-- Above order two the derived-model restriction is the full parabolic. -/
noncomputable def secondModelFullEquiv {F : Type*} [Field F] [Finite F]
    (hF : 2 < Nat.card F) : secondModel F ≃* parabolic₂ (F := F) := by
  let := Atlas.G2.isPerfect (F := F) hF
  exact {
    toFun := fun x => ⟨x.val.val, x.property⟩
    invFun := fun x => ⟨⟨x.val, Group.IsPerfect.mem_commutator⟩, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor

end
