module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.Sections
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RootObstructions
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import Theory.GroupTheory.Commutator.PerfectSolvableSupplement
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The long-local part of the second G₂ actor argument

Above field order two, a subnormal subgroup of the long local group maps
trivially or surjectively onto its simple SL₂ quotient. In the surjective
case its solvable radical is a supplement. The subnormal supplement theorem
and perfectness then force the subgroup to be the whole local group, where
the long-Weyl commutator has nonidentity square. Thus a subgroup satisfying
the square condition lies in the two-core; if it is two-perfect, it is trivial.

This also controls the intersection of a square-trivial subnormal subgroup
of the full parabolic with the long local group. It does not dispose of the
remaining torus action or the binary derived-group case.

Source: Aschbacher–Smith 2.3.9(7), printed p.526, using F.1.12(I)(3),(II).
The concrete root and quotient calculations are from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem longSL_simple (hq : 2 < Nat.card F) : IsSimpleGroup SL(2,F) := by
  have hfour : 4 ≤ Nat.card F := by
    obtain ⟨n, hn, he⟩ := field_card (F := F)
    have hn2 : 2 ≤ n := by
      by_contra hn2
      have hn1 : n = 1 := by omega
      simp [hn1] at he
      omega
    rw [he]
    change 2 ^ 2 ≤ 2 ^ n
    exact pow_le_pow_right₀ (by decide) hn2
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hfour
  exact (longSLEquivPSL (F := F)).isSimpleGroup

/-- The simple quotient and perfect local group eliminate every nontrivial quotient image. -/
theorem local_subnormal_square_le_core (hq : 2 < Nat.card F)
    (X : Subgroup (local₂ (F := F))) (hX : X.IsSubnormal)
    (hsq : ∀ q ∈ pCore 2 (local₂ (F := F)), ∀ x ∈ X, (⁅q,x⁆ : local₂)^2 = 1) :
    X ≤ pCore 2 (local₂ (F := F)) := by
  have hker : (longSLHom (F := F)).ker = pCore 2 (local₂ (F := F)) := by
    rw [longSLHom_ker, local₂_pCore]
  rcases (hX.map longSLHom_surjective).eq_bot_or_top_of_isSimpleGroup
      (longSL_simple hq) with hb | ht
  · rw [← hker]
    exact X.map_eq_bot_iff.mp hb
  · have hsup : X ⊔ pCore 2 (local₂ (F := F)) = ⊤ := by
      rw [← hker, ← X.comap_map_eq longSLHom, ht, comap_top]
    let : Group.IsNilpotent (pCore 2 (local₂ (F := F))) := pCore_isPGroup.isNilpotent
    have htop : X = ⊤ := by
      apply top_unique
      rw [← local₂_solvableResidual_eq_top hq]
      exact hX.solvableResidual_le_of_sup_eq_top _ hsup
    let q : local₂ (F := F) := ⟨rootD 1,
      radical₂_le_local₂ ⟨![0,0,0,1,0,0],rfl,by simp [unipotentProduct]⟩⟩
    let w : local₂ (F := F) := ⟨weylR, mem_sup_right (subset_closure (by simp))⟩
    have hqcore : q ∈ pCore 2 (local₂ (F := F)) := by
      rw [local₂_pCore]
      exact ⟨![0,0,0,1,0,0],rfl,by simp [q, unipotentProduct]⟩
    have hwX : w ∈ X := by rw [htop]; trivial
    have he := congrArg (local₂ (F := F)).subtype (hsq q hqcore w hwX)
    change ⁅rootD (1 : F), weylR⁆ ^ 2 = 1 at he
    rw [long_root_commutator_square] at he
    exact (rootAB_one_ne_one he).elim

/-- Two-perfection eliminates the subgroup remaining inside the local two-core. -/
theorem local_actor_eq_bot (hq : 2 < Nat.card F)
    (X : Subgroup (local₂ (F := F))) (hX : X.IsSubnormal) (hp : IsPPerfect 2 X)
    (hsq : ∀ q ∈ pCore 2 (local₂ (F := F)), ∀ x ∈ X, (⁅q,x⁆ : local₂)^2 = 1) :
    X = ⊥ := by
  have hle := local_subnormal_square_le_core hq X hX hsq
  have hpX : IsPGroup 2 X := pCore_isPGroup.to_le hle
  have he := hp.hom_eq_one_of_isPGroup hpX (MonoidHom.id X)
  apply X.eq_bot_iff_forall.mpr
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x,hx⟩)
/-- Restriction from the full parabolic retains the actual local two-core. -/
theorem full_intersection_le_core (hq : 2 < Nat.card F)
    (X : Subgroup (parabolic₂ (F := F))) (hX : X.IsSubnormal)
    (hsq : ∀ q ∈ pCore 2 (parabolic₂ (F := F)), ∀ x ∈ X, (⁅q,x⁆ : parabolic₂)^2 = 1) :
    X.comap (Subgroup.inclusion local₂_le_parabolic₂) ≤ pCore 2 (local₂ (F := F)) := by
  let f : local₂ (F := F) →* parabolic₂ := Subgroup.inclusion local₂_le_parabolic₂
  apply local_subnormal_square_le_core hq _ (hX.comap f)
  intro q hq x hx
  have hq' : f q ∈ pCore 2 (parabolic₂ (F := F)) := by
    rw [Atlas.G2.EvenLocal.parabolic₂_pCore]
    rw [local₂_pCore] at hq
    exact hq
  apply (Subgroup.inclusion_injective local₂_le_parabolic₂)
  simpa only [map_pow, map_commutatorElement, map_one] using hsq (f q) hq' (f x) hx

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor

end
