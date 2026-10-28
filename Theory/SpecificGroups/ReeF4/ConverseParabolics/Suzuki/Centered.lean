module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.SuzukiRadical
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity
public import Theory.GroupTheory.CentralCoverCenteredModules
-- The Suzuki extension reuses the internal solvable-supplement argument
-- from the corresponding linear parabolic calculation.
import all Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity

/-!
# Centered modules in the full Suzuki-side Ree parabolic

A perfect nonsolvable normal subgroup has full image in the simple Suzuki
coordinate. The two-group kernel and solvable-supplement argument identify
it with the original perfect seed. The radical-center calculation then
rules out every nontrivial centered commutator module in a central cover.
All seed inclusions, full parabolic tori and central kernels are retained.

Source: Aschbacher--Smith 4.4.12 and F.1.12(I)(5), printed pp.621--622
and 263--264.
-/

public noncomputable section
open Subgroup
namespace ReeF4.ConverseParabolics.CoreActionRigidity
open LargeLocalSeeds BenderSuzuki.MatrixGroups

/-- The original fixed Suzuki seed inside its full parabolic. -/
def suzukiSeed (m : ℕ) : Subgroup (parabolic m .suzuki) :=
  (seedInclusion m .suzuki).range

def suzukiSeedEquiv (m : ℕ) :
    standardSeed (canonicalLocalBlockInput m) .suzuki ≃* suzukiSeed m :=
  MonoidHom.ofInjective (seedInclusion_injective m .suzuki)

theorem suzukiSeed_eq_subgroupOf (m : ℕ) :
    suzukiSeed m = (Parabolics.seed m .suzuki).subgroupOf (parabolic m .suzuki) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact (Parabolics.seedEquiv m .suzuki y).property
  · intro hx
    obtain ⟨y,hy⟩ := (Parabolics.seedEquiv m .suzuki).surjective ⟨x.val,hx⟩
    have he : (canonicalLocalBlockInput m).modelEquiv y.val = x.val :=
      congrArg (fun z : Parabolics.seed m .suzuki => (z : Model m)) hy
    exact ⟨y,Subtype.ext he⟩

theorem suzukiSeed_normal (m : ℕ) : (suzukiSeed m).Normal := by
  rw [suzukiSeed_eq_subgroupOf,
    MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic]
  exact Parabolics.seed_normal m .suzuki

theorem suzukiSeed_perfect {m : ℕ} (hm : 1 ≤ m) : Group.IsPerfect (suzukiSeed m) := by
  let := Parabolics.OuterLocal.suzukiSeed_perfect hm
  exact Group.IsPerfect.ofSurjective (suzukiSeedEquiv m).surjective

private theorem suzukiSeed_not_solvable {m : ℕ} (hm : 1 ≤ m) :
    ¬ Group.IsSolvable (suzukiSeed m) := by
  intro hh
  let := hh
  let := Group.isSolvable_of_isSolvable_injective (suzukiSeedEquiv m).injective
  exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
    (Group.isSolvable_of_surjective
      (SuzukiLeviProjection.projection_surjective (canonicalLocalBlockInput m)))

/-- A perfect nonsolvable normal subgroup has the full simple Suzuki image. -/
private theorem suzuki_simple_image_eq_top {m : ℕ} (hm : 1 ≤ m)
    (B : Subgroup (parabolic m .suzuki)) [B.Normal] [Group.IsPerfect B]
    (hn : ¬ Group.IsSolvable B) :
    B.map ((MonoidHom.fst _ _).comp (suzukiProjection hm)) = ⊤ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let f := suzukiProjection hm
  let g := (MonoidHom.fst _ _).comp f
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,hx⟩ := suzukiProjection_surjective hm (y,1)
    exact ⟨x,congrArg Prod.fst hx⟩
  let : (B.map g).Normal := Normal.map inferInstance g hg
  rcases (inferInstance : (B.map g).Normal).eq_bot_or_eq_top with hz | ht
  · exfalso
    have hB : B ≤ f.ker := by
      intro b hb
      have h1 : (f b).1 = 1 := mem_bot.mp (hz ▸ mem_map_of_mem g hb)
      have h2 : (f b).2 = 1 := Abelianization.commutator_subset_ker
        (((MonoidHom.snd _ _).comp f).comp B.subtype)
        (show (⟨b,hb⟩ : B) ∈ _root_.commutator B from Group.IsPerfect.mem_commutator)
      exact Prod.ext h1 h2
    let : Group.IsNilpotent f.ker := (suzukiProjection_ker_isPGroup hm).isNilpotent
    exact hn (Group.isSolvable_of_isSolvable_injective (inclusion_injective hB))
  · exact ht

/-- The full parabolic has only one perfect nonsolvable normal subgroup:
the actual seed, retaining its original inclusion. -/
theorem suzuki_perfect_normal_eq_seed {m : ℕ} (hm : 1 ≤ m)
    (B : Subgroup (parabolic m .suzuki)) [B.Normal] [Group.IsPerfect B]
    (hn : ¬ Group.IsSolvable B) : B = suzukiSeed m := by
  let := suzukiSeed_normal m
  let := suzukiSeed_perfect hm
  let := Parabolics.OuterLocal.suzukiQuotient_perfect m hm
  let f := suzukiProjection hm
  let : Group.IsNilpotent f.ker := (suzukiProjection_ker_isPGroup hm).isNilpotent
  have hB := product_lift_of_perfect_image f B (suzuki_simple_image_eq_top hm B hn)
  have hK := product_lift_of_perfect_image f (suzukiSeed m)
    (suzuki_simple_image_eq_top hm _ (suzukiSeed_not_solvable hm))
  exact le_antisymm
    (perfect_le_subnormal_of_le_sup_solvable B (suzukiSeed m) f.ker
      (Normal.isSubnormal inferInstance) (perfect_le_sup_kernel f B (suzukiSeed m) hK))
    (perfect_le_subnormal_of_le_sup_solvable (suzukiSeed m) B f.ker
      (Normal.isSubnormal inferInstance) (perfect_le_sup_kernel f (suzukiSeed m) B hB))

/-- A central cover of a perfect nonsolvable normal subgroup of the full
Suzuki parabolic has no nontrivial centered commutator module. -/
theorem suzuki_no_centered_commutator {m : ℕ} (hm : 1 ≤ m)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (hn : ¬ Group.IsSolvable A)
    (f : A →* parabolic m .suzuki) (hker : f.ker ≤ center A) [f.range.Normal]
    (W : Subgroup A) (hW : W ≤ centralizer (pCore 2 A : Set A))
    (hcomm : W = ⁅W,⊤⁆) : W = ⊥ := by
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  have hnsol : ¬ Group.IsSolvable f.range := by
    intro hh
    let := hh
    let : CommGroup (center A) := IsMulCommutative.instCommGroup
    let : Group.IsSolvable f.ker :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hker)
    exact hn (Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict,range_subtype]))
  have hr := suzuki_perfect_normal_eq_seed hm f.range hnsol
  let a := suzukiSeedEquiv m
  let k := f.codRestrict (suzukiSeed m) (fun x => hr ▸ (show f x ∈ f.range from ⟨x,rfl⟩))
  let q := a.symm.toMonoidHom.comp k
  have hk : Function.Surjective k := by
    rintro ⟨x,hx⟩
    obtain ⟨y,hy⟩ := (show x ∈ f.range from hr.symm ▸ hx)
    exact ⟨y,Subtype.ext hy⟩
  have hq : Function.Surjective q := a.symm.surjective.comp hk
  have hqker : q.ker ≤ center A := by
    intro x hx
    apply hker
    have he : k x = 1 := a.symm.injective (hx.trans a.symm.map_one.symm)
    exact congrArg Subtype.val he
  exact centered_commutator_eq_bot_of_central_cover q hq hqker
    (NormalizedRootCentralizers.CenterExponent.suzuki_seed_core_centralizer_le_center hm)
    W hW hcomm
end ReeF4.ConverseParabolics.CoreActionRigidity
