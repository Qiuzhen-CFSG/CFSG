module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Centerless subgroups under a homomorphism with central kernel

A central kernel intersects a subgroup in its center. Consequently the
restriction to a centerless subgroup is injective, and identifies it with
its actual image. No injectivity on the whole ambient group is required.

This is the elementary central-cover restriction used for the A₅ subgroup
in Aschbacher–Smith 16.1.7(3f) and 16.3.5, printed pp.1172 and 1178–1179
of the combined manuscript of 1 March 2004.
-/

public section
namespace MonoidHom
open Subgroup
variable {X Y : Type*} [Group X] [Group Y]

/-- A homomorphism with central kernel is injective on every centerless subgroup. -/
theorem subgroupMap_injective_of_ker_le_center (f : X →* Y)
    (hk : f.ker ≤ center X) (P : Subgroup X) (hc : center P = ⊥) :
    Function.Injective (f.subgroupMap P) := by
  apply (f.subgroupMap P).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxk : (x : X) ∈ f.ker :=
    congrArg Subtype.val (show f.subgroupMap P x = 1 from hx)
  have hxc : x ∈ center P := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (hk hxk) y
  simpa only [hc, mem_bot] using hxc

/-- The restriction identifies a centerless subgroup with its actual image. -/
noncomputable def subgroupMapEquivOfKerLeCenter (f : X →* Y)
    (hk : f.ker ≤ center X) (P : Subgroup X) (hc : center P = ⊥) : P ≃* P.map f :=
  MulEquiv.ofBijective (f.subgroupMap P)
    ⟨f.subgroupMap_injective_of_ker_le_center hk P hc, f.subgroupMap_surjective P⟩

end MonoidHom
