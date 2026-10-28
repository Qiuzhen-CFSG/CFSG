module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.Covering
public import Theory.PGroupCore

/-!
# Prime-power multipliers and perfect central covers

A surjective morphism of central covers maps the first kernel onto the
second. Thus a p-group universal kernel makes the kernel of every finite
perfect central cover a p-group. If the source has trivial p-core, its
covering map is an isomorphism. The same argument is supplied for the
finite quasisimple covering API used by the multiplier tables.

This is the covering deduction needed in Aschbacher–Smith, B.1.13,
printed pp.73–74, from the even G₂ entries of I.1.3–I.1.4, pp.407–408.
The family-specific multiplier calculations are separate hypotheses;
in particular a nontrivial p-group multiplier is allowed.
-/

public section

open Subgroup
namespace PerfectCentralCovering
universe u v w
variable {U : Type u} {G : Type v} {L : Type w}
  [Group U] [Group G] [Group L]

/-- A surjective commuting triangle maps its upper kernel onto its lower kernel. -/
theorem kernel_isPGroup_of_surjective_triangle
    {p : ℕ} (f : L →* G) (g : U →* G) (a : U →* L)
    (ha : Function.Surjective a) (htriangle : f.comp a = g)
    (hp : IsPGroup p g.ker) : IsPGroup p f.ker := by
  let k : g.ker →* f.ker :=
    (a.comp g.ker.subtype).codRestrict f.ker (fun x => by
      change f (a x) = 1
      rw [← MonoidHom.comp_apply, htriangle]
      exact x.property)
  apply hp.of_surjective k
  intro x
  obtain ⟨y, hy⟩ := ha x
  have hgy : y ∈ g.ker := by
    change g y = 1
    rw [← htriangle, MonoidHom.comp_apply, hy]
    exact x.property
  exact ⟨⟨y, hgy⟩, Subtype.ext hy⟩

/-- A p-group universal multiplier controls every finite perfect central cover. -/
theorem Cover.ker_isPGroup_of_universal [Finite G] [Finite L]
    (f : Cover L G) (g : Cover U G) (hg : IsUniversal.{u, v, w} g)
    {p : ℕ} (hp : IsPGroup p g.toMonoidHom.ker) :
    IsPGroup p f.toMonoidHom.ker := by
  obtain ⟨a, ha, _⟩ := hg L f
  let : Group.IsPerfect L := f.isPerfect
  have hasurj := surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f.toMonoidHom a (ha ▸ g.surjective) f.ker_le_center
  exact kernel_isPGroup_of_surjective_triangle _ _ a hasurj ha hp

/-- Trivial p-core removes the entire kernel, including exceptional p-multipliers. -/
theorem Cover.injective_of_pCore_eq_bot_of_universal_pGroup [Finite G] [Finite L]
    (f : Cover L G) (g : Cover U G) (hg : IsUniversal.{u, v, w} g)
    {p : ℕ} (hp : IsPGroup p g.toMonoidHom.ker) (hc : pCore p L = ⊥) :
    Function.Injective f.toMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  rw [← hc]
  exact le_sSup ⟨inferInstance, f.ker_isPGroup_of_universal g hg hp⟩

/-- The isomorphism is the specified covering map, not a new abstract identification. -/
noncomputable def Cover.equivOfPCoreEqBotOfUniversalPGroup [Finite G] [Finite L]
    (f : Cover L G) (g : Cover U G) (hg : IsUniversal.{u, v, w} g)
    {p : ℕ} (hp : IsPGroup p g.toMonoidHom.ker) (hc : pCore p L = ⊥) : L ≃* G :=
  MulEquiv.ofBijective f.toMonoidHom
    ⟨f.injective_of_pCore_eq_bot_of_universal_pGroup g hg hp hc, f.surjective⟩

@[simp] theorem Cover.equivOfPCoreEqBotOfUniversalPGroup_apply [Finite G] [Finite L]
    (f : Cover L G) (g : Cover U G) (hg : IsUniversal.{u, v, w} g)
    {p : ℕ} (hp : IsPGroup p g.toMonoidHom.ker) (hc : pCore p L = ⊥) (x : L) :
    f.equivOfPCoreEqBotOfUniversalPGroup g hg hp hc x = f.toMonoidHom x := by
  unfold Cover.equivOfPCoreEqBotOfUniversalPGroup
  rfl

end PerfectCentralCovering

namespace Theory.GroupTheory.Covering
universe u v w
variable {U : Type u} {G : Type v} {L : Type w}
  [Group U] [Finite U] [IsQuasisimple U]
  [Group G] [Finite G] [IsQuasisimple G]
  [Group L] [Finite L] [IsQuasisimple L]

/-- The quasisimple universal-cover convention gives the same kernel conclusion. -/
theorem ker_isPGroup_of_universal (f : Covering L G) (g : Covering U G)
    (hg : IsUniversal.{v, u, w} g) {p : ℕ} (hp : IsPGroup p g.toMonoidHom.ker) :
    IsPGroup p f.toMonoidHom.ker := by
  obtain ⟨a, ha, _⟩ := hg L f
  exact PerfectCentralCovering.kernel_isPGroup_of_surjective_triangle
    f.toMonoidHom g.toMonoidHom a.toMonoidHom a.surjective
    (congrArg Covering.toMonoidHom ha) hp

/-- Consume the actual universal-cover kernels calculated in a multiplier table. -/
noncomputable def equivOfPCoreEqBotOfUniversalPGroup
    (f : Covering L G) (g : Covering U G) (hg : IsUniversal.{v, u, w} g)
    {p : ℕ} (hp : IsPGroup p g.toMonoidHom.ker) (hc : pCore p L = ⊥) : L ≃* G := by
  have hk : f.toMonoidHom.ker = ⊥ := by
    apply bot_unique
    rw [← hc]
    exact le_sSup ⟨inferInstance, ker_isPGroup_of_universal f g hg hp⟩
  exact MulEquiv.ofBijective f.toMonoidHom
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hk, f.surjective⟩

@[simp] theorem equivOfPCoreEqBotOfUniversalPGroup_apply
    (f : Covering L G) (g : Covering U G) (hg : IsUniversal.{v, u, w} g)
    {p : ℕ} (hp : IsPGroup p g.toMonoidHom.ker) (hc : pCore p L = ⊥) (x : L) :
    equivOfPCoreEqBotOfUniversalPGroup f g hg hp hc x = f x := by
  unfold equivOfPCoreEqBotOfUniversalPGroup
  rfl

end Theory.GroupTheory.Covering
