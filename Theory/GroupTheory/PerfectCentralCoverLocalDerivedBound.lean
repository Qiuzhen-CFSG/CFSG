module

public import Theory.GroupTheory.PerfectCentralCoverPrimaryQuotient
public import Theory.GroupTheory.PerfectCentralSupplement

/-!
# Primary bounds from the derived kernel of a local extension

Let H have index prime to p in the base of a finite perfect central cover.
First retain just the p-primary part of its kernel. Transfer puts this
entire kernel in the derived subgroup of the full preimage of H. The
restriction to H retains that same kernel. Consequently a bound for the
derived kernel of every central p-extension of H bounds the original
covering kernel, even when the original kernel had other prime factors.

The local extension is not assumed perfect: H itself need not be perfect.
The concrete application to the full involution centralizer of PSU₄(3)
is in `HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary`.
Source: the central-transfer argument underlying Aschbacher--Smith I.1.1--2,
printed p.407 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace PerfectCentralCovering
universe u v

/-- A primary bound on all local derived kernels applies to arbitrary
perfect central kernels. The local groups need not be perfect. -/
theorem Cover.not_primePower_dvd_kernel_of_local_derived_bound
    {E : Type u} {G : Type v} [Group E] [Finite E] [Group G]
    (f : Cover E G) {p n : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hi : ¬ p ∣ H.index)
    (hlocal : ∀ {D : Type u} [Group D] [Finite D] (g : D →* H),
      Function.Surjective g → g.ker ≤ center D → IsPGroup p g.ker →
        ¬ p ^ n ∣ Nat.card (g.ker ⊓ _root_.commutator D : Subgroup D)) :
    ¬ p ^ n ∣ Nat.card f.toMonoidHom.ker := by
  apply f.not_primePower_dvd_kernel_of_primary_case
  intro D _ _ c hp
  let : Group.IsPerfect D := c.isPerfect
  let M := H.comap c.toMonoidHom
  let q : M →* H := c.toMonoidHom.subgroupComap H
  have hq : Function.Surjective q :=
    c.toMonoidHom.subgroupComap_surjective_of_surjective H c.surjective
  have hker {x : M} (hx : x ∈ q.ker) : (x : D) ∈ c.toMonoidHom.ker :=
    congrArg Subtype.val hx
  have hKM : c.toMonoidHom.ker ≤ M := by
    intro x hx
    change c.toMonoidHom x ∈ H
    rw [MonoidHom.mem_ker.mp hx]
    exact H.one_mem
  let e : c.toMonoidHom.ker ≃* q.ker := {
    toFun x := ⟨⟨x.val, hKM x.property⟩, Subtype.ext x.property⟩
    invFun x := ⟨x.val.val, hker x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hqc : q.ker ≤ center M := by
    intro x hx
    exact mem_center_iff.mpr fun y =>
      Subtype.ext (mem_center_iff.mp (c.ker_le_center (hker hx)) y)
  have hder : c.toMonoidHom.ker ≤ ⁅M, M⁆ :=
    central_pSubgroup_le_commutator M c.toMonoidHom.ker hKM c.ker_le_center hp
      (by simpa only [M, Subgroup.index_comap_of_surjective _ c.surjective] using hi)
  have hqd : q.ker ≤ _root_.commutator M := by
    intro x hx
    have hxd := hder (hker hx)
    rw [← map_subtype_commutator] at hxd
    obtain ⟨y, hy, hyx⟩ := hxd
    exact (show y = x from Subtype.ext hyx) ▸ hy
  have hb := hlocal q hq hqc (hp.of_equiv e)
  rwa [inf_eq_left.mpr hqd, ← Nat.card_congr e.toEquiv] at hb

end PerfectCentralCovering
