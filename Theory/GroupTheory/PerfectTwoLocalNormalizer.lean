module
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.PGroup

/-!
# Perfect subgroups and inner two-local normalizers

Suppose every nontrivial two-subgroup of a centerless group has a solvable
normalizer. A nontrivial perfect subgroup of its inner automorphism group
cannot normalize a nontrivial inner two-subgroup. Faithful conjugation
identifies the latter subgroup with its actual preimage; its normalizer
would otherwise contain an injective image of the perfect subgroup.

Source application: Aschbacher–Smith, original 4.3.16(2), printed p.618;
`NonblockEndgameSieveExclusionsUnitary` supplies the unitary local geometry.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A nontrivial perfect inner subgroup excludes every normalized inner two-subgroup. -/
theorem inner_twoGroup_eq_bot_of_perfect_normalizer
    (hZ : center G = ⊥)
    (hlocal : ∀ P : Subgroup G, IsPGroup 2 P → P ≠ ⊥ →
      Group.IsSolvable (normalizer (P : Set G)))
    (X : Subgroup (MulAut G)) [Group.IsPerfect X] (hne : X ≠ ⊥)
    (hiX : X ≤ MulAut.innerSubgroup G)
    (R : Subgroup (MulAut G)) (hR : IsPGroup 2 R)
    (hi : R ≤ MulAut.innerSubgroup G)
    (hXR : X ≤ normalizer (R : Set (MulAut G))) : R = ⊥ := by
  let j : G →* MulAut G := MulAut.conj
  have hj : Function.Injective j := MulAut.conj_injective_of_center_eq_bot hZ
  let P := R.comap j
  have hp : IsPGroup 2 P := hR.of_injective (j.subgroupComap R) (by
    intro x y h
    exact Subtype.ext (hj (congrArg Subtype.val h)))
  have hmap : P.map j = R := map_comap_eq_self hi
  by_contra hr
  have hP : P ≠ ⊥ := by
    intro he
    rw [he,Subgroup.map_bot] at hmap
    exact hr hmap.symm
  let := hlocal P hp hP
  let e := MonoidHom.ofInjective hj
  let f : X →* G := e.symm.toMonoidHom.comp
    (X.subtype.codRestrict (MulAut.innerSubgroup G) (fun x => hiX x.property))
  have hf (x : X) : j (f x) = x := congrArg Subtype.val (e.apply_symm_apply
    (⟨x,hiX x.property⟩ : MulAut.innerSubgroup G))
  have hfn (x : X) : f x ∈ normalizer (P : Set G) := by
    apply mem_normalizer_iff.mpr
    intro p
    have hn := mem_normalizer_iff.mp (hXR x.property) (j p)
    change j p ∈ R ↔ j (f x * p * (f x)⁻¹) ∈ R
    simpa only [map_mul,map_inv,hf] using hn
  let k : X →* normalizer (P : Set G) := f.codRestrict _ hfn
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    have hh := congrArg (fun z : normalizer (P : Set G) => j z.val) he
    exact (hf x).symm.trans (hh.trans (hf y))
  let : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective (f := k) hk
  let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable X inferInstance
end Theory.GroupTheory
