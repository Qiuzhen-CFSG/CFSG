module
public import Theory.GroupTheory.SolvableResidual.DerivedCentralCover
public import Theory.GroupTheory.PerfectCentralCoverLocalBound
public import Mathlib.GroupTheory.IndexNormal

/-!
# Perfect index-two restrictions of central double covers

Let E be a perfect central double cover of G. If J has odd index in G and
its derived subgroup is perfect of index two, the full inverse image of
that derived subgroup is perfect. Transfer first puts the binary kernel
in the commutator of the inverse image of J. If the perfect residual missed
the kernel, the residual splitting calculation would identify this
commutator with the residual, a contradiction.

The subgroup form retains an arbitrary actual perfect subgroup B of index
two in J. The M₂₂ pair-stabilizer application is the local restriction
needed in Aschbacher--Smith 8.2.10(3), printed p.721, using I.2.2(6), p.412.
-/

public section
open Subgroup
namespace PerfectCentralCovering
variable {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]

/-- A perfect derived subgroup of index two retains the whole binary covering
kernel when its overgroup has odd index in the ambient perfect cover. -/
theorem Cover.perfect_preimage_derived_index_two
    (c : Cover E G) (hk : Nat.card c.toMonoidHom.ker = 2)
    (J : Subgroup G) (hi : Odd J.index)
    [Group.IsPerfect (_root_.commutator J)]
    (hd : (_root_.commutator J).index = 2) :
    Group.IsPerfect (((_root_.commutator J).map J.subtype).comap c.toMonoidHom) := by
  let f := c.toMonoidHom
  let P := J.comap f
  let q : P →* J := f.subgroupComap J
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective J c.surjective
  have hkp : f.ker ≤ P := f.ker_le_comap J
  have hqker : q.ker = f.ker.subgroupOf P := by
    ext x
    exact Subtype.ext_iff
  have hqcard : Nat.card q.ker = 2 := by
    rw [hqker, Nat.card_congr (subgroupOfEquivOfLe hkp).toEquiv]
    exact hk
  let : Group.IsPerfect E := c.isPerfect
  have hZ : f.ker ≤ ⁅P,P⁆ := central_pSubgroup_le_commutator P f.ker hkp
    c.ker_le_center (IsPGroup.of_card (n := 1) (by simpa using hk)) (by
      rw [index_comap_of_surjective _ c.surjective]
      exact hi.not_two_dvd_nat)
  have hZD : q.ker ≤ _root_.commutator P := by
    intro x hx
    have hx' : x ∈ f.ker.subgroupOf P := hqker ▸ hx
    have hh := hZ hx'
    rw [←map_subtype_commutator] at hh
    obtain ⟨y,hy,he⟩ := hh
    exact (Subtype.ext he : y=x) ▸ hy
  have hZR : q.ker ≤ solvableResidual P := by
    by_contra hn
    have hodd : ¬ 2 ∣ Nat.card (residualDerivedMap q).ker := by
      intro hh
      let j : (residualDerivedMap q).ker →* q.ker := {
        toFun x := ⟨x.val.val,congrArg Subtype.val x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
      have hj : Function.Injective j := by
        intro x y he
        exact Subtype.ext (Subtype.ext (congrArg (fun a : q.ker => (a : P)) he))
      have he : j.range = ⊤ := by
        apply eq_top_of_card_eq
        rw [←Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,hqcard]
        exact Nat.dvd_antisymm (hqcard ▸ card_dvd_of_injective j hj) hh
      apply hn
      intro x hx
      obtain ⟨y,hy⟩ := MonoidHom.range_eq_top.mp he ⟨x,hx⟩
      have hxy : y.val.val = x := congrArg Subtype.val hy
      exact hxy ▸ y.val.property
    have hb := residualDerivedMap_bijective_of_two_kernel q hq hqcard hodd
    exact hn ((commutator_eq_residual_of_two_kernel q hq hqcard hd hb) ▸ hZD)
  let D := (solvableResidual P).map P.subtype
  have hm : D.map f = (_root_.commutator J).map J.subtype := by
    rw [show D = (solvableResidual P).map P.subtype from rfl,
      map_solvableResidual_comap f c.surjective J,
      residual_eq_commutator_of_perfect_derived]
  have hkerD : f.ker ≤ D := by
    intro x hx
    exact ⟨⟨x,hkp hx⟩,hZR (hqker.symm ▸ hx),rfl⟩
  have hD : ((_root_.commutator J).map J.subtype).comap f = D := by
    rw [←hm,comap_map_eq,sup_of_le_left hkerD]
  change Group.IsPerfect (((_root_.commutator J).map J.subtype).comap f)
  rw [hD]
  exact Group.IsPerfect.map P.subtype

/-- The literal full preimage of a perfect subgroup of index two in an odd-index
subgroup is perfect. -/
theorem Cover.perfect_preimage_of_index_two
    (c : Cover E G) (hk : Nat.card c.toMonoidHom.ker = 2)
    (J B : Subgroup G) (hBJ : B ≤ J) (hi : Odd J.index)
    [Group.IsPerfect B] (hBi : (B.subgroupOf J).index = 2) :
    Group.IsPerfect (B.comap c.toMonoidHom) := by
  let B₀ := B.subgroupOf J
  let : Group.IsPerfect B₀ := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBJ).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBJ).symm.surjective
  have hder : _root_.commutator J = B₀ := by
    let : B₀.Normal := normal_of_index_eq_two hBi
    let : IsCyclic (J ⧸ B₀) := isCyclic_of_prime_card hBi
    apply le_antisymm
    · exact Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    · exact B₀.commutator_eq_self.symm.le.trans (commutator_mono le_top le_top)
  let : Group.IsPerfect (_root_.commutator J) := hder.symm ▸ inferInstance
  have hm : (_root_.commutator J).map J.subtype = B := by
    rw [hder]
    exact map_subgroupOf_eq_of_le hBJ
  have hp := c.perfect_preimage_derived_index_two hk J hi (hder.symm ▸ hBi)
  rwa [hm] at hp

end PerfectCentralCovering
