module
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PerfectCentralModSolvable
/-!
# Perfect subgroup normalizers in a normal quotient action

Let C be normal and N a solvable characteristic subgroup of C. For a
perfect subgroup R of C normalized by N, ambient conjugation on C/N
reflects the full normalizer of R. Restrict to C: the kernel of the inner
quotient action is central modulo N. Perfect containment lifts through
that central quotient, then through N by taking the solvable residual.
Apply this to each ambient conjugate of R.

The theorem does not require R to be normal or subnormal in C. Its local
Cartan application is the quotient-action step of Aschbacher--Smith 5.1.13,
printed p.636, with N = O₂(C).
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_le_of_normalQuotientAction_map_le
    (C : Subgroup G) [C.Normal] (N : Subgroup C) [N.Characteristic]
    [Group.IsSolvable N] (P B : Subgroup G)
    [Group.IsPerfect P] [Group.IsPerfect B]
    (hPC : P ≤ C) (hBC : B ≤ C)
    (hn : N.map C.subtype ≤ normalizer (B : Set G))
    (hm : P.map (normalQuotientAction C N) ≤ B.map (normalQuotientAction C N)) : P ≤ B := by
  let f := (normalQuotientAction C N).comp C.subtype
  let q := QuotientGroup.mk' N
  have hN : N ≤ f.ker := by
    intro x hx
    change normalQuotientAction C N (x : G) = 1
    have hqx : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [normalQuotientAction_inner, hqx, map_one]
  have hc : f.ker.map q ≤ center (C ⧸ N) := by
    rintro z ⟨x,hx,rfl⟩
    have hx' : MulAut.conj (q x) = 1 := by
      change normalQuotientAction C N (x : G) = 1 at hx
      rwa [normalQuotientAction_inner] at hx
    apply mem_center_iff.mpr
    intro y
    have he := congrArg (fun a : MulAut (C ⧸ N) => a y) hx'
    change q x * y * (q x)⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let : Group.IsPerfect (P.subgroupOf C) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPC).symm.toMonoidHom)
    (subgroupOfEquivOfLe hPC).symm.surjective
  let : Group.IsPerfect (B.subgroupOf C) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBC).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBC).symm.surjective
  have hn' : N ≤ normalizer (B.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hBC]
    intro x hx
    exact hn (mem_map_of_mem C.subtype hx)
  have hm' : (P.subgroupOf C).map f ≤ (B.subgroupOf C).map f := by
    simpa only [f,←Subgroup.map_map,map_subgroupOf_eq_of_le hPC,
      map_subgroupOf_eq_of_le hBC] using hm
  have hp := perfect_le_of_map_le_of_kernel_central_mod_solvable
    f N hN hc (P.subgroupOf C) (B.subgroupOf C) hn' hm'
  have he := map_mono (f := C.subtype) hp
  simpa only [map_subgroupOf_eq_of_le hPC,map_subgroupOf_eq_of_le hBC] using he

/-- The literal action on C/N creates no new normalizers of a perfect
subgroup normalized by the solvable characteristic kernel. -/
theorem normalQuotientAction_perfect_normalizer
    (C : Subgroup G) [C.Normal] (N : Subgroup C) [N.Characteristic]
    [Group.IsSolvable N] (R : Subgroup G) [Group.IsPerfect R]
    (hRC : R ≤ C) (hn : N.map C.subtype ≤ normalizer (R : Set G)) :
    (normalizer (R.map (normalQuotientAction C N) : Set (MulAut (C ⧸ N)))).comap
      (normalQuotientAction C N) = normalizer (R : Set G) := by
  let f := normalQuotientAction C N
  apply le_antisymm
  · intro x hx
    apply mem_normalizer_fintype
    intro r hr
    let P := R.map (MulAut.conj x).toMonoidHom
    let : Group.IsPerfect P := Group.IsPerfect.map _
    have hPC : P ≤ C := by
      rintro y ⟨s,hs,rfl⟩
      exact (inferInstance : C.Normal).conj_mem s (hRC hs) x
    have hm : P.map f ≤ R.map f := by
      have he : P.map f = (R.map f).map (MulAut.conj (f x)).toMonoidHom := by
        change (R.map (MulAut.conj x).toMonoidHom).map f =
          (R.map f).map (MulAut.conj (f x)).toMonoidHom
        rw [Subgroup.map_map,Subgroup.map_map]
        congr 1
        ext s
        simp [MulAut.conj_apply]
      rw [he]
      exact (mem_normalizer_iff_map_conj_eq.mp hx).le
    exact (perfect_le_of_normalQuotientAction_map_le C N P R hPC hRC hn hm)
      (mem_map_of_mem (MulAut.conj x).toMonoidHom hr)
  · exact map_le_iff_le_comap.mp (R.le_normalizer_map f)

end Subgroup
