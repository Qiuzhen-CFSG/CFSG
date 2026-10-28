module

public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Residuals in solvable supplements

If a subgroup supplements a solvable normal subgroup, its residual maps onto
the ambient residual modulo that normal subgroup. If the ambient residual is
a C-component, so is the supplement's residual. The proof uses the actual
quotient homomorphism and the C-component correspondence through solvable
kernels, not just an abstract isomorphism of simple quotients.

Source: Aschbacher–Smith, A.3.3(3–4), printed pp.42–43. The application in
13.6.16(2), printed p.930, takes a characteristic-subgroup normalizer as the
supplement. The surjection argument also occurs in the project's proof of
1.3.8 in `Chapter1.Section03.Radical.Normalizers.Residual.Components`.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_surjective_of_sup_eq_top (R N : Subgroup G) [R.Normal]
    (hgen : R ⊔ N = ⊤) :
    Function.Surjective ((QuotientGroup.mk' R).comp N.subtype) := by
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R z
  have hg : g ∈ R ⊔ N := hgen.symm ▸ mem_top g
  obtain ⟨r, hr, n, hn, rfl⟩ := mem_sup_of_normal_left.mp hg
  refine ⟨⟨n, hn⟩, ?_⟩
  change QuotientGroup.mk' R n = QuotientGroup.mk' R (r * n)
  have hrq : QuotientGroup.mk' R r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  rw [map_mul, hrq, one_mul]

/-- A normal supplement covers the ambient residual together with the
residual of the other factor. Solvability of the normal factor is not needed. -/
theorem solvableResidual_le_sup_residual_of_sup_eq_top
    (R N : Subgroup G) [R.Normal] (hgen : R ⊔ N = ⊤) :
    solvableResidual G ≤ R ⊔ (solvableResidual N).map N.subtype := by
  let q := QuotientGroup.mk' R
  have he : (solvableResidual G).map q =
      ((solvableResidual N).map N.subtype).map q := by
    rw [map_map, map_solvableResidual_eq q (QuotientGroup.mk'_surjective R),
      map_solvableResidual_eq (q.comp N.subtype)
        (quotient_surjective_of_sup_eq_top R N hgen)]
  have hc := congrArg (comap q) he
  rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at hc
  exact le_sup_left.trans (hc.le.trans_eq (sup_comm _ _))

/-- Having a C-component as residual lifts through a solvable kernel. -/
theorem residual_isCComponent_of_surjective
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hB : (solvableResidual B).IsCComponent) :
    (solvableResidual A).IsCComponent := by
  have hne : solvableResidual A ≠ ⊥ := by
    intro he
    have hh := map_solvableResidual_eq f hf
    rw [he, map_bot] at hh
    exact hB.ne_bot hh.symm
  obtain ⟨K, hKR, hK⟩ := exists_isCComponent_le hne inferInstance
    (inferInstance : (solvableResidual A).Normal).isSubnormal
  have hm : K.map f = (solvableResidual A).map f := by
    rw [map_solvableResidual_eq f hf]
    exact (cComponent_map_of_solvable_ker hK f hf).eq_of_le hB
      ((map_mono hKR).trans_eq (map_solvableResidual_eq f hf))
  have hcover : solvableResidual A ≤ K ⊔ f.ker := by
    have h := congrArg (comap f) hm
    rw [comap_map_eq, comap_map_eq] at h
    exact le_sup_left.trans h.ge
  have hle := le_map_solvableResidual_of_isPerfect (solvableResidual A) (K ⊔ f.ker) hcover
  rw [hK.solvableResidual_sup_eq f.ker le_normalizer_of_normal] at hle
  exact (le_antisymm hKR hle) ▸ hK

/-- A supplement to a solvable normal subgroup inherits a C-component residual. -/
theorem residual_isCComponent_of_solvable_supplement
    (R N : Subgroup G) [R.Normal] [Group.IsSolvable R]
    (hgen : R ⊔ N = ⊤) (hG : (solvableResidual G).IsCComponent) :
    (solvableResidual N).IsCComponent := by
  let q := QuotientGroup.mk' R
  let f := q.comp N.subtype
  let k : f.ker →* R := (N.subtype.comp f.ker.subtype).codRestrict R (by
    intro x
    exact (QuotientGroup.eq_one_iff (x.val : G)).mp x.property)
  have hk : Function.Injective k := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : R => (z : G)) hab))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hk
  have hq := hG.map_quotient R
  rw [map_solvableResidual_eq q (QuotientGroup.mk'_surjective R)] at hq
  exact residual_isCComponent_of_surjective f
    (quotient_surjective_of_sup_eq_top R N hgen) hq

/-- Ambient form of residual coverage by a normal supplement. -/
theorem map_solvableResidual_le_sup_residual_of_sup_eq
    (H R N : Subgroup G) (hRH : R ≤ H) (hNH : N ≤ H)
    (hn : H ≤ normalizer (R : Set G)) (hgen : R ⊔ N = H) :
    (solvableResidual H).map H.subtype ≤ R ⊔ (solvableResidual N).map N.subtype := by
  let R' := R.subgroupOf H
  let N' := N.subgroupOf H
  let : R'.Normal := normal_subgroupOf_of_le_normalizer hn
  have hgen' : R' ⊔ N' = ⊤ := by
    apply map_injective H.subtype_injective
    simp only [R', N', map_sup, map_subgroupOf_eq_of_le hRH,
      map_subgroupOf_eq_of_le hNH, hgen, ← MonoidHom.range_eq_map, range_subtype]
  have hm := map_mono (f := H.subtype)
    (solvableResidual_le_sup_residual_of_sup_eq_top R' N' hgen')
  have he : ((solvableResidual N').map N'.subtype).map H.subtype =
      (solvableResidual N).map N.subtype := by
    let e := subgroupOfEquivOfLe hNH
    have hc : N.subtype.comp e.toMonoidHom = H.subtype.comp N'.subtype := rfl
    rw [map_map, ← hc, ← map_map, map_solvableResidual_eq e.toMonoidHom e.surjective]
  simpa only [map_sup, R', map_subgroupOf_eq_of_le hRH, he] using hm

/-- Ambient form of the C-component residual theorem for a solvable supplement. -/
theorem residual_isCComponent_of_solvable_supplement_in
    (H R N : Subgroup G) (hRH : R ≤ H) (hNH : N ≤ H)
    (hn : H ≤ normalizer (R : Set G)) [Group.IsSolvable R]
    (hgen : R ⊔ N = H) (hH : (solvableResidual H).IsCComponent) :
    (solvableResidual N).IsCComponent := by
  let R' := R.subgroupOf H
  let N' := N.subgroupOf H
  let : R'.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Group.IsSolvable R' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hRH).toMonoidHom) (subgroupOfEquivOfLe hRH).injective
  have hgen' : R' ⊔ N' = ⊤ := by
    apply map_injective H.subtype_injective
    simp only [R', N', map_sup, map_subgroupOf_eq_of_le hRH,
      map_subgroupOf_eq_of_le hNH, hgen, ← MonoidHom.range_eq_map, range_subtype]
  have h := residual_isCComponent_of_solvable_supplement R' N' hgen' hH
  let e := subgroupOfEquivOfLe hNH
  have hm := h.map_equiv e
  rwa [map_solvableResidual_eq e.toMonoidHom e.surjective] at hm

omit [Finite G] in
/-- A perfect normal subgroup with a solvable supplement is the residual of
the join, with both subgroup inclusions retained. -/
theorem map_residual_sup_eq_of_perfect_of_solvable
    (K S : Subgroup G) [Group.IsPerfect K] [Group.IsSolvable S]
    (hS : S ≤ normalizer (K : Set G)) :
    (solvableResidual (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = K := by
  let H := K ⊔ S
  let K' := K.subgroupOf H
  let S' := S.subgroupOf H
  let : K'.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hS)
  let : Group.IsSolvable S' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show S ≤ H from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show S ≤ H from le_sup_right)).injective
  have hg : K' ⊔ S' = ⊤ := (codisjoint_subgroupOf_sup K S).eq_top
  let : Group.IsSolvable (H ⧸ K') := Group.isSolvable_of_surjective
    (quotient_surjective_of_sup_eq_top K' S' hg)
  apply le_antisymm _ (le_map_solvableResidual_of_isPerfect K H le_sup_left)
  have hm := map_mono (f := H.subtype) (solvableResidual_le_of_solvable_quotient K')
  simpa only [K', map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] using hm

end Subgroup
