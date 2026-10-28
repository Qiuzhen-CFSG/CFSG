module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PGroup.MaximalIndex
public import Mathlib.GroupTheory.Index


/-!
# Central-line automorphisms of an elementary eight

A subgroup of automorphisms of an elementary abelian group of order eight
which fixes an order-two subgroup pointwise and acts trivially on its quotient
has order at most four. Pointwise fixedness and trivial quotient action are
stated explicitly; there is no ambient classification assumption.

Choose a maximal subgroup W containing the fixed line Z. Its index is two,
so W has order four and Z has index two in W. Choose u in W outside Z and v
outside W. An automorphism is determined by its values on u and v, because
it fixes Z and each of the two index-two decompositions covers the group.
Its two displacements lie in Z; this embeds the automorphism subgroup in
Z times Z and gives the order-four bound.

This elementary action count supplies the terminal-core centralizer order
in Stellmacher(9.1), Journal of Algebra190 (1997), p.48. It uses only finite
elementary groups, maximal subgroups of two-groups, and subgroup indices.
-/

namespace Subgroup

public theorem card_le_four_of_fixed_line_and_trivial_quotient_on_eight
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U=8) (Z : Subgroup U) (hZ : Nat.card Z=2)
    (A : Subgroup (MulAut U))
    (hfix : ∀a∈A,∀z∈Z,a z=z)
    (hdiff : ∀a∈A,∀u:U,u⁻¹*a u∈Z) : Nat.card A≤4 := by
  classical
  have hZne : Z≠⊤ := by intro h; simp [h,hU] at hZ
  obtain ⟨W,hW,hZW⟩ := (eq_top_or_exists_le_coatom Z).resolve_left hZne
  have hWindex : W.index=2 := (IsElementaryAbelian.isPGroup 2 U).index_of_isCoatom W hW
  have hWcard : Nat.card W=4 := by
    have h := W.card_mul_index
    rw [hWindex,hU] at h
    omega
  have hWnot : ¬W≤Z := by
    intro h
    have hh := card_le_of_le h
    rw [hWcard,hZ] at hh
    omega
  obtain ⟨u,huW,huZ⟩ := SetLike.not_le_iff_exists.mp hWnot
  have hZidx : (Z.subgroupOf W).index=2 := by
    have h := (Z.subgroupOf W).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv,hZ,hWcard] at h
    omega
  obtain ⟨v,hvW⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hW.ne_top)
  have hv : v∉W := hvW.2
  let displacement : A → Z×Z := fun a =>
    (⟨u⁻¹*(a:MulAut U) u,hdiff a a.property u⟩,
     ⟨v⁻¹*(a:MulAut U) v,hdiff a a.property v⟩)
  have hdet : Function.Injective displacement := by
    intro a b hab
    have hu : (a:MulAut U) u=(b:MulAut U) u := by
      have hh := congrArg (fun p:Z×Z => (p.1:U)) hab
      exact mul_left_cancel hh
    have hv' : (a:MulAut U) v=(b:MulAut U) v := by
      have hh := congrArg (fun p:Z×Z => (p.2:U)) hab
      exact mul_left_cancel hh
    have hWfix : ∀w∈W,(a:MulAut U) w=(b:MulAut U) w := by
      intro w hw
      by_cases hz : w∈Z
      · rw [hfix a a.property w hz,hfix b b.property w hz]
      · have hprod : u⁻¹*w∈Z := by
          have hh : (⟨u,huW⟩:W)⁻¹*(⟨w,hw⟩:W)∈Z.subgroupOf W := by
            rw [mul_mem_iff_of_index_two hZidx]
            change (u⁻¹∈Z ↔ w∈Z)
            simp [huZ,hz]
          exact hh
        have ha := hfix a a.property _ hprod
        have hb := hfix b b.property _ hprod
        simp only [map_mul,map_inv] at ha hb
        rw [hu] at ha
        exact mul_left_cancel (ha.trans hb.symm)
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    by_cases hx : x∈W
    · exact hWfix x hx
    · have hprod : v⁻¹*x∈W := by
        rw [mul_mem_iff_of_index_two hWindex]
        simp [hv,hx]
      have hh := hWfix _ hprod
      simp only [map_mul,map_inv] at hh
      rw [hv'] at hh
      exact mul_left_cancel hh
  have hcard := Nat.card_le_card_of_injective displacement hdet
  rw [Nat.card_prod,hZ] at hcard
  exact hcard
end Subgroup
