module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.QuotientAction.Points
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Two-group kernels of the literal parabolic core actions

For the marked commuting S₄ pair, its product is normal in the generated
star overgroup and has a two-group quotient, supplied by T*. An element
of this product fixing every core point has both coordinates in the
respective two-cores: each S₄ two-core is self-centralizing. Thus the
point-action kernel has a two-group intersection with the factor product
and a two-group image in the quotient, so it is itself a two-group.

The lifted action has a two-group kernel by pulling back through the
published star projection, whose kernel is already a two-group. Neither
calculation assumes an image order or a wreath-product identification.

These are the kernel calculations for the L₃(2) wreath-overgroup route in
Aschbacher–Smith, Lemma 13.8.16(1), printed p.952. The exact two-core and
wreath-quotient identifications remain with the quotient assembly.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair
variable {G : Type*} [Group G] {H L₁ T : Subgroup G} (d : ParabolicPair H L₁ T)

private theorem kernel_commutes (g : d.starOvergroup) (hg : g ∈ d.corePointAction.ker)
    (x : Source.Hstar H) (hx : x ∈ d.left.pCoreIn 2 ∨ x ∈ d.right.pCoreIn 2) :
    Commute g.val x := by
  by_cases h1 : x = 1
  · rw [h1]
    exact Commute.one_right _
  · have he := congrArg (fun f : Equiv.Perm d.CorePoints =>
        (f ⟨x, h1, hx⟩ : Source.Hstar H)) (MonoidHom.mem_ker.mp hg)
    change g.val * x * g.val⁻¹ = x at he
    exact mul_inv_eq_iff_eq_mul.mp he

private theorem cores_isPGroup :
    IsPGroup 2 (d.left.pCoreIn 2 ⊔ d.right.pCoreIn 2 : Subgroup (Source.Hstar H)) := by
  apply (isPGroup_pCoreIn 2 d.left).to_sup_of_normal_right'
    (isPGroup_pCoreIn 2 d.right)
  apply le_trans _ (centralizer_le_normalizer _)
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact (d.commute x (pCoreIn_le 2 d.left hx) y (pCoreIn_le 2 d.right hy)).eq.symm

variable [Finite G]

private theorem kernel_product_le_cores (g : d.starOvergroup)
    (hg : g ∈ d.corePointAction.ker) (hprod : g.val ∈ d.left ⊔ d.right) :
    g.val ∈ d.left.pCoreIn 2 ⊔ d.right.pCoreIn 2 := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    d.left d.right d.disjoint (by
      intro a ha
      rw [mem_centralizer_iff]
      intro b hb
      exact (d.commute a ha b hb).eq.symm)
  obtain ⟨⟨a, b⟩, hab⟩ := e.surjective ⟨g.val, hprod⟩
  have hab' : (a : Source.Hstar H) * b = g.val :=
    (he a b).symm.trans (congrArg Subtype.val hab)
  have ha : a ∈ pCore 2 d.left := by
    apply Matrix.PSL3Two.ParabolicCoreModel.core_selfCentralizing d.leftEquiv
    rw [mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    have hc := d.kernel_commutes g hg x.val
      (Or.inl (mem_map_of_mem d.left.subtype hx))
    rw [← hab'] at hc
    have hb := (d.commute x.val x.property b.val b.property).symm
    simpa using (hc.mul_left hb.inv_left).eq.symm
  have hb : b ∈ pCore 2 d.right := by
    apply Matrix.PSL3Two.ParabolicCoreModel.core_selfCentralizing d.rightEquiv
    rw [mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    have hc := d.kernel_commutes g hg x.val
      (Or.inr (mem_map_of_mem d.right.subtype hx))
    rw [← hab'] at hc
    have ha := d.commute a.val a.property x.val x.property
    simpa [mul_assoc] using (ha.inv_left.mul_left hc).eq.symm
  rw [← hab']
  exact mul_mem_sup (mem_map_of_mem d.left.subtype ha)
    (mem_map_of_mem d.right.subtype hb)

/-- The kernel of literal conjugation on the parabolic core points is a two-group. -/
theorem corePointAction_kernel_isPGroup : IsPGroup 2 d.corePointAction.ker := by
  let N := (d.left ⊔ d.right).subgroupOf d.starOvergroup
  let R := (Source.starImage H T).subgroupOf d.starOvergroup
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (d.left ⊔ d.right).le_normalizer d.normalizes_product)
  have hT : IsPGroup 2 (Source.starImage H T) :=
    (d.two.comap_of_injective H.subtype H.subtype_injective).map _
  have hquot : IsPGroup 2 (d.starOvergroup ⧸ N) := by
    apply isPGroup_quotient_of_sup_eq_top N R hT.comap_subtype
    rw [← subgroupOf_sup (show d.left ⊔ d.right ≤ d.starOvergroup from le_sup_left)
      (show Source.starImage H T ≤ d.starOvergroup from le_sup_right)]
    exact subgroupOf_self _
  let f : d.corePointAction.ker →* (d.starOvergroup ⧸ N) :=
    (QuotientGroup.mk' N).comp d.corePointAction.ker.subtype
  have hker : IsPGroup 2 f.ker := by
    let j : f.ker →* Source.Hstar H := d.starOvergroup.subtype.comp
      (d.corePointAction.ker.subtype.comp f.ker.subtype)
    have hj (x : f.ker) : j x ∈ d.left.pCoreIn 2 ⊔ d.right.pCoreIn 2 := by
      apply d.kernel_product_le_cores x.val.val x.val.property
      exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property
    apply d.cores_isPGroup.of_injective (j.codRestrict _ hj)
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (d.left.pCoreIn 2 ⊔ d.right.pCoreIn 2 : Subgroup (Source.Hstar H)) =>
      (z : Source.Hstar H)) hxy
  have ht := (hquot.to_subgroup (⊤ : Subgroup (d.starOvergroup ⧸ N))).comap_of_ker_isPGroup
    f hker
  simpa using ht.of_equiv Subgroup.topEquiv

/-- The same kernel bound survives the full lift through O₂(H). -/
theorem liftedCorePointAction_kernel_isPGroup : IsPGroup 2 d.liftedCorePointAction.ker := by
  exact d.corePointAction_kernel_isPGroup.comap_of_ker_isPGroup
    d.starProjection d.starProjection_kernel_isPGroup

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair

end
