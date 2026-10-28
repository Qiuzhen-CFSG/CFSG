module
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Two-group extensions of a symmetric-three core quotient

If a normal subgroup has two-core quotient S₃ and a two-group supplements
it, the entire group has the same two-core quotient. The conjugation action
on S₃ is inner and faithful on that normal image. The supplement makes its
remaining kernel a two-group, so it disappears upon removing the two-core.
No splitting of the original group is required.

Source application: Aschbacher--Smith 15.1.22(*), (3), pp.1098--1100.
-/
public section
open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThreeExtension
open NormalSymmetricThreePairRank
variable {G : Type*} [Group G]
private theorem conj_bijective :
    Function.Bijective (MulAut.conj : Equiv.Perm (Fin 3) →* MulAut (Equiv.Perm (Fin 3))) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply symmetricThree_center_trivial x
    intro y
    have hh := congrArg (fun a : MulAut (Equiv.Perm (Fin 3)) => a y) hx
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro a
    obtain ⟨x,hx⟩ := symmetricThree_aut_inner a
    exact ⟨x,hx.symm⟩

/-- A core-free two-group extension of a normal S₃ is S₃. -/
theorem coreFree (hcore : pCore 2 G = ⊥)
    (N P : Subgroup G) [N.Normal] (e : N ≃* Equiv.Perm (Fin 3))
    (hP : IsPGroup 2 P) (hgen : N ⊔ P = ⊤) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  let c := MulEquiv.ofBijective (MulAut.conj : Equiv.Perm (Fin 3) →* _) conj_bijective
  let f : G →* Equiv.Perm (Fin 3) := c.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N)))
  have hfN : f.comp N.subtype = e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply c.injective
    change c (c.symm ((MulAut.congr e) (MulAut.conjNormal (x : G)))) = _
    rw [c.apply_symm_apply,MulAut.conjNormal_val,MulAut.congr_conj]
    rfl
  have hkerN : (f.comp N.subtype).ker = ⊥ := by
    rw [hfN]
    exact e.toMonoidHom.ker_eq_bot e.injective
  have hk : IsPGroup 2 f.ker := f.kernel_isPGroup_of_normal_supplement N P hP hgen
    (by rw [hkerN]; exact IsPGroup.of_subsingleton 2 _)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact bot_unique ((show f.ker ≤ pCore 2 G from le_sSup ⟨inferInstance,hk⟩).trans hcore.le)
  refine ⟨MulEquiv.ofBijective f ⟨hf,?_⟩⟩
  intro x
  obtain ⟨n,rfl⟩ := e.surjective x
  exact ⟨n,DFunLike.congr_fun hfN n⟩

/-- Adjoining a normalizing two-group preserves the normal S₃ core quotient. -/
theorem quotient [Finite G]
    (N P : Subgroup G) [N.Normal] (e : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3))
    (hP : IsPGroup 2 P) (hgen : N ⊔ P = ⊤) :
    Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let I := N.map q
  let R := P.map q
  let : I.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let t : I ≃* Equiv.Perm (Fin 3) :=
    ((Normal.isSubnormal (inferInstance : N.Normal)).quotientCoreImageEquiv 2).symm.trans e
  have hgen' : I ⊔ R = ⊤ := by
    rw [←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map,
      q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective _)]
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcore : pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
    apply comap_injective (QuotientGroup.mk'_surjective (pCore 2 G))
    rw [q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hqker,
      MonoidHom.comap_bot,QuotientGroup.ker_mk']
  exact coreFree hcore I R t (hP.map q) hgen'

/-- The same statement for the literal join of the original subgroups. -/
theorem normalized_join [Finite G]
    (N P : Subgroup G) (hn : P ≤ normalizer (N : Set G))
    (e : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3)) (hP : IsPGroup 2 P) :
    Nonempty (((N ⊔ P : Subgroup G) ⧸ pCore 2 (N ⊔ P : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let H := N ⊔ P
  let I := N.subgroupOf H
  let R := P.subgroupOf H
  let : I.Normal := normal_subgroupOf_of_le_normalizer (sup_le N.le_normalizer hn)
  let t : I ≃* N := subgroupOfEquivOfLe (show N ≤ H from le_sup_left)
  have hgen : I ⊔ R = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show N ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show P ≤ H from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  exact quotient I R ((QuotientGroup.congr _ _ t (pCore_map_iso 2 t)).trans e)
    hP.comap_subtype hgen
end Theory.GroupTheory.NormalSymmetricThreeExtension
