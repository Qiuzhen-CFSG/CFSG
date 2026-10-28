module
public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The join of a constrained C-component and a two-group

If the component has two conjugates and R moves it, its R-orbit is its
full conjugacy orbit. Thus N(R) preserves the join of the component and R.
When the ambient odd core is trivial and the component is constrained,
that join has characteristic two by the C-component prime-group theorem.
These are the restriction steps used in Aschbacher--Smith C.4.4, p.152.
-/
public section
open Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_join_of_moved_index_two {K R : Subgroup G}
    (hi : (normalizer (K : Set G)).index = 2)
    (hm : ¬ R ≤ normalizer (K : Set G)) :
    normalizer (R : Set G) ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) := by
  obtain ⟨a,ha,han⟩ := Set.not_subset.mp hm
  have hmove : K.map (MulAut.conj a).toMonoidHom ≠ K :=
    fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)
  let D := K ⊔ K.map (MulAut.conj a).toMonoidHom
  have hc (g : G) : K.map (MulAut.conj g).toMonoidHom ≤ D := by
    rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hmove g with he | he
    · rw [he]; exact le_sup_left
    · rw [he]; exact le_sup_right
  have hD : D.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hmap : D.map (MulAut.conj g).toMonoidHom ≤ D := by
      rw [Subgroup.map_sup]
      apply sup_le (hc g)
      rw [map_map]
      have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (g*a)).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev]
        group
      rw [he]
      exact hc (g*a)
    exact hmap (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  let := hD
  have he : D ⊔ R = K ⊔ R := by
    apply le_antisymm
    · refine sup_le (sup_le le_sup_left ?_) le_sup_right
      rintro x ⟨k,hk,rfl⟩
      exact (K ⊔ R).mul_mem ((K ⊔ R).mul_mem (mem_sup_right ha)
        (mem_sup_left hk)) ((K ⊔ R).inv_mem (mem_sup_right ha))
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  rw [← he]
  exact (le_inf (show normalizer (R : Set G) ≤ normalizer (D : Set G) from by
    rw [normalizer_eq_top (H := D)]; exact le_top) le_rfl).trans
    (normalizer_inf_normalizer_le_normalizer_sup D R)

theorem IsCComponent.constrained_join_characteristicTwo {K R : Subgroup G}
    (hK : K.IsCComponent) (hr : IsPGroup 2 R)
    (ho : pPrimeCore 2 G = ⊥) (hf : generalizedFitting K = pCore 2 K) :
    centralizer (pCore 2 ↥(K ⊔ R) : Set ↥(K ⊔ R)) ≤ pCore 2 ↥(K ⊔ R) := by
  rcases hK.component_or_generalizedFitting_sup_eq_pCore hr ho with hc | hc
  · let := hc.2
    have he : pCore 2 K = ⊤ := hf.symm.trans generalizedFitting_eq_top_of_quasisimple
    have hp : IsPGroup 2 K := (he ▸ (pCore_isPGroup (p := 2) (G := K))).of_equiv topEquiv
    let := hp.isNilpotent
    exact (hK.not_isSolvable inferInstance).elim
  · exact hc ▸ centralizer_generalizedFitting_le ↥(K ⊔ R)

end Subgroup
