module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormFixedSeed

/-! An exchanged pair is the full component orbit under the odd-rank bound,
so its product is normal.  This is the second-pumpup terminal case of
Aschbacher–Smith 2.5.19, printed p.564. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G] [Finite G]

theorem exchanged_component_pair_normal
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (P : Subgroup G) (hP : IsComponent G P) (t : G)
    (hm : P.map (MulAut.conj t).toMonoidHom ≠ P) :
    (P ⊔ P.map (MulAut.conj t).toMonoidHom : Subgroup G).Normal := by
  have hidx : (normalizer (P : Set G)).index = 2 := by
    rcases hP.normal_or_index_two_of_odd_rank_le_two hrank with hn | hi
    · exact (hm (normal_iff_map_conj_eq.mp hn t)).elim
    · exact hi
  let X := P ⊔ P.map (MulAut.conj t).toMonoidHom
  have hc (g : G) : P.map (MulAut.conj g).toMonoidHom ≤ X := by
    change P.map (MulAut.conj g).toMonoidHom ≤ P ⊔ P.map (MulAut.conj t).toMonoidHom
    rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two (K := P) (a := t) hidx hm g with he | he
    · rw [he]
      exact le_sup_left
    · rw [he]
      exact le_sup_right
  have hmX (g : G) : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rw [Subgroup.map_sup]
    apply sup_le (hc g)
    rw [map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (g*t)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev]
      group
    rw [he]
    exact hc (g*t)
  exact ⟨fun x hx g => hmX g (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
