module
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.Completion
public import Mathlib.GroupTheory.Index

/-!
# Conjugate elementary TI subgroups in a two-group

The elementary TI-pair theorem gives commutation once a mutual normalizer
is nontrivial. A relative-index bound supplies that nontrivial intersection.
Automorphism transport and the equality-or-disjoint alternative retain
the literal conjugate embeddings.

Source: Aschbacher–Smith, I.6.2 and its use in 2.4.19, printed pp.424,534.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

theorem IsTISubgroup.map_equiv {Z : Subgroup G} (hZ : IsTISubgroup Z) (e : G ≃* G) :
    IsTISubgroup (Z.map e.toMonoidHom) := by
  apply (isTISubgroup_iff _).mpr
  intro g hg x hx hgx
  obtain ⟨a,ha,rfl⟩ := hx
  by_contra ha1
  have ha1' : a ≠ 1 := fun he => ha1 (by rw [he,map_one])
  have hconj : e.symm g * a * (e.symm g)⁻¹ ∈ Z := by
    apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using hgx
  have hn := hZ.mem_normalizer_of_conj_mem ha ha1' hconj
  apply hg
  exact Z.le_normalizer_map e.toMonoidHom
    ⟨e.symm g,hn,e.apply_symm_apply g⟩

theorem IsTISubgroup.eq_or_disjoint_conjugate {Z : Subgroup G}
    (hZ : IsTISubgroup Z) (g : G) :
    Z.map (MulAut.conj g).toMonoidHom = Z ∨
      Disjoint (Z.map (MulAut.conj g).toMonoidHom) Z := by
  by_cases hg : g ∈ normalizer (Z : Set G)
  · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hg)
  · right
    apply disjoint_def.mpr
    rintro x ⟨a,ha,rfl⟩ hx
    have ha1 := (isTISubgroup_iff Z).mp hZ g hg a ha hx
    simp only [ha1,map_one]

/-- Equal-order elementary TI conjugates in a two-group commute as soon as
the conjugate is larger than the index of the first subgroup's normalizer.
This is the local I.6.2 step used in original 2.4.19. -/
theorem IsTISubgroup.conjugate_le_centralizer_of_index [Finite G]
    (Z T : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZ : IsTISubgroup Z) (hT : IsPGroup 2 T) (hZT : Z ≤ T)
    (hi : (normalizer (Z : Set G)).relIndex T < Nat.card Z)
    (g : G) (hgT : Z.map (MulAut.conj g).toMonoidHom ≤ T) :
    Z.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) := by
  let E := Z.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hc : Nat.card E = Nat.card Z := card_map_of_injective (MulAut.conj g).injective
  rcases hZ.eq_or_disjoint_conjugate g with he | hd
  · rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hn : E ⊓ normalizer (Z : Set G) ≠ ⊥ := by
    intro hh
    have hb := relIndex_le_of_le_right (H := normalizer (Z : Set G)) hgT
      (show (normalizer (Z : Set G)).relIndex T ≠ 0 from index_ne_zero_of_finite)
    rw [← inf_relIndex_right, inf_comm,hh,relIndex_bot_left,hc] at hb
    exact (not_lt_of_ge hb) hi
  exact (ti_pair_directProduct_of_isPGroup E Z hd (hZ.map_equiv (MulAut.conj g)) hZ hc hn
    (hT.to_le (sup_le hgT hZT))).1
end CFSG.Quasithin.ChapterI.Section06To08
