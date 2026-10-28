module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineLocalResidual

/-!
# The ordinary PSL₃(2) exclusion from actual local residual control

The original central omega subgroup supplies a nontrivial marked involution.
For an ordinary PSL₃(2) component its marked automorphism is inner and its
full automorphism centralizer is a two-group. The actual two-perfect residual
of M_Z must therefore centralize that component. Its given full-normalizer
bound contradicts the original component escape.

Only the two explicit local controls are needed: the partner centralizes
the original central seed, and the full normalizer of the marked residual
lies in that partner. No Nine row or global 15.1.14 conclusion is assumed.

Source: Aschbacher--Smith 15.1.18--20, printed pp.1092--1097.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem pslThreeTwo_inner
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Matrix.PSL3Two.PSL)
    {α : MulAut d.L} (hm : ModelAction115 d.L α) :
    α ∈ (MulAut.conj (G := d.L)).range := by
  have hcard : Nat.card d.L = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hnot (n : ℕ) (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n)) :
      ¬ AlternatingAction α n σ := by
    rintro (⟨f,_⟩ | ⟨_,⟨f⟩,_⟩)
    · have hh := Nat.card_congr f.toEquiv
      rcases hn with rfl | rfl <;>
        rw [hcard,nat_card_alternatingGroup,Nat.card_fin] at hh <;> norm_num at hh
    · have hh : Nat.card (center d.L) = 3 := by simpa using Nat.card_congr f.toEquiv
      rcases (s.ordinary hL).center_two.card_eq_or_dvd with h1 | h2
      · omega
      · norm_num [hh] at h2
  cases hm with
  | lie _ _ hi => exact hi
  | two_cover _ _ _ hi => exact hi
  | six σ _ ha => exact (hnot 6 (Or.inl rfl) σ ha).elim
  | seven σ _ ha => exact (hnot 7 (Or.inr rfl) σ ha).elim
  | odd _ hi => exact hi
  | sporadic _ _ _ ha => exact ha.1

/-- An actual ordinary PSL₃(2) component contradicts the two local marked
residual controls, independently of the chosen action row. -/
theorem PreExclusionSource.false_of_pslThreeTwo_equiv_of_local_control
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hMcC : Mc ≤ centralizer (centralInvolutions T : Set G))
    (hNY : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Matrix.PSL3Two.PSL) : False := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,hm⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  have hi := pslThreeTwo_inner (h := h) s hL e hm
  have hzL : center d.L = ⊥ := by
    apply (center d.L).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr (e.trans Matrix.PSL3Two.equiv.symm)).toEquiv,
      Matrix.PSL3Two.center_eq_bot,card_bot]
  obtain ⟨t,ht⟩ := hi
  have hα2 : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change (α (α l) : G) = (l : G)
    rw [ha,ha]
    have hz2 := (mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.1
    have hzz : z*z=1 := by simpa only [pow_two] using hz2
    calc
      z*(z*(l : G)*z⁻¹)*z⁻¹ = (z*z)*(l : G)*(z*z)⁻¹ := by group
      _ = _ := by rw [hzz]; simp
  have hαne : α ≠ 1 := by
    intro he
    apply hzne
    apply mem_bot.mp
    rw [←(s.ordinary hL).central_faithful]
    refine ⟨hz,?_⟩
    intro l hl
    have hh := ha ⟨l,hl⟩
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have ht2 : orderOf t = 2 := by
    rw [←orderOf_injective _ (MulAut.conj_injective_of_center_eq_bot hzL) t,ht]
    exact orderOf_eq_prime hα2 hαne
  apply d.false_of_twoGroup_marked_centralizer_local h hG hMcC hNY hz α ha
  rw [←ht]
  apply MulAut.isPGroup_centralizer_conj_of_outer hzL
    (Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
      (MulAut.outerCongr (e.trans Matrix.PSL3Two.equiv.symm)).symm)
  let f : centralizer ({t} : Set d.L) →* centralizer ({e t} : Set Matrix.PSL3Two.PSL) :=
    (e.toMonoidHom.comp (centralizer ({t} : Set d.L)).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      exact (map_mul e _ _).symm.trans
        ((congrArg e (mem_centralizer_singleton_iff.mp x.property)).trans (map_mul e _ _)))
  exact (Matrix.PSL3Two.InvolutionResidual.centralizer_two (e t)
    ((e.orderOf_eq t).trans ht2)).of_injective f
      (fun a b hh => Subtype.ext (e.injective (congrArg Subtype.val hh)))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
