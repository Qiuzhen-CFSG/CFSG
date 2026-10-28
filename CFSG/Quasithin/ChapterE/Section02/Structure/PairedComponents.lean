module
public import CFSG.Quasithin.ChapterE.Section02.Structure.CoreLayer
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.PGroup.IndexTwoElementaryConjugate
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.ConjugateSpanSylow
/-!
# The original normal-or-paired component reduction

The odd-prime rank bound permits at most two conjugate components.
An actual Sylow element outside the component normalizer exchanges the
pair, whose commuting join is the two-residual. In the core-free source
setting the components are simple and multiplication gives their exact
internal direct product. Additivity of prime rank then bounds every odd
prime rank of either factor by one. The Sylow orbit identity supplies the
literal automizer input used to construct the paired Bender witnesses.

Source: Aschbacher–Smith E.2.2, printed pp.215–216, and E.2.7, p.218.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

/-- The actual Sylow orbit of the selected source component is the two-residual. -/
theorem generating_component_orbit_eq_residual (hH : IsStronglyQuasithin H)
    (T : Sylow 2 H) {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    componentOrbit K (T : Subgroup H) = pResidual 2 H := by
  have he : componentOrbit K (T : Subgroup H) = conjugateSpanBy K (T : Subgroup H) := by
    rw [conjugateSpanBy_eq_iSup_conj]
    rfl
  have hn : (componentOrbit K (T : Subgroup H)).Normal := by
    rw [he]
    exact conjugateSpanBy_sylow_normal K T (hK.normal_or_index_two_of_odd_rank_le_two hH)
  let := hn
  apply le_antisymm
  · rw [residual_eq_layer T hK hgen]
    exact iSup_le fun t : T => le_sSup (hK.map_conj t)
  · have hOT : componentOrbit K (T : Subgroup H) ⊔ (T : Subgroup H) = ⊤ := top_unique (by
      rw [← hgen]
      exact sup_le_sup (le_componentOrbit K (T : Subgroup H)) le_rfl)
    exact sInf_le ⟨hn,isPGroup_quotient_of_sup_eq_top _ (T : Subgroup H) T.isPGroup' hOT⟩

/-- The literal two-factor alternative for an original generating component. -/
theorem component_normal_or_pair (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    (K.Normal ∧ pResidual 2 H = K) ∨
      ∃ t : T, let D := K.map (MulAut.conj (t:H)).toMonoidHom
        D ≠ K ∧ IsComponent H D ∧
        ⁅K,D⁆ = ⊥ ∧ (K ⊔ D).Normal ∧ pResidual 2 H = K ⊔ D ∧
        D.map (MulAut.conj (t:H)).toMonoidHom = K ∧
        (normalizer (K : Set H)).index = 2 := by
  rcases hK.normal_or_index_two_of_odd_rank_le_two hH with hn | hi
  · let := hn
    exact Or.inl ⟨hn,(residual_eq_layer T hK hgen).trans (layer_eq_normal_component T hK hgen)⟩
  · have hnot : ¬ (T : Subgroup H) ≤ normalizer (K : Set H) := by
      intro h
      have hd := index_dvd_of_le h
      rw [hi] at hd
      exact T.not_dvd_index hd
    obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hnot
    let D := K.map (MulAut.conj t).toMonoidHom
    have hd : D ≠ K := by
      intro he
      exact htn (mem_normalizer_iff_map_conj_eq.mpr he)
    have hD := hK.map_conj t
    have hN : (K ⊔ D).Normal := sup_conjugate_normal_of_normalizer_index_two K hi t htn
    let := hN
    have hNT : (K ⊔ D) ⊔ (T : Subgroup H) = ⊤ := top_unique (by
      rw [← hgen]
      exact sup_le_sup le_sup_left le_rfl)
    have hR : pResidual 2 H = K ⊔ D := by
      apply le_antisymm
      · exact sInf_le ⟨hN,isPGroup_quotient_of_sup_eq_top (K ⊔ D) (T : Subgroup H) T.isPGroup' hNT⟩
      · rw [residual_eq_layer T hK hgen]
        exact sup_le (le_sSup hK) (le_sSup hD)
    have hswap : D.map (MulAut.conj t).toMonoidHom = K := by
      have hmaps : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          (MulAut.conj (t^2)).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,pow_two]
        group
      change (K.map _).map _ = K
      rw [map_map,hmaps]
      exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (K : Set H)).sq_mem_of_index_two hi t)
    exact Or.inr ⟨⟨t,ht⟩,hd,hD,hK.commutator_eq_bot_of_ne hD hd.symm,hN,hR,hswap,hi⟩

/-- In the actual core-free source setting the component selected in E.2.2 is simple. -/
theorem source_core_free_component {κ : GroupClass} (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hJ : ChapterB.minimalParabolicCore T hP = ⊥) :
    ∃ K : Subgroup H, IsComponent H K ∧ K.IsCComponent ∧ IsSimpleGroup K ∧
      ¬ IsMulCommutative K ∧ K ⊔ (T : Subgroup H) = ⊤ ∧
      ((K.Normal ∧ pResidual 2 H = K) ∨
        ∃ t : T, let D := K.map (MulAut.conj (t:H)).toMonoidHom
          D ≠ K ∧ IsComponent H D ∧ ⁅K,D⁆ = ⊥ ∧ (K ⊔ D).Normal ∧
          pResidual 2 H = K ⊔ D ∧ D.map (MulAut.conj (t:H)).toMonoidHom = K ∧
          (normalizer (K : Set H)).index = 2) := by
  have hO : pCore 2 H = ⊥ := bot_unique (hJ ▸ ChapterB.minimalParabolicTwoCore_le_core T hP)
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  obtain ⟨K,hK,hC,hgen⟩ := exists_generating_quasisimple_component hH T hP hs hO
  exact ⟨K,hK,hC,hC.isSimpleGroup_of_solvableRadical_eq_bot hrad,
    hC.not_isMulCommutative_of_solvableRadical_eq_bot hrad,hgen,
    component_normal_or_pair hH.stronglyQuasithin T hK hgen⟩
/-- The actual swapped factor has odd-prime rank at most one. -/
theorem paired_component_odd_rank_le_one
    (hH : IsStronglyQuasithin H) (hrad : solvableRadical H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    (t : H) (hne : K.map (MulAut.conj t).toMonoidHom ≠ K) :
    ∀ p : ℕ, p.Prime → Odd p → primeRank p K ≤ 1 := by
  let D := K.map (MulAut.conj t).toMonoidHom
  have hcomm : ⁅K,D⁆ = ⊥ := hK.commutator_eq_bot_of_ne (hK.map_conj t) hne.symm
  have hd : Disjoint K D := hC.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hrad hcomm
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hr := primeRank_sup_eq_add_of_disjoint_commuting K D hd
    (commutator_eq_bot_iff_le_centralizer.mp hcomm) p
  have he : primeRank p K = primeRank p D :=
    Theory.GroupTheory.primeRank_equiv p ((MulAut.conj t).subgroupMap K)
  have hu : primeRank p (K ⊔ D : Subgroup H) ≤ 2 :=
    (primeRank_subgroup_le p (K ⊔ D)).trans (hH p hp ho)
  omega

/-- Original E.2.2 pair coordinates, with multiplication and the rank restriction preserved. -/
theorem source_pair_coordinates (hH : IsStronglyQuasithin H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    ∃ t : T, let D := K.map (MulAut.conj (t:H)).toMonoidHom
      D ≠ K ∧ IsSimpleGroup D ∧ IsComponent H D ∧
      pResidual 2 H = K ⊔ D ∧
      (∃ e : K × D ≃* (K ⊔ D : Subgroup H),
        ∀ k d, (e (k,d) : H) = (k:H)*(d:H)) ∧
      D.map (MulAut.conj (t:H)).toMonoidHom = K ∧
      (∀ p : ℕ, p.Prime → Odd p → primeRank p K ≤ 1) := by
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  rcases component_normal_or_pair hH T hK hgen with h | ⟨t,hne,hD,hcomm,_,hR,hswap,_⟩
  · exact (hn h.1).elim
  · have hsD := isSimpleGroup_of_isQuasisimple_of_solvableRadical_eq_bot hrad hD.1
        (hq := hD.2)
    exact ⟨t,hne,hsD,hD,hR,
      hC.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hrad hcomm,hswap,
      paired_component_odd_rank_le_one hH hrad hK hC t hne⟩
end CFSG.Quasithin.ChapterE.Structure
