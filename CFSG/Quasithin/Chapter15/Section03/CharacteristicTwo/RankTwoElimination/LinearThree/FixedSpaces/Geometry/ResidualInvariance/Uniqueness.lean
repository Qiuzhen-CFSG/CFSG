module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.Basic
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
/-!
# The unique relative C-component containing the moving residual

Distinct C-components normalize each other. Their intersection is a proper
normal, hence solvable, subgroup of either component. For the actual binary
linear-three quotient, its image is a solvable normal subgroup of a centerless
quasisimple group, so the intersection lies in the two-core. Since that core
centralizes V, a residual moving V cannot be in two distinct C-components.

We apply this inside the actual Thompson subgroup J(I), then transport by
its automorphisms induced by S. Thus normalization of Y_L implies normalization
of L without assuming that L is normal in the ambient group or in I.

Source: Aschbacher–Smith 15.3.23, printed p.1128 (combined manuscript,
1 March 2004), using the relative C-component calculus A.3.3.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance
variable {G : Type*} [Group G] [Finite G]

private theorem unique_component_of_not_le_core {K B : Subgroup G}
    (hK : K.IsCComponent) (hBK : B ≤ K) (hB : ¬ B ≤ K.pCoreIn 2)
    [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hcenter : center (K ⧸ pCore 2 K) = ⊥) :
    ∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K := by
  intro D hD hBD
  by_contra hne
  have hKD : K ≤ normalizer (D : Set G) :=
    (le_cComponentLayer hK).trans (cComponentLayer_le_normalizer hD)
  let N := D.subgroupOf K
  let : N.Normal := normal_subgroupOf_of_le_normalizer hKD
  have hproper : N ≠ ⊤ := by
    intro ht
    have hle : K ≤ D := fun k hk => show (⟨k,hk⟩ : K) ∈ N from ht ▸ mem_top _
    exact hne (hK.eq_of_le hD hle).symm
  let : Group.IsSolvable N := hK.isSolvable_of_subnormal_lt_top
    (inferInstance : N.Normal).isSubnormal hproper
  let q := QuotientGroup.mk' (pCore 2 K)
  let : (N.map q).Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  have hqN : N.map q = ⊥ := by
    rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top (N.map q) with hc | ht
    · exact le_bot_iff.mp (hc.trans hcenter.le)
    · have hs : Function.Surjective (q.comp N.subtype) := by
        intro z
        obtain ⟨n,hn,he⟩ := (show z ∈ N.map q from ht ▸ mem_top z)
        exact ⟨⟨n,hn⟩, he⟩
      have hsol : Group.IsSolvable (K ⧸ pCore 2 K) := Group.isSolvable_of_surjective hs
      let : IsSimpleGroup ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) :=
        Theory.GroupTheory.IsQuasisimple.simple
      let : Nontrivial (K ⧸ pCore 2 K) :=
        (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K))).nontrivial
      exact (Group.IsPerfect.not_isSolvable (K ⧸ pCore 2 K) hsol).elim
  have hNcore : N ≤ pCore 2 K := by
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hqN
  apply hB
  intro b hb
  exact mem_map.mpr ⟨⟨b,hBK hb⟩, hNcore (hBD hb), rfl⟩

omit [Finite G] in
private theorem component_quotient_center (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL) :
    center (c.L ⧸ pCore 2 c.L) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply e.injective
  have hm := (centerCongr e) ⟨x,hx⟩ |>.property
  have he : e x = 1 := mem_bot.mp (Matrix.PSL3Two.center_eq_bot ▸ hm)
  simpa using he

/-- The residual moving V belongs to a unique C-component of J(I).
The uniqueness is proved using the actual simple two-core quotient; it is
not an extra local hypothesis. -/
theorem component_unique_over_YL (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (hcore : c.L.pCoreIn 2 ≤ centralizer (d.V : Set G))
    (hne : ⁅d.V,YL d c.L⁆ ≠ ⊥) :
    ∀ D : Subgroup (Stellmacher.elementaryAbelianMaxJ I), D.IsCComponent →
      (YL d c.L).subgroupOf (Stellmacher.elementaryAbelianMaxJ I) ≤ D →
      D = c.L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I) := by
  let J := Stellmacher.elementaryAbelianMaxJ I
  let K := c.L.subgroupOf J
  let eK : K ≃* c.L := subgroupOfEquivOfLe c.le_thompson
  let eQ : (K ⧸ pCore 2 K) ≃* (c.L ⧸ pCore 2 c.L) :=
    QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let := c.core_quotient_quasisimple
  let : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K) :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv eQ.symm
  have hcenter : center (K ⧸ pCore 2 K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply eQ.injective
    have hm := (centerCongr eQ) ⟨x,hx⟩ |>.property
    have he : eQ x = 1 := mem_bot.mp (component_quotient_center d c e ▸ hm)
    simpa using he
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  apply unique_component_of_not_le_core c.component (comap_mono hAL) _ hcenter
  intro hbad
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  apply le_trans _ hcore
  intro a ha
  have haJ : a ∈ J := c.le_thompson (hAL ha)
  obtain ⟨k,hk,hka⟩ := hbad (show (⟨a,haJ⟩ : J) ∈ (YL d c.L).subgroupOf J from ha)
  have hmap := mem_map_of_mem eK.toMonoidHom hk
  rw [pCore_map_iso] at hmap
  refine mem_map.mpr ⟨eK k,hmap,?_⟩
  exact congrArg Subtype.val hka

/-- Normalization of the moving residual forces normalization of its unique
relative C-component. Only J(I), not the ambient group, carries the component. -/
theorem component_normalized_of_YL (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (hcore : c.L.pCoreIn 2 ≤ centralizer (d.V : Set G))
    (hne : ⁅d.V,YL d c.L⁆ ≠ ⊥)
    (hS : d.S ≤ normalizer (YL d c.L : Set G)) :
    d.S ≤ normalizer (c.L : Set G) := by
  let J := Stellmacher.elementaryAbelianMaxJ I
  have hSJ : d.S ≤ normalizer (J : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.elementaryAbelianMaxJ I).map (MulAut.conj s).toMonoidHom = _
    rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv]
    have hi : I.map (MulAut.conj s).toMonoidHom = I :=
      mem_normalizer_iff_map_conj_eq.mp (I.le_normalizer (hI.1.2 (mem_sup_right hs)))
    exact congrArg Stellmacher.elementaryAbelianMaxJ hi
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  apply le_normalizer_iff.mpr
  intro s hs l hl
  let eJ : MulAut J := J.normalizerMonoidHom ⟨s,hSJ hs⟩
  have he : (c.L.subgroupOf J).map eJ.toMonoidHom = c.L.subgroupOf J := by
    apply component_unique_over_YL d c e hcore hne _ (c.component.map_equiv eJ)
    intro b hb
    have hpre : (eJ.symm b : G) ∈ YL d c.L := by
      have hm := (hS (d.S.inv_mem hs) b).mp hb
      change (↑((J.normalizerMonoidHom ⟨s,hSJ hs⟩)⁻¹ b) : G) ∈ YL d c.L
      rw [← map_inv]
      exact hm
    exact mem_map.mpr ⟨eJ.symm b,hAL hpre,eJ.apply_symm_apply b⟩
  have hm := mem_map_of_mem eJ.toMonoidHom
    (show (⟨l,c.le_thompson hl⟩ : J) ∈ c.L.subgroupOf J from hl)
  rw [he] at hm
  exact hm
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance

end
