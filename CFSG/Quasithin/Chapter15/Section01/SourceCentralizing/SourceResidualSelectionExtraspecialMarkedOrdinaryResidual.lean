module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableOrdinaryLinear

/-!
# Ordinary small-component exclusion from the actual marked residual

Only the embedded two-residual of M_Z must centralize the original seed.
Its two-perfect image in a marked automorphism centralizer is trivial when
that centralizer is a two-group. The original residual-normalizer bound
then contradicts component escape. Apply this to the PSL₃(2) component.
No assertion that the entire partner centralizes the seed is required.
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

/-- A two-group marked automorphism centralizer is incompatible with the
local residual's normalizer bound and the actual component escape. -/
theorem false_of_twoGroup_marked_centralizer_of_residual_seed
    (d : CaseIComponentData T M Mc V) (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hYseed : (pResidual 2 d.MZ).map d.MZ.subtype ≤
      centralizer (centralInvolutions T : Set G))
    (hNY : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    {z : G} (hz : z ∈ centralInvolutions T)
    (α : MulAut d.L) (ha : ∀ x : d.L, (α x : G) = z*x*z⁻¹)
    (hp : IsPGroup 2 (centralizer ({α} : Set (MulAut d.L)))) : False := by
  let Y := (pResidual 2 d.MZ).map d.MZ.subtype
  let N := normalizer (d.L : Set G)
  let f := d.L.normalizerMonoidHom
  have hYN : Y ≤ N := d.markedResidual_normalizes_component h hG
  let a : Y →* MulAut d.L := f.comp (inclusion hYN)
  have hac : ∀ y : Y, a y ∈ centralizer ({α} : Set (MulAut d.L)) := by
    intro y
    apply mem_centralizer_singleton_iff.mpr
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change (y : G)*(α l : G)*(y : G)⁻¹ = (α (f (inclusion hYN y) l) : G)
    rw [ha,ha]
    change (y : G)*(z*(l : G)*z⁻¹)*(y : G)⁻¹ = z*((y : G)*(l : G)*(y : G)⁻¹)*z⁻¹
    have hyz : z*(y : G) = (y : G)*z := hYseed y.property z hz
    calc
      (y : G)*(z*(l : G)*z⁻¹)*(y : G)⁻¹ =
          ((y : G)*z)*(l : G)*((y : G)*z)⁻¹ := by group
      _ = (z*(y : G))*(l : G)*(z*(y : G))⁻¹ := by rw [hyz]
      _ = _ := by group
  let b := a.codRestrict (centralizer ({α} : Set (MulAut d.L))) hac
  have hb := (isPPerfect_embedded_pResidual 2 d.MZ).hom_eq_one_of_isPGroup hp b
  have hc : Y ≤ centralizer (d.L : Set G) := by
    intro y hy l hl
    have hy1 : a ⟨y,hy⟩ = 1 := congrArg (fun c : Y →* centralizer ({α} : Set (MulAut d.L)) =>
      (c ⟨y,hy⟩ : MulAut d.L)) hb
    have he := congrArg Subtype.val (DFunLike.congr_fun hy1 (⟨l,hl⟩ : d.L))
    change y*l*y⁻¹=l at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply d.L_not_le_MZ
  exact le_inf d.L_component.1 (((le_centralizer_iff.mp hc).trans
    (Subgroup.centralizer_le_normalizer _)).trans hNY)

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
theorem PreExclusionSource.false_of_pslThreeTwo_equiv_of_residual_seed
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hYseed : (pResidual 2 d.MZ).map d.MZ.subtype ≤
      centralizer (centralInvolutions T : Set G))
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
  apply d.false_of_twoGroup_marked_centralizer_of_residual_seed h hG hYseed hNY hz α ha
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
