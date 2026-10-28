module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourOrbits
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Nonfusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Centralizers

/-!
# The two inner involution classes in the prepared unitary-four branch

The native plane core has two orbits under its full parabolic, by explicit
Hermitian elimination and fixed-field torus conjugation. The original
faithful-left hypothesis excludes the opposite endpoint orientation.
Restriction to the actual solvable residuals transports the two orbits to
O₂(L), with conjugators in N_G(L). The accepted Hermitian nonfusion result
proves that those two orbits remain distinct under the ambient group G.

Using both squares of the whole amalgam comparison, point conjugation now
places each involution of the reduced common Sylow T ∩ L specifically in
O₂(L). Thus exactly two ambient classes meet that reduced Sylow. Both
ordinary and degree-two comparisons are retained. In the latter case the
ordinary comparison is the proved residual restriction, with its full
reduced overlap; the original sourceS and ambient T are not redefined.

These are the inner-class coverage and nonfusion steps of Aschbacher–Smith
F.4.35, printed p.292 of `refs/quasithin.pdf`. Concrete simultaneous
full-normalizer realization, outer transfer, F.4.42 containment and the
full-extension order comparison remain further source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
namespace UnitarySource
variable {G : Type*} [Group G] [Finite G]
private theorem reverse_comparison (P : Fin 2 → Subgroup G) (L R : Subgroup G)
    (hL : faithfulLocal L)
    (hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,R] i)
    (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
    (b : R ≃* PointLocal.ProjectiveLocal m hm)
    (hz : (center (pCore 2 R)).map (pCore 2 R).subtype ≤ center R)
    (he : Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
        (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
        (amalgam m hm).reverse)) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (amalgam m hm).reverse) := by
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · let a : solvableResidual (P 0) ≃* L :=
      ((solvableResidual (P 0)).equivMapOfInjective (P 0).subtype
        (P 0).subtype_injective).trans (MulEquiv.subgroupCongr (hr 0))
    let c : solvableResidual (pointParabolic m hm) ≃* PointLocal.ProjectiveLocal m hm :=
      ((solvableResidual (pointParabolic m hm)).equivMapOfInjective
        (pointParabolic m hm).subtype (pointParabolic m hm).subtype_injective).trans
          (MulEquiv.subgroupCongr (PointLocal.pointParabolic_solvableResidual m hm hm'))
    exact (faithful_not_core_center_central hL
      (a.symm.trans (e.left.solvableResidualEquiv.trans (c.trans b.symm))) hz).elim
  · exact ⟨e⟩

private theorem residual_core_orbits (P L : Subgroup G)
    (hr : (solvableResidual P).map P.subtype = L)
    (m : ℕ) (hm : 1 ≤ m) [NeZero m] (e : P ≃* planeParabolic m hm) :
    ∃ z ∈ L.pCoreIn 2, ∃ t ∈ L.pCoreIn 2,
      z ≠ 1 ∧ t ≠ 1 ∧ ∀ x ∈ L.pCoreIn 2, x ≠ 1 →
        ∃ g ∈ normalizer (L : Set G), g*x*g⁻¹ = z ∨ g*x*g⁻¹ = t := by
  have hLP : L ≤ P := hr ▸ map_subtype_le _
  have hn : P ≤ normalizer (L : Set G) := by
    rw [←hr]
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (solvableResidual P).le_normalizer_map P.subtype
  have heq : P.pCoreIn 2 = L.pCoreIn 2 :=
    le_antisymm (ChapterF.UnitarySource.FourPlacement.plane_comparison_core_le_residual_core
      m hm P L e hr) (pCoreIn_mono_of_normalizes hLP hn)
  obtain ⟨z,hz,t,ht,hz1,ht1,hcov⟩ :=
    ChapterF.UnitarySource.FourOrbits.planeCore_two_orbits_transport m hm P e
  rw [heq] at hz ht hcov
  refine ⟨z,hz,t,ht,hz1,ht1,?_⟩
  intro x hx hx1
  obtain ⟨g,hg,hgx⟩ := hcov x hx hx1
  exact ⟨g,hn hg,hgx⟩
end UnitarySource

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original left core has at most two nonidentity orbits under N_G(L).
The torus actors are constructed in the actual ordinary/reduced parabolic. -/
theorem Preparation.unitary_core_two_orbits
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    ∃ z ∈ L.pCoreIn 2, ∃ t ∈ L.pCoreIn 2,
      z ≠ 1 ∧ t ≠ 1 ∧ ∀ x ∈ L.pCoreIn 2, x ≠ 1 →
        ∃ g ∈ normalizer (L : Set G), g*x*g⁻¹ = z ∨ g*x*g⁻¹ = t := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨hm',_,_,⟨b⟩,_⟩ := hc.elim
    (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  have hz := (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.2.2.2.2.2.2.2
  rcases hc with ho | he
  · obtain ⟨e⟩ := UnitarySource.reverse_comparison _ L (residual H) h.local_mem.2
      (d.parabolic_residuals h hH.1.1.2 hp) m hm hm' b hz ho
    exact UnitarySource.residual_core_orbits _ L
      (d.parabolic_residuals h hH.1.1.2 hp 0) m hm e.left
  · have hred := d.unitaryExtension_reduced_amalgam h hH.1.1.2 hp m hm' he
    obtain ⟨e⟩ := UnitarySource.reverse_comparison _ L (residual H) h.local_mem.2
      (d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryExtension m hm he))
      m hm hm' b hz hred
    exact UnitarySource.residual_core_orbits _ L
      (d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryExtension m hm he) 0) m hm e.left

/-- Every involution in the reduced common Sylow is conjugate into the original
left core. The conjugator lies in the full-normalizer join. -/
theorem Preparation.unitary_inner_involution_to_left_core
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (x : G) (hx : x ∈ (T : Subgroup G) ⊓ L) (hx2 : x^2 = 1) :
    ∃ g ∈ NormalizerJoin L (residual H), g*x*g⁻¹ ∈ L.pCoreIn 2 := by
  obtain ⟨hm',_,_,⟨b⟩,_⟩ := hc.elim
    (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  have hz := (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.2.2.2.2.2.2.2
  have transfer (P : Fin 2 → Subgroup G)
      (hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,residual H] i)
      (he : Nonempty (RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
          (amalgam m hm)) ∨
        Nonempty (RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
          (amalgam m hm).reverse))
      (hxp : x ∈ P 0 ⊓ P 1) :
      ∃ g ∈ NormalizerJoin L (residual H), g*x*g⁻¹ ∈ L.pCoreIn 2 := by
    obtain ⟨e⟩ := UnitarySource.reverse_comparison P L (residual H) h.local_mem.2 hr
      m hm hm' b hz he
    let swap : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (P 1) (P 1 ⊓ P 0) (P 0) inf_le_left inf_le_right)
        (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right).reverse := {
      left := MulEquiv.refl _
      right := MulEquiv.refl _
      middle := MulEquiv.subgroupCongr (inf_comm _ _)
      left_commutes _ := rfl
      right_commutes _ := rfl }
    obtain ⟨g,hg,hgc⟩ := ChapterF.UnitarySource.FourPlacement.comparison_involution_to_core
      m hm (P 1) (P 0) (swap.trans e.reverse) x ⟨hxp.2,hxp.1⟩ hx2
    have hn : P 1 ≤ normalizer (residual H : Set G) := by
      have hr1 : (solvableResidual (P 1)).map (P 1).subtype = residual H := hr 1
      rw [←hr1]
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
        (solvableResidual (P 1)).le_normalizer_map (P 1).subtype
    exact ⟨g,(hn.trans le_sup_right) hg,
      ChapterF.UnitarySource.FourPlacement.plane_comparison_core_le_residual_core
        m hm (P 0) L e.left (hr 0) hgc⟩
  have hxi (i : Fin 2) :
      x ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i :=
    (show (T : Subgroup G) ⊓ L ≤ _ from le_sup_right.trans le_sup_left) hx
  rcases hc with ho | he
  · have hle (i : Fin 2) :
        ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i ≤
          ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i := by
      rw [d.reduced_source_parabolics h hH.1.1.2 hp (.unitary m hm ho) i]
      exact map_subtype_le _
    exact transfer _ (d.parabolic_residuals h hH.1.1.2 hp) ho
      ⟨hle 0 (hxi 0),hle 1 (hxi 1)⟩
  · exact transfer _
      (d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryExtension m hm he))
      (d.unitaryExtension_reduced_amalgam h hH.1.1.2 hp m hm' he) ⟨hxi 0,hxi 1⟩

/-- Exactly two ambient classes meet the reduced common Sylow. Both have
representatives in O₂(L), and remain distinct in the original G. -/
theorem Preparation.unitary_inner_two_classes
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    ∃ z ∈ L.pCoreIn 2, ∃ t ∈ L.pCoreIn 2,
      orderOf z = 2 ∧ orderOf t = 2 ∧ ¬ IsConj z t ∧
        ∀ x ∈ (T : Subgroup G) ⊓ L, orderOf x = 2 → IsConj x z ∨ IsConj x t := by
  obtain ⟨z,hz,t,ht,hz1,ht1,hcov⟩ := d.unitary_core_two_orbits h hH hp m hm hc
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.1
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  have order_two (x : G) (hx : x ∈ L.pCoreIn 2) (hx1 : x ≠ 1) : orderOf x = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hx1
  have classes (x : G) (hx : x ∈ L.pCoreIn 2) (hx1 : x ≠ 1) : IsConj x z ∨ IsConj x t := by
    obtain ⟨g,_,hg⟩ := hcov x hx hx1
    exact hg.elim (fun he => Or.inl (isConj_iff.mpr ⟨g,he⟩))
      (fun he => Or.inr (isConj_iff.mpr ⟨g,he⟩))
  have hzt : ¬ IsConj z t := by
    intro hzt
    obtain ⟨a,ha,b,hb,ha2,hb2,hab⟩ :=
      d.unitary_core_two_nonconjugate_involutions h hH hp m hm hc
    have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
    have hb1 : b ≠ 1 := by intro he; simp [he] at hb2
    have hat : IsConj a t := (classes a ha ha1).elim (fun hh => hh.trans hzt) id
    have hbt : IsConj b t := (classes b hb hb1).elim (fun hh => hh.trans hzt) id
    exact hab (hat.trans hbt.symm)
  refine ⟨z,hz,t,ht,order_two z hz hz1,order_two t ht ht1,hzt,?_⟩
  intro x hx hx2
  obtain ⟨g,_,hg⟩ := d.unitary_inner_involution_to_left_core h hH hp m hm hc x hx
    (hx2 ▸ pow_orderOf_eq_one x)
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx2
  have hy1 : g*x*g⁻¹ ≠ 1 := by
    intro he
    apply hx1
    exact (MulAut.conj g).injective (he.trans (map_one _).symm)
  have hxy : IsConj x (g*x*g⁻¹) := isConj_iff.mpr ⟨g,rfl⟩
  exact (classes _ hg hy1).elim (fun hh => Or.inl (hxy.trans hh))
    (fun hh => Or.inr (hxy.trans hh))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
