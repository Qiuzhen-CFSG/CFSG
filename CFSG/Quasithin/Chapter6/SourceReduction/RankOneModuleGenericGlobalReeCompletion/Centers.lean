module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRootFusion
public import Theory.SpecificGroups.ReeF4.SourceCompletion.Centers

/-!
# Original Ree long-root centralizers and TI geometry

The right parabolic comparison transports the native torus orbit on the
long-root center to the center of the whole original residual O²(H).
Characteristic two puts this center inside T. Its T-invariance supplies a
Sylow-central involution, whose ambient centralizer is controlled by the
original uniqueness theorem. Transitivity gives the full centralizer bound
for every central involution of the residual. The resulting center is
nontrivial, elementary abelian and TI, with normalizer exactly N_G(O²(H)).

This proves the long-root input to 5.3.3 and F.4.34 at every positive Ree
parameter. The generic transport and orbit lemmas are reused read-only.
Compatible extension to the native model, involution nonfusion, short-root
centralizer control and the full-extension order comparison remain open.
Source: Aschbacher–Smith, printed pp.659,291 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

/-- The actual right parabolic is transitive on the nonidentity residual center. -/
theorem Preparation.ree_right_center_orbit
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    ∀ x ∈ (center (residual H)).map (residual H).subtype, x ≠ 1 →
      ∀ y ∈ (center (residual H)).map (residual H).subtype, y ≠ 1 →
        ∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
          y = g*x*g⁻¹ := by
  rcases he with he | he
  · exact (d.not_ree_unreversed h hTH hp m he).elim
  obtain ⟨e⟩ := he
  have hm := d.ree_parameter_positive h hp m 1 .suzuki e.right
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  have hres : (residual H).subgroupOf P = solvableResidual P := by
    have hr : (solvableResidual P).map P.subtype = residual H :=
      d.parabolic_residuals h hTH hp 1
    rw [←hr]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  apply center_orbit_transport (R := ReeF4.Parabolics.localFactor m .suzuki) hKP e.right
  · rw [hres,←map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
    exact ReeF4.Parabolics.parabolic_solvableResidual_map hm .suzuki
  · intro x hx hx1 y hy hy1
    exact ReeF4.SourceCompletion.suzuki_center_orbit hm x y hx hy hx1 hy1

/-- The full ambient centralizer of each central involution in either original
factor lies in its full normalizer, as required by source 5.3.3. -/
theorem Preparation.ree_central_involution_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  intro i
  fin_cases i
  · exact d.left_central_involution_centralizer
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hK := d.ree_right_maximal h hH hp m he
  have hu := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_unique
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK)
      (le_componentOrbit _ _)
  rw [ho] at hu
  have hc := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) hK.1
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  exact center_orbit_centralizer_bound hTK hc hPN hu
    (d.ree_right_center_orbit h hH.1.1.2 hp m he)

/-- The right center is nontrivial; its involution has the full ambient
centralizer bound, with no supplied root or centralizer premise. -/
theorem Preparation.ree_right_center_involution
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    ∃ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 ∧
      centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) := by
  have hc := d.ree_central_involution_centralizers h hH hp m he 1
  rcases he with he | he
  · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
  obtain ⟨e⟩ := he
  obtain ⟨_,hm,_,⟨a⟩,_⟩ := d.ree_local_structure h hH.1.1.2 hp m e
  obtain ⟨z,hz⟩ := ReeF4.SourceCompletion.suzuki_center_involution hm
  let x := (centerCongr a).symm z
  have hx : (x.val : G) ∈ (center (residual H)).map (residual H).subtype :=
    mem_map_of_mem _ x.property
  have hx2 : orderOf (x.val : G) = 2 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact ((centerCongr a).symm.orderOf_eq z).trans hz
  exact ⟨x.val,hx,hx2,hc x.val hx hx2⟩

/-- F.4.34 for the original general Ree pair: its nontrivial right center
is elementary abelian and TI, and has exactly the full right normalizer. -/
theorem Preparation.ree_right_center_fusion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    IsElementaryAbelian 2 ((center (residual H)).map (residual H).subtype) ∧
    IsTISubgroup ((center (residual H)).map (residual H).subtype) ∧
    normalizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) =
      normalizer (residual H : Set G) := by
  obtain ⟨z,hz,hz2,_⟩ := d.ree_right_center_involution h hH hp m he
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  exact center_orbit_fusion hPN ⟨z,hz,hz2⟩
    (d.ree_right_center_orbit h hH.1.1.2 hp m he)
    (d.ree_central_involution_centralizers h hH hp m he 1)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
