module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.CoreCenters
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.LineCenter
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRootFusion

/-!
# Ambient long-root centralizers and TI geometry for U₅(4)

The actual right endpoint map transports the native cubic orbit to the center
of the whole residual O²(H). Original nonsolvable uniqueness bounds the
centralizer of a Sylow-central involution by its full normalizer, and the
transported orbit extends this bound to every central involution. The center
has order four, so Cauchy's theorem supplies an involution. The orbit and
centralizer bounds then give elementary abelianity, the TI property and the
exact ambient normalizer of the whole center.

These prove the long-root hypothesis of F.4.31(b) and its F.4.34 consequence
from the original prepared row, with both comparison orientations retained.
They do not assert nonfusion with the short-root class or T = S.
Source: Aschbacher--Smith 5.3.3(b), F.4.31(b) and F.4.34, printed pp.659,291.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The whole original line residual has center of order four. -/
theorem Preparation.unitaryFive_right_center_card
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    Nat.card (center (residual H)) = 4 := by
  rcases hc with ho | hr
  · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
  obtain ⟨e⟩ := hr
  obtain ⟨_,_,⟨b⟩,_⟩ := d.unitaryFive_local_structure h hH.1.1.2 hp U e
  exact (Nat.card_congr (centerCongr b).toEquiv).trans U.leftLocalImage_center_card

/-- The original right source parabolic is transitive on the nonidentity center. -/
theorem Preparation.unitaryFive_right_center_orbit
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    ∀ x ∈ (center (residual H)).map (residual H).subtype, x ≠ 1 →
      ∀ y ∈ (center (residual H)).map (residual H).subtype, y ≠ 1 →
        ∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
          y = g*x*g⁻¹ := by
  rcases hc with ho | hr
  · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
  obtain ⟨e⟩ := hr
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  apply center_orbit_transport (show residual H ≤ P from le_sup_left.trans le_sup_left)
    e.right (R := U.leftLocalImage)
  · have hres : (residual H).subgroupOf P = solvableResidual P := by
      have he : (solvableResidual P).map P.subtype = residual H :=
        d.parabolic_residuals h hH.1.1.2 hp 1
      rw [←he]
      exact comap_map_eq_self_of_injective P.subtype_injective _
    rw [hres,←map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
    rfl
  · exact U.leftLocalImage_center_orbit

/-- Original uniqueness and the constructed orbit give the full ambient centralizer bounds. -/
theorem Preparation.unitaryFive_central_involution_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  intro i
  fin_cases i
  · exact d.left_central_involution_centralizer
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hK := d.unitaryFive_right_maximal h hH hp U hc
  have hu := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_unique
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK)
      (le_componentOrbit _ _)
  rw [ho] at hu
  have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) hK.1
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  exact center_orbit_centralizer_bound hTK hchar hPN hu
    (d.unitaryFive_right_center_orbit h hH hp U hc)

/-- The original long-root group is elementary abelian, TI, and has the full right normalizer. -/
theorem Preparation.unitaryFive_right_center_fusion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    IsElementaryAbelian 2 ((center (residual H)).map (residual H).subtype) ∧
      ChapterI.Section06To08.IsTISubgroup ((center (residual H)).map (residual H).subtype) ∧
      normalizer ((center (residual H)).map (residual H).subtype : Set G) =
        normalizer (residual H : Set G) := by
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  have hz : ∃ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 := by
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (residual H)) 2
      (by rw [d.unitaryFive_right_center_card h hH hp U hc]; decide)
    exact ⟨z.val.val,⟨z.val,z.property,rfl⟩,by simpa only [Subgroup.orderOf_coe] using hz⟩
  exact center_orbit_fusion hPN hz (d.unitaryFive_right_center_orbit h hH hp U hc)
    (d.unitaryFive_central_involution_centralizers h hH hp U hc 1)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
