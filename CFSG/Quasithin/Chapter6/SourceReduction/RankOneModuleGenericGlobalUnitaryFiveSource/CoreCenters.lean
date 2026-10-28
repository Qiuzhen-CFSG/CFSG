module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.PlaneCenter
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveMaximal
public import Theory.GroupTheory.ElementaryThompsonElementaryCore

/-!
# Core centers in the original prepared U₅(4) row

The reversed native comparison identifies the original plane residual L with
the model's actual plane residual. Its canonical core therefore has center
of order `4^4`, equal to its commutator and Frattini subgroup, and every
involution in that core is central. This identifies the Thompson subgroup
of the core itself; it does not identify J(T).

Both original full normalizers are maximal two-local subgroups, using the
published U₅ right-maximality theorem. The nontrivial characteristic centers
of their cores consequently recover those same full normalizers. The
published local normalizer conditions identify the cores on the literal
normalizer endpoints, retaining the whole right residual and both orientations.

Source: Aschbacher--Smith 5.3.3(a), F.4.31(a) and the native input to
F.4.35, printed pp.659,291--292. The Chapter12 companion applies these
results to the original whole-reduced chosen-module input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
open Theory.SpecificGroups.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The actual ambient image of the plane core is special, and its square-one
locus is exactly its elementary center. -/
theorem Preparation.unitaryFive_plane_core_structure
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    let Q := L.pCoreIn 2
    Nat.card (center Q) = 4 ^ 4 ∧ IsElementaryAbelian 2 (center Q) ∧
      center Q = commutator Q ∧ center Q = frattini Q ∧
      ∀ x : Q, x ^ 2 = 1 ↔ x ∈ center Q := by
  rcases hc with ho | hr
  · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
  obtain ⟨e0⟩ := hr
  obtain ⟨_,⟨e⟩,_⟩ := d.unitaryFive_local_structure h hH.1.1.2 hp U e0
  let f : L.pCoreIn 2 ≃* PlaneCore.Parameters U.form :=
    ((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).symm.trans
      ((LocalCoreTransport.coreEquiv 2 e).trans U.rightLocalImageCoreParameters)
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  exact PlaneCore.Parameters.structure_of_equiv U.form U.local_field_card U.conjugation c hc f

/-- Every elementary subgroup inside the original plane core lies in its center. -/
theorem Preparation.unitaryFive_plane_core_elementary_le_center
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (E : Subgroup G) (hE : E ≤ L.pCoreIn 2) (hel : IsElementaryAbelian 2 E) :
    E ≤ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
  let := hel
  intro x hx
  let q : L.pCoreIn 2 := ⟨x,hE hx⟩
  have hsq : q ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
  exact ⟨q,(d.unitaryFive_plane_core_structure h hH hp U hc).2.2.2.2 q |>.mp hsq,rfl⟩

/-- The Thompson subgroup of the plane core, in the original ambient group.
No equality with the Thompson subgroup of T is asserted. -/
theorem Preparation.unitaryFive_plane_core_thompson
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    elementaryAbelianMaxJ (L.pCoreIn 2) =
      (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
  have hj : elementaryAbelianMaxJ (L.pCoreIn 2) ≤
      (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
    apply sSup_le
    intro E hE
    exact d.unitaryFive_plane_core_elementary_le_center h hH hp U hc E hE.1 hE.2.1
  exact elementaryAbelianMaxJ_eq_of_elementary_overgroup _ _ hj (map_subtype_le _)
    ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1.map (L.pCoreIn 2).subtype)

/-- The two core centers recover the original full factor normalizers. -/
theorem Preparation.unitaryFive_core_center_normalizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    ∀ i : Fin 2, normalizer
      ((center ((![L,residual H] i).pCoreIn 2)).map
        ((![L,residual H] i).pCoreIn 2).subtype : Set G) =
      normalizer (![L,residual H] i : Set G) := by
  have hmax : ∀ i : Fin 2, IsMaximalTwoLocal (normalizer (![L,residual H] i : Set G)) := by
    intro i
    fin_cases i
    · exact h.maximal
    · have hTK := hH.1.1.2.trans (le_normalizer_residual H)
      have hm := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T
        (d.unitaryFive_right_maximal h hH hp U hc)).normalizer_maximal
      have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
        le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK)
          (le_componentOrbit _ _)
      rwa [ho] at hm
  have hne : ∀ i : Fin 2, pCore 2 (![L,residual H] i) ≠ ⊥ := by
    rcases hc with ho | hr
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
    obtain ⟨e0⟩ := hr
    have hs := d.unitaryFive_local_structure h hH.1.1.2 hp U e0
    intro i he
    fin_cases i
    · change pCore 2 L = ⊥ at he
      have hd := hs.2.2.2.2.1
      rw [he,Nat.card_unique] at hd
      norm_num at hd
    · change pCore 2 (residual H) = ⊥ at he
      have hd := hs.2.2.2.2.2.1
      rw [he,Nat.card_unique] at hd
      norm_num at hd
  intro i
  let K := ![L,residual H] i
  let Q := K.pCoreIn 2
  have hQ : IsPGroup 2 Q := isPGroup_pCoreIn 2 K
  let : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr (by
    intro he
    exact hne i ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp he))
  let : Nontrivial (center Q) := hQ.center_nontrivial
  have hZ : (center Q).map Q.subtype ≠ ⊥ := by
    intro he
    exact (nontrivial_iff_ne_bot (center Q)).mp inferInstance
      ((map_eq_bot_iff_of_injective _ Q.subtype_injective).mp he)
  have hN : normalizer (K : Set G) ≤ normalizer ((center Q).map Q.subtype : Set G) :=
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K)).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  exact le_antisymm ((hmax i).2
    ⟨(center Q).map Q.subtype,hZ,(hQ.to_subgroup (center Q)).map Q.subtype,rfl⟩ hN) hN

/-- The same center normalizers on the literal full-normalizer endpoints. -/
theorem Preparation.unitaryFive_full_normalizer_core_centers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    ∀ i : Fin 2,
      let M := normalizer (![L,residual H] i : Set G)
      M.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
      normalizer ((center (M.pCoreIn 2)).map (M.pCoreIn 2).subtype : Set G) = M := by
  have hl := d.unitaryFive_normalizer_local_conditions h hH hp U hc
  intro i
  have he : (normalizer (![L,residual H] i : Set G)).pCoreIn 2 =
      (![L,residual H] i).pCoreIn 2 := by
    fin_cases i
    · exact hl.twoCore_left
    · exact hl.twoCore_right
  refine ⟨he,?_⟩
  rw [he]
  exact d.unitaryFive_core_center_normalizers h hH hp U hc i

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- F.4.31(a) on the original source parabolics: their index-three residuals
contain their two-cores, which therefore have the original factor centers. -/
theorem Preparation.unitaryFive_parabolic_core_centers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    ∀ i : Fin 2,
      let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
      P.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
      normalizer ((center (P.pCoreIn 2)).map (P.pCoreIn 2).subtype : Set G) =
        normalizer (![L,residual H] i : Set G) := by
  have hind : ∀ i : Fin 2,
      (solvableResidual (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i)).index = 3 := by
    rcases hc with ho | hr
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
    obtain ⟨e⟩ := hr
    intro i
    fin_cases i
    · change (solvableResidual (ChapterF.Source.parabolic ![L,residual H]
        (sourceS L H) 0)).index = 3
      rw [←Subgroup.index_map_equiv _ e.left]
      change ((solvableResidual (ChapterF.Source.parabolic ![L,residual H]
        (sourceS L H) 0)).map e.left.toMonoidHom).index = 3
      rw [map_solvableResidual_eq e.left.toMonoidHom e.left.surjective]
      exact U.rightLocal_index
    · change (solvableResidual (ChapterF.Source.parabolic ![L,residual H]
        (sourceS L H) 1)).index = 3
      rw [←Subgroup.index_map_equiv _ e.right]
      change ((solvableResidual (ChapterF.Source.parabolic ![L,residual H]
        (sourceS L H) 1)).map e.right.toMonoidHom).index = 3
      rw [map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
      exact U.leftLocal_index_eq_three
  intro i
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
  let K := ![L,residual H] i
  have hKP : K ≤ P := le_sup_left.trans le_sup_left
  have hPN : P ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKP).mp
      ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic i)
  have hQ : pCore 2 P ≤ solvableResidual P :=
    IsPGroup.le_normal_of_index_primeTo (solvableResidual P) (pCore 2 P) pCore_isPGroup
      (by rw [hind i]; decide)
  have hQL : P.pCoreIn 2 ≤ K :=
    (map_mono (f := P.subtype) hQ).trans_eq (d.parabolic_residuals h hH.1.1.2 hp i)
  have he : P.pCoreIn 2 = K.pCoreIn 2 := le_antisymm
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 P) hQL
      (hKP.trans (P.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))))
    (pCoreIn_mono_of_normalizes hKP hPN)
  refine ⟨he,?_⟩
  rw [he]
  exact d.unitaryFive_core_center_normalizers h hH hp U hc i

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
