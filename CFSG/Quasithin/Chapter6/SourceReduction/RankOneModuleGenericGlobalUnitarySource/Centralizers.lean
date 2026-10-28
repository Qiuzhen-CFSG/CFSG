module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySecondParabolic
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Centralizers

/-!
# Ambient long-root control for the prepared unitary-four branch

The explicit fixed-field diagonal action is transitive on the nonidentity
center of the point residual. Restricting the actual endpoint maps to their
solvable residuals transports this orbit to the original O²(H). Faithfulness
of the original left factor excludes the opposite orientation; the
ordinary/degree-two comparisons both retain their whole overlap.

Original uniqueness and right maximality place the centralizer of a
Sylow-central root involution in the full right normalizer. The transported
orbit gives that bound for every nonidentity root element. It also recovers
the exact root-group normalizer. The full I.6.1(1) criterion proves that
distinct conjugates of the root group intersect only in the identity.

These are source 5.3.3 and F.4.34, printed pp.659,291 of
`refs/quasithin.pdf`, with the literal original residual embeddings.
The concrete full-normalizer realization, ambient nonfusion of the two
inner involution classes, outer transfer, short-root centralizer containment
and ambient order comparison remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
namespace UnitarySource

private theorem point_center_orbit (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m) :
    ∀ x ∈ (center (PointLocal.ProjectiveLocal m hm)).map
        (PointLocal.ProjectiveLocal m hm).subtype, x ≠ 1 →
      ∀ y ∈ (center (PointLocal.ProjectiveLocal m hm)).map
        (PointLocal.ProjectiveLocal m hm).subtype, y ≠ 1 →
        ∃ g ∈ pointParabolic m hm, y = g*x*g⁻¹ := by
  let e : pointParabolicMatrix m hm ≃* pointParabolic m hm :=
    (pointParabolicMatrix m hm).equivMapOfInjective (projection m hm)
      (projection_injective m hm)
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_equiv (MatrixGroup m hm) (Extension.projectEquiv m hm).toEquiv
  apply center_orbit_transport (PointLocal.projectiveLocal_le_pointParabolic m hm)
    e.symm (R := PointLocal.MatrixLocal m hm)
  · have hr : (PointLocal.ProjectiveLocal m hm).subgroupOf (pointParabolic m hm) =
        solvableResidual (pointParabolic m hm) := by
      rw [←PointLocal.pointParabolic_solvableResidual m hm hm']
      exact comap_map_eq_self_of_injective (pointParabolic m hm).subtype_injective _
    rw [hr,←map_map,map_solvableResidual_eq e.symm.toMonoidHom e.symm.surjective]
    exact PointLocal.pointParabolicMatrix_solvableResidual m hm hm'
  · exact Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter.center_orbit
      (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
      (PointLocal.fieldConj_nontrivial m hm)

variable {G : Type*} [Group G] [Finite G]

private theorem right_point_equiv (P : Fin 2 → Subgroup G) (L R : Subgroup G)
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
    Nonempty (P 1 ≃* pointParabolic m hm) := by
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
  · exact ⟨e.right⟩
end UnitarySource

open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The actual source right parabolic is transitive on the nonidentity
center of O²(H), in both ordinary and degree-two rows. -/
theorem Preparation.unitary_right_center_orbit
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    ∀ x ∈ (center (residual H)).map (residual H).subtype, x ≠ 1 →
      ∀ y ∈ (center (residual H)).map (residual H).subtype, y ≠ 1 →
        ∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
          y = g*x*g⁻¹ := by
  obtain ⟨hm',_,_,⟨b⟩,_⟩ := hc.elim
    (d.unitary_local_structure h hTH hp m hm)
    (d.unitaryExtension_local_structure h hTH hp m hm)
  have hz := (d.unitary_core_structure h hTH hp m hm hc).2.2.2.2.2.2.2.2.2
  have transfer (P : Fin 2 → Subgroup G)
      (hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,residual H] i)
      (hKP : residual H ≤ P 1)
      (he : Nonempty (RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
          (amalgam m hm)) ∨
        Nonempty (RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
          (amalgam m hm).reverse)) :
      ∀ x ∈ (center (residual H)).map (residual H).subtype, x ≠ 1 →
        ∀ y ∈ (center (residual H)).map (residual H).subtype, y ≠ 1 →
          ∃ g ∈ P 1, y = g*x*g⁻¹ := by
    obtain ⟨e⟩ := UnitarySource.right_point_equiv P L (residual H) h.local_mem.2 hr
      m hm hm' b hz he
    apply center_orbit_transport hKP e (R := PointLocal.ProjectiveLocal m hm)
    · have hres : (residual H).subgroupOf (P 1) = solvableResidual (P 1) := by
        have hr1 : (solvableResidual (P 1)).map (P 1).subtype = residual H := hr 1
        rw [←hr1]
        exact comap_map_eq_self_of_injective (P 1).subtype_injective _
      rw [hres,←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
      exact PointLocal.pointParabolic_solvableResidual m hm hm'
    · exact UnitarySource.point_center_orbit m hm hm'
  rcases hc with ho | he
  · exact transfer _ (d.parabolic_residuals h hTH hp)
      (le_sup_left.trans le_sup_left) ho
  · have hred := d.unitaryExtension_reduced_amalgam h hTH hp m hm' he
    have horbit := transfer _
      (d.reduced_parabolic_residuals h hTH hp (.unitaryExtension m hm he))
      (le_sup_left.trans le_sup_left) hred
    intro x hx hx1 y hy hy1
    obtain ⟨g,hg,hgxy⟩ := horbit x hx hx1 y hy hy1
    refine ⟨g,?_,hgxy⟩
    have hle : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 ≤
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 := by
      rw [d.reduced_source_parabolics h hTH hp (.unitaryExtension m hm he) 1]
      exact map_subtype_le _
    exact hle hg

/-- The central-involution bounds in source 5.3.3 hold in the original
ambient group, with no additional orbit or centralizer hypothesis. -/
theorem Preparation.unitary_central_involution_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  intro i
  fin_cases i
  · exact d.left_central_involution_centralizer
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hK := d.unitary_right_maximal h hH hp m hm hc
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
    (d.unitary_right_center_orbit h hH.1.1.2 hp m hm hc)

/-- Every nonidentity element of the actual right residual center is an
involution. The center of its special two-core and its ambient embedding
are retained. -/
theorem Preparation.unitary_right_center_involutions
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (z : G) (hz : z ∈ (center (residual H)).map (residual H).subtype)
    (hz1 : z ≠ 1) : orderOf z = 2 := by
  have hK := d.unitary_right_maximal h hH hp m hm hc
  have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) hK.1
  have hZQ : center (residual H) ≤ pCore 2 (residual H) :=
    (center_le_centralizer (pCore 2 (residual H) : Set (residual H))).trans hchar
  have hele := (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.2.2.2.2.2.2.1
  let : IsElementaryAbelian 2 (center (pCore 2 (residual H))) := hele
  obtain ⟨a,ha,rfl⟩ := hz
  let q : pCore 2 (residual H) := ⟨a,hZQ ha⟩
  have hq : q ∈ center (pCore 2 (residual H)) :=
    mem_center_iff.mpr (fun b => Subtype.ext (mem_center_iff.mp ha b.val))
  have hq2 : q^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) q hq
  apply orderOf_eq_prime _ hz1
  exact congrArg (fun b : pCore 2 (residual H) => b.val.val) hq2

/-- The normalizer of the actual long-root group is the full right
normalizer. The nontrivial root element is obtained from the proved q-element
center of the special core. -/
theorem Preparation.unitary_right_center_normalizer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    normalizer ((center (residual H)).map (residual H).subtype : Set G) =
      normalizer (residual H : Set G) := by
  obtain ⟨hm',_,_,_,_,hZcard,_,_,_,hcent⟩ :=
    d.unitary_core_structure h hH.1.1.2 hp m hm hc
  let : Nontrivial (center (pCore 2 (residual H))) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hZcard]
      exact Nat.one_lt_pow (by omega) (by decide))
  obtain ⟨z,hz⟩ := exists_ne (1 : center (pCore 2 (residual H)))
  let x : G := z.val.val.val
  have hx : x ∈ (center (residual H)).map (residual H).subtype :=
    ⟨z.val.val,hcent ⟨z.val,z.property,rfl⟩,rfl⟩
  have hx1 : x ≠ 1 := fun he => hz (Subtype.ext (Subtype.ext (Subtype.ext he)))
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  apply le_antisymm ?_
    (normalizer_le_normalizer_characteristic_image (residual H) (center (residual H)))
  intro g hg
  have hxy := (mem_normalizer_iff.mp hg x).mp hx
  have hxy1 : g*x*g⁻¹ ≠ 1 := by
    intro he
    apply hx1
    exact (MulAut.conj g).injective (by
      simpa only [MulAut.conj_apply,map_one] using he)
  obtain ⟨k,hk,he⟩ := d.unitary_right_center_orbit h hH.1.1.2 hp m hm hc
    x hx hx1 (g*x*g⁻¹) hxy hxy1
  have hkg : k⁻¹*g ∈ centralizer ({x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    symm
    calc
      x*(k⁻¹*g) = k⁻¹*(k*x*k⁻¹)*g := by group
      _ = k⁻¹*(g*x*g⁻¹)*g := by rw [←he]
      _ = (k⁻¹*g)*x := by group
  have hC := d.unitary_central_involution_centralizers h hH hp m hm hc 1 x hx
    (d.unitary_right_center_involutions h hH hp m hm hc x hx hx1)
  have hgN := (normalizer (residual H : Set G)).mul_mem (hPN hk) (hC hkg)
  simpa only [mul_inv_cancel_left] using hgN

/-- The long-root group in the actual right residual is a TI-subgroup of
the ambient group (the unitary case of F.4.34). -/
theorem Preparation.unitary_right_center_ti
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    ChapterI.Section06To08.IsTISubgroup
      ((center (residual H)).map (residual H).subtype) := by
  have hN : normalizer (residual H : Set G) ≤
      normalizer ((center (residual H)).map (residual H).subtype : Set G) :=
    normalizer_le_normalizer_characteristic_image (residual H) (center (residual H))
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  apply ChapterI.Section06To08.lemma_I_6_1_1_of_mem_normalizer
  · intro z hz hz1
    exact (d.unitary_central_involution_centralizers h hH hp m hm hc 1 z hz
      (d.unitary_right_center_involutions h hH hp m hm hc z hz hz1)).trans hN
  · intro x y hx hy hxy
    by_cases hx1 : x = 1
    · obtain ⟨g,hg⟩ := hxy
      have hy1 : y = 1 := by simpa only [hx1,mul_one,mul_inv_cancel] using hg.symm
      exact ⟨1,by simp [hx1,hy1]⟩
    have hy1 : y ≠ 1 := by
      obtain ⟨g,hg⟩ := hxy
      intro he
      apply hx1
      exact (MulAut.conj g).injective (by simpa only [MulAut.conj_apply,map_one] using hg.trans he)
    obtain ⟨g,hg,he⟩ := d.unitary_right_center_orbit h hH.1.1.2 hp m hm hc x hx hx1 y hy hy1
    exact ⟨⟨g,hN (hPN hg)⟩,he.symm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
