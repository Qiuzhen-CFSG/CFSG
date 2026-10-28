module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourPointField
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Commutators
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.TorusSplitting

/-!
# Center fixation forces the prepared U₄ Sylow to be inner

For an ordinary projective U₄ comparison, the right residual is transported
to the point residual of the unitary local model. Its radical center lies in
the residual center, and its quotient by the radical is the actual middle
SL₂ over the fixed field. The result `FourPointField.inner_quotient_of_center_fixed`
shows that an automorphism fixing this center induces an inner automorphism
on that quotient. The prepared residual Sylow field-kernel theorem then puts
the actor in the common source Sylow. The existing long-centralization result
shows every involution of the ambient Sylow fixes the original center; torus
splitting therefore rules out a proper inner Sylow.

This is the ambient transfer step for the ordinary U₄ row in Aschbacher–Smith
F.4.35 and 5.3.3, printed pp.292 and659 of `refs/quasithin.pdf`. The full
normalizer marking and the separate ambient order comparison remain the
inputs to completion and recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

omit hc in
/-- For the ordinary source row, fixing the original right-residual center
forces a Sylow actor into the original inner Sylow, at every exponent. -/
theorem Preparation.unitaryFour_ordinary_center_fixer_mem_left
    (ho : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse))
    (u : T)
    (hu : u.val ∈ centralizer (((center (residual H)).map (residual H).subtype) : Set G)) :
    u.val ∈ L := by
  let K := residual H
  let F := MatrixField m
  let σ := fieldConj m
  let hs := fieldConj_involutive m hm
  let N := PointLocal.MatrixLocal m hm
  let R := PointLocal.Radical m hm
  let k := PointLocal.FixedField m
  obtain ⟨e₀⟩ := (d.unitary_local_structure h hH.1.1.2 hp m hm ho).2.2.2.1
  let e : K ≃* N := e₀.trans (PointLocal.localEquiv m hm).symm
  let a : MulAut K := K.normalizerMonoidHom ⟨u.val,(hH.1.1.2.trans (le_normalizer_residual H)) u.property⟩
  let β := (MulAut.congr e) a
  let c : R ≃* pCore 2 N := MulEquiv.subgroupCongr (PointLocal.radical_eq_twoCore m hm)
  let b : MulAut R := c.trans ((MulAut.characteristic (pCore 2 N) β).trans c.symm)
  have hb (r : R) : (b r).val=β r.val := rfl
  let q : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) k :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      ((QuotientGroup.quotientMulEquivOfEq (PointLocal.radical_eq_twoCore m hm).symm).trans
        (PointLocal.quotientEquivSL m hm))
  have hq (x : K) : q (QuotientGroup.mk' (pCore 2 K) x)=UnitaryFourPointQuotient.middleSL F σ hs (e x) := rfl
  let α := (MulAut.congr q) (quotientAut (pCore 2 K) a)
  have hα (g : N) : UnitaryFourPointQuotient.middleSL F σ hs (β g)=
      α (UnitaryFourPointQuotient.middleSL F σ hs g) := by
    have hh : α (q (QuotientGroup.mk' (pCore 2 K) (e.symm g)))=
        q (QuotientGroup.mk' (pCore 2 K) (a (e.symm g))) := by
      change q ((quotientAut (pCore 2 K) a) (q.symm (q _)))=_
      rw [q.symm_apply_apply,quotientAut_apply_mk]
    rw [hq,hq,e.apply_symm_apply] at hh
    exact hh.symm
  have hfix (z : N) (hz : z ∈ center N) : β z=z := by
    have hzK : e.symm z ∈ center K := (centerCongr e.symm ⟨z,hz⟩).property
    have hcomm := mem_centralizer_iff.mp hu (e.symm z).val
      (mem_map_of_mem K.subtype hzK)
    have ha : a (e.symm z)=e.symm z := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
    change e (a (e.symm z))=z
    rw [ha,e.apply_symm_apply]
  obtain ⟨g,hg⟩ := SourceNormalizer.FourPointField.inner_quotient_of_center_fixed
    F σ hs (PointLocal.fieldConj_nontrivial m hm) β b hb α hα hfix
  let q' := q.trans (Theory.PSL2.sl2QuotientEquiv k)
  have hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i := by
    rw [d.unitary_ordinary_sourceS_eq h hH.1.1.2 hp m hm ho]
    intro i
    fin_cases i
    · exact inf_le_right
    · rw [d.common_sylow_of_comparison h hH.1.1.2 hp (.unitary m hm ho)]
      exact inf_le_right
  have hmem : u ∈ (sourceS L H).subgroupOf (T : Subgroup G) := by
    rw [←d.residual_sylow_field_kernel h hH.1.1.2 hS q']
    change Theory.PSL2.fieldProjection k ((MulAut.congr (Theory.PSL2.sl2QuotientEquiv k)) α)=1
    rw [hg,MulAut.congr_conj]
    apply MonoidHom.mem_ker.mp
    rw [Theory.PSL2.fieldProjection_ker]
    exact ⟨_,rfl⟩
  have hmS : u.val ∈ sourceS L H := hmem
  rw [d.unitary_ordinary_sourceS_eq h hH.1.1.2 hp m hm ho] at hmS
  exact hmS.2

/-- No involution in the original Sylow lies outside L: degree-two rows are
excluded, and the ordinary right quotient detects the fixed long-root center. -/
theorem Preparation.unitaryFour_involution_mem_left (u : T) (hu : orderOf u=2) :
    u.val ∈ L :=
  d.unitaryFour_ordinary_center_fixer_mem_left h hH hp m hm
    (d.unitaryFour_comparison_ordinary h hH hp m hm hc) u
    (d.unitaryFour_involution_centralizes_right_center h hH hp m hm hc u hu)

/-- The actual ambient Sylow is the original inner Sylow. -/
theorem Preparation.unitaryFour_sylow_eq_inner : (T : Subgroup G) ⊓ L=(T : Subgroup G) := by
  by_contra hne
  obtain ⟨u,hu,ho⟩ := d.unitaryFour_exists_outer_involution h hH hp m hm hc
    (lt_of_le_of_ne inf_le_left hne)
  exact ho (d.unitaryFour_involution_mem_left h hH hp m hm hc u hu)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
