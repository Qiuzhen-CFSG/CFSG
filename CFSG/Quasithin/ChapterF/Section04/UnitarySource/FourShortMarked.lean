module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourShortTransport
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointResidual
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongMark
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# Simultaneous residual markings of the unitary short and long roots

Restrict the two endpoint isomorphisms to their actual solvable residuals.
The left restriction identifies the plane factor with the original L.
Both overlap squares identify its short root with sourceShort and its
long root with an element of the center of the original right residual.
Thus separately chosen abstract residual isomorphisms are not needed.

Source: Aschbacher–Smith F.4.42, printed p.295 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourShortMarked
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot

private theorem plane_residual (m : ℕ) (hm : 1 ≤ m) :
    (solvableResidual (planeParabolic m hm)).map (planeParabolic m hm).subtype = L2 m hm := by
  let := L2_isPerfect m hm
  have hmat : (solvableResidual (planeParabolicMatrix m hm)).map
      (planeParabolicMatrix m hm).subtype = L2Matrix m hm := by
    let f := planeDet (MatrixField m) (standardForm m hm)
    have hle : solvableResidual (planeParabolicMatrix m hm) ≤ f.ker := by
      apply (Subgroup.map_eq_bot_iff _).mp
      exact bot_unique ((map_solvableResidual_le f).trans (solvableResidual_eq_bot.le))
    apply le_antisymm (map_mono hle)
    change L2Matrix m hm ≤ _
    let : Group.IsPerfect (L2Matrix m hm) :=
      Group.IsPerfect.ofSurjective (f := (L2ProjectIso m hm).symm.toMonoidHom)
        (L2ProjectIso m hm).symm.surjective
    exact le_map_solvableResidual_of_isPerfect _ _ (L2Matrix_le_planeParabolic m hm)
  let e : planeParabolicMatrix m hm ≃* planeParabolic m hm :=
    (planeParabolicMatrix m hm).equivMapOfInjective (projection m hm) (projection_injective m hm)
  rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,Subgroup.map_map]
  change (solvableResidual (planeParabolicMatrix m hm)).map
    ((projection m hm).comp (planeParabolicMatrix m hm).subtype) = _
  rw [←Subgroup.map_map,hmat]
  rfl

private theorem marked_residual_equiv
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    (P K : Subgroup G) (Q D : Subgroup X)
    (hP : (solvableResidual P).map P.subtype = K)
    (hQ : (solvableResidual Q).map Q.subtype = D) (e : P ≃* Q) :
    ∃ f : K ≃* D, ∀ x : K,
      (f x).val = (e ⟨x.val,(hP ▸ map_subtype_le _) x.property⟩).val := by
  let a : solvableResidual P ≃* K :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
  let b : solvableResidual Q ≃* D :=
    ((solvableResidual Q).equivMapOfInjective Q.subtype Q.subtype_injective).trans
      (MulEquiv.subgroupCongr hQ)
  refine ⟨a.symm.trans (e.solvableResidualEquiv.trans b),?_⟩
  intro x
  obtain ⟨y,rfl⟩ := a.surjective x
  simp only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
  rfl

variable {G : Type*} [Group G] [Finite G]
  (P : Fin 2 → Subgroup G) (L K : Subgroup G)
  (hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,K] i)
  (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (amalgam m hm).reverse)

include hr hm' in
/-- Restriction through the same endpoint and overlap maps preserves both root marks. -/
theorem marked_plane_equiv_with_map :
    ∃ f : localFactor (MatrixField m) (form (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm)) ≃* L,
      (∀ x, ∀ hx : (f x).val ∈ P 0,
        (e.left ⟨(f x).val,hx⟩).val = projection m hm x.val) ∧
      (f (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))).val =
        (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val ∧
      (f (SourceNormalizer.FourShortRoot.longMark (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm)).val).val ∈ (center K).map K.subtype := by
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_surjective (projection m hm) (project_surjective _ _)
  obtain ⟨a,ha⟩ := marked_residual_equiv (P 0) L (planeParabolic m hm) (L2 m hm)
    (hr 0) (plane_residual m hm) e.left
  obtain ⟨b,hb⟩ := marked_residual_equiv (P 1) K (pointParabolic m hm)
    (PointLocal.ProjectiveLocal m hm) (hr 1)
    (PointLocal.pointParabolic_solvableResidual m hm hm') e.right
  have hLP : L ≤ P 0 := by
    rw [←show (solvableResidual (P 0)).map (P 0).subtype = L from hr 0]
    exact map_subtype_le _
  have hKP : K ≤ P 1 := by
    rw [←show (solvableResidual (P 1)).map (P 1).subtype = K from hr 1]
    exact map_subtype_le _
  let f : L2Matrix m hm ≃* L := (L2ProjectIso m hm).trans a.symm
  have hf (x : L2Matrix m hm) :
      (e.left ⟨(f x).val,hLP (f x).property⟩).val =
        projection m hm x.val := by
    have hh := ha (f x)
    have hh' : a (f x) = L2ProjectIso m hm x := a.apply_symm_apply _
    rw [hh'] at hh
    exact hh.symm
  refine ⟨f,(fun x _ => hf x),?_,?_⟩
  · let t := ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e
    have hte := congrArg Subtype.val (e.left_commutes t)
    change (e.left ⟨t.val,t.property.1⟩).val = (e.middle t).val at hte
    have htm : e.middle t = ChapterF.UnitarySource.FourShortTransport.shortOverlap m hm :=
      e.middle.apply_symm_apply _
    rw [htm] at hte
    have he : e.left ⟨(f (shortLocal (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm))).val,
          hLP (f _).property⟩ =
        e.left ⟨t.val,t.property.1⟩ := Subtype.ext ((hf _).trans hte.symm)
    exact congrArg Subtype.val (e.left.injective he)
  · let z₀ := SourceNormalizer.FourShortRoot.longMark (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm)
    have hz₀ : projection m hm z₀.val.val ∈
        (center (PointLocal.ProjectiveLocal m hm)).map (PointLocal.ProjectiveLocal m hm).subtype := by
      obtain ⟨z,hz,he⟩ := SourceNormalizer.FourShortRoot.longMark_mem_point_center
        (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
      refine ⟨PointLocal.localEquiv m hm z,?_,?_⟩
      · rw [←center_map_equiv (PointLocal.localEquiv m hm)]
        exact mem_map_of_mem _ hz
      · exact congrArg (projection m hm) he
    obtain ⟨z,hz,hzval⟩ := hz₀
    let k := b.symm z
    have hk : (e.right ⟨k.val,hKP k.property⟩).val =
        projection m hm z₀.val.val := by
      have hh := hb k
      rw [show b k = z from b.apply_symm_apply z] at hh
      exact hh.symm.trans hzval
    have hplane : projection m hm z₀.val.val ∈ planeParabolic m hm :=
      (L2_le_planeParabolic m hm) (L2ProjectIso m hm z₀.val).property
    let c : overlap m hm := ⟨projection m hm z₀.val.val,
      (exact_overlap m hm).le ⟨hzval ▸ (PointLocal.projectiveLocal_le_pointParabolic m hm z.property),hplane⟩⟩
    let w := e.middle.symm c
    have hw (i : Fin 2) : w.val ∈ P i := by
      fin_cases i
      · exact w.property.1
      · exact w.property.2
    have hwl : (e.left ⟨w.val,hw 0⟩).val = c.val := by
      have hh := congrArg Subtype.val (e.left_commutes w)
      change (e.left ⟨w.val,hw 0⟩).val = (e.middle w).val at hh
      rw [show e.middle w = c from e.middle.apply_symm_apply _] at hh
      exact hh
    have hwr : (e.right ⟨w.val,hw 1⟩).val = c.val := by
      have hh := congrArg Subtype.val (e.right_commutes w)
      change (e.right ⟨w.val,hw 1⟩).val = (e.middle w).val at hh
      rw [show e.middle w = c from e.middle.apply_symm_apply _] at hh
      exact hh
    have hfl : (f z₀.val).val = w.val := congrArg Subtype.val
      (e.left.injective (Subtype.ext ((hf z₀.val).trans hwl.symm)))
    have hkr : k.val = w.val := congrArg Subtype.val
      (e.right.injective (Subtype.ext (hk.trans hwr.symm)))
    refine ⟨k,?_,hkr.trans hfl.symm⟩
    rw [←center_map_equiv b.symm]
    exact mem_map_of_mem _ hz

include hr hm' in
/-- Restriction through the same endpoint and overlap maps preserves both root marks. -/
theorem marked_plane_equiv :
    ∃ f : localFactor (MatrixField m) (form (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm)) ≃* L,
      (f (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))).val =
        (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val ∧
      (f (SourceNormalizer.FourShortRoot.longMark (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm)).val).val ∈ (center K).map K.subtype := by
  obtain ⟨f,_,ht,hz⟩ := marked_plane_equiv_with_map P L K hr m hm hm' e
  exact ⟨f,ht,hz⟩

end CFSG.Quasithin.ChapterF.UnitarySource.FourShortMarked
