module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourInvolutionPlacement
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.SylowGeometry
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PlaneParabolic
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical.Structure
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SolvableResidual
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneShort.Structure
public import Theory.GroupTheory.Amalgam.Reversal
/-!
# Projective unitary-four involutions in the marked plane core

For every m ≥ 1, the faithful map SU₄(2^m) → PSU₄(2^m) carries the
matrix placement theorem to the actual projective flag amalgam. An involution
in its whole overlap lies in the native upper Sylow and is point-conjugate
into the plane radical. That radical has the full plane parabolic as its
normalizer and is exactly its two-core.

Both commuting squares of a compatible subgroup-amalgam isomorphism transport
the conjugator and its target. Restriction to the actual solvable residuals
then places the image in an original residual two-core. The two orientations
are retained. This is local involution placement, not ambient nonfusion,
outer-involution transfer, or a construction of the full-normalizer extension.

Source: Aschbacher–Smith F.4.27(3), F.4.30 and the unitary argument in
F.4.35, printed pp.288–292 (`refs/quasithin.pdf`). The matrix calculation is
`UnitaryFourInvolutionPlacement.upper_involution_point_conjugate_plane`.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourPlacement
open GreenBook.LieModels.UnitaryFour
variable (m : ℕ) (hm : 1 ≤ m)
local notation "L" => L2 m hm

/-- The plane residual two-core in the actual projective carrier. -/
def planeCore : Subgroup (ProjectiveGroup m hm) := (pCore 2 L).map (L2 m hm).subtype

/-- Projectivization preserves the literal plane residual core. -/
theorem matrix_plane_core_map :
    ((pCore 2 (L2Matrix m hm)).map (L2Matrix m hm).subtype).map (projection m hm) = planeCore m hm := by
  have he : (L2 m hm).subtype.comp (L2ProjectIso m hm).toMonoidHom =
      (projection m hm).comp (L2Matrix m hm).subtype := rfl
  rw [planeCore, ← pCore_map_iso 2 (L2ProjectIso m hm)]
  simp only [map_map, he]

/-- Point conjugation puts every upper involution in the plane core. -/
theorem projective_sylow_involution_placement
    (a : ProjectiveGroup m hm) (ha : a ∈ upperProjective m hm) (ha2 : a ^ 2 = 1) :
    ∃ g : pointParabolic m hm, g.val * a * g.val⁻¹ ∈ planeCore m hm := by
  obtain ⟨a,ha,rfl⟩ := ha
  have hsq : a ^ 2 = 1 := (projection_injective m hm) (by simpa only [map_pow, map_one] using ha2)
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourInvolutionPlacement.upper_involution_point_conjugate_plane
    (MatrixField m) (fieldConj m) (fieldConj_involutive m hm) a ha hsq
  refine ⟨⟨projection m hm g.val, ⟨g.val,g.property,rfl⟩⟩, ?_⟩
  let gM : MatrixGroup m hm := g.val
  have hmatrix : gM * a * gM⁻¹ ∈
      (pCore 2 (L2Matrix m hm)).map (L2Matrix m hm).subtype := by
    rw [← L2MatrixRadical_eq_twoCore]
    exact hg
  have hh := mem_map_of_mem (projection m hm) hmatrix
  rw [matrix_plane_core_map] at hh
  simpa only [map_mul,map_inv] using hh

open Theory.SpecificGroups.ClassicalUnitary

private theorem matrix_core_eq_ambientRadical :
    (pCore 2 (L2Matrix m hm)).map (L2Matrix m hm).subtype =
      UnitaryFourConverse.PlaneParabolic.ambientRadical (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm) := by
  rw [← L2MatrixRadical_eq_twoCore]
  apply le_antisymm
  · rintro x ⟨a, ha, rfl⟩
    let q := (UnitaryFourConverse.PlaneParabolic.kernelEquivRadical
      (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).symm ⟨a, ha⟩
    exact ⟨q.val, q.property, rfl⟩
  · rintro x ⟨a, ha, rfl⟩
    let q := UnitaryFourConverse.PlaneParabolic.kernelEquivRadical
      (MatrixField m) (fieldConj m) (fieldConj_involutive m hm) ⟨a, ha⟩
    exact ⟨q.val, q.property, rfl⟩

/-- The fixed coordinate plane recovers the whole radical normalizer. -/
theorem planeCore_normalizer :
    normalizer (planeCore m hm : Set (ProjectiveGroup m hm)) = planeParabolic m hm := by
  have hn : normalizer (((pCore 2 (L2Matrix m hm)).map
      (L2Matrix m hm).subtype : Subgroup (MatrixGroup m hm)) : Set _) =
      planeParabolicMatrix m hm := by
    rw [matrix_core_eq_ambientRadical]
    exact UnitaryFourConverse.PlaneParabolic.normalizer_ambientRadical
      (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  rw [← matrix_plane_core_map, ← Subgroup.map_normalizer_eq_of_bijective _
    ⟨projection_injective m hm, UnitaryFourFlag.project_surjective _ _⟩, hn]
  rfl

/-- The radical is a normal two-subgroup of the full plane endpoint. -/
theorem planeCore_le_twoCore : planeCore m hm ≤ (planeParabolic m hm).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (L2 m hm))
    ((pCoreIn_le 2 (L2 m hm)).trans (L2_le_planeParabolic m hm))
  change planeParabolic m hm ≤ normalizer (planeCore m hm : Set _)
  rw [planeCore_normalizer]

/-- The odd diagonal torus introduces no involutions into the overlap. -/
theorem overlap_involution_mem_upper (a : overlap m hm) (ha : a ^ 2 = 1) :
    a.val ∈ upperProjective m hm := by
  let S := (projectiveSylow m hm).subtype (upperProjective_le_overlap m hm)
  let : (S : Subgroup (overlap m hm)).Normal := upperProjective_normal_in_overlap m hm
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one ha)
  have hle : zpowers a ≤ (S : Subgroup (overlap m hm)) :=
    sup_eq_right.mp (S.is_maximal' (hp.to_sup_of_normal_right S.isPGroup') le_sup_right)
  exact hle (mem_zpowers a)

open Theory.GroupTheory

/-- Compatible endpoint maps carry the native placement to the whole source overlap. -/
theorem comparison_involution_to_core
    {G : Type*} [Group G] (P Q : Subgroup G)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right)
      (amalgam m hm))
    (x : G) (hx : x ∈ P ⊓ Q) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ P, g * x * g⁻¹ ∈ Q.pCoreIn 2 := by
  let α := RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right
  let b : (P ⊓ Q : Subgroup G) := ⟨x,hx⟩
  let a : overlap m hm := e.middle b
  have ha2 : a ^ 2 = 1 := by
    change e.middle b ^ 2 = 1
    rw [←map_pow, show b ^ 2 = 1 from Subtype.ext hx2, map_one]
  have hau := overlap_involution_mem_upper m hm a ha2
  obtain ⟨g,hg⟩ := projective_sylow_involution_placement m hm a.val hau
    (congrArg Subtype.val ha2)
  let y := g.val * a.val * g.val⁻¹
  have haPQ : a.val ∈ pointParabolic m hm ⊓ planeParabolic m hm := by
    rw [exact_overlap]
    exact a.property
  have haP : a.val ∈ pointParabolic m hm := haPQ.1
  have hyP : y ∈ pointParabolic m hm :=
    (pointParabolic m hm).mul_mem ((pointParabolic m hm).mul_mem g.property haP)
      ((pointParabolic m hm).inv_mem g.property)
  have hyQ : y ∈ planeParabolic m hm :=
    pCoreIn_le 2 _ (planeCore_le_twoCore m hm hg)
  let yB : overlap m hm := ⟨y, (exact_overlap m hm) ▸ ⟨hyP,hyQ⟩⟩
  let c : (P ⊓ Q : Subgroup G) := e.middle.symm yB
  let k : P := e.left.symm g
  have he : k * α.left b * k⁻¹ = α.left c := by
    apply e.left.injective
    rw [map_mul,map_mul,map_inv,e.left_commutes,e.left_commutes]
    rw [show e.left k = g from e.left.apply_symm_apply g]
    change g * (amalgam m hm).left a * g⁻¹ =
      (amalgam m hm).left (e.middle (e.middle.symm yB))
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hval : k.val * x * k.val⁻¹ = c.val := congrArg Subtype.val he
  refine ⟨k.val,k.property,?_⟩
  rw [hval]
  have hnative : (amalgam m hm).right yB ∈ pCore 2 (planeParabolic m hm) :=
    (mem_map_iff_mem (planeParabolic m hm).subtype_injective).mp
      (planeCore_le_twoCore m hm hg)
  have hc : e.right (α.right c) ∈ pCore 2 (planeParabolic m hm) := by
    rw [e.right_commutes]
    simpa only [c, MulEquiv.apply_symm_apply] using hnative
  rw [←pCore_map_iso 2 e.right] at hc
  exact ⟨α.right c,(mem_map_iff_mem e.right.injective).mp hc,rfl⟩

/-- The radical is exactly the two-core of the full plane stabilizer. -/
theorem planeCore_eq_twoCore : planeCore m hm = (planeParabolic m hm).pCoreIn 2 := by
  apply le_antisymm (planeCore_le_twoCore m hm)
  change (planeParabolic m hm).pCoreIn 2 ≤ (L2 m hm).pCoreIn 2
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
    (two_subgroup_le_L2 m hm _ (isPGroup_pCoreIn 2 _) (pCoreIn_le 2 _))
  exact (L2_le_planeParabolic m hm).trans
    ((planeParabolic m hm).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _))

/-- The plane core lies in the perfect local factor, hence in the solvable residual. -/
theorem plane_twoCore_le_residual :
    pCore 2 (planeParabolic m hm) ≤ solvableResidual (planeParabolic m hm) := by
  let := L2_isPerfect m hm
  apply (map_le_map_iff_of_injective (planeParabolic m hm).subtype_injective).mp
  exact (two_subgroup_le_L2 m hm _ (isPGroup_pCoreIn 2 _) (pCoreIn_le 2 _)).trans
    (le_map_solvableResidual_of_isPerfect _ _ (L2_le_planeParabolic m hm))

/-- Transport retains the original residual, as an ambient subgroup. -/
theorem plane_comparison_core_le_residual_core
    {G : Type*} [Group G] [Finite G] (Q R : Subgroup G)
    (e : Q ≃* planeParabolic m hm)
    (hr : (solvableResidual Q).map Q.subtype = R) :
    Q.pCoreIn 2 ≤ R.pCoreIn 2 := by
  have hcore : pCore 2 Q ≤ solvableResidual Q := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso, map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact plane_twoCore_le_residual m hm
  have hQR : Q.pCoreIn 2 ≤ R := hr ▸ map_mono hcore
  have hRQ : R ≤ Q := hr ▸ map_subtype_le _
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Q) hQR
  exact hRQ.trans (Q.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Q (pCore 2 Q)))

/-- Either orientation of the whole diagram places overlap involutions in
one of the two original residual cores. The conjugator belongs to the opposite endpoint. -/
theorem comparison_involution_to_residual_core
    {G : Type*} [Group G] [Finite G] (P R : Fin 2 → Subgroup G)
    (hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = R i)
    (he : Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
        (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
        (amalgam m hm).reverse))
    (x : G) (hx : x ∈ P 0 ⊓ P 1) (hx2 : x ^ 2 = 1) :
    (∃ g ∈ P 0, g * x * g⁻¹ ∈ (R 1).pCoreIn 2) ∨
      (∃ g ∈ P 1, g * x * g⁻¹ ∈ (R 0).pCoreIn 2) := by
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · obtain ⟨g,hg,hc⟩ := comparison_involution_to_core m hm (P 0) (P 1) e x hx hx2
    exact Or.inl ⟨g,hg,plane_comparison_core_le_residual_core m hm _ _ e.right (hr 1) hc⟩
  · let swap : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (P 1) (P 1 ⊓ P 0) (P 0) inf_le_left inf_le_right)
        (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right).reverse := {
      left := MulEquiv.refl _
      right := MulEquiv.refl _
      middle := MulEquiv.subgroupCongr (inf_comm _ _)
      left_commutes _ := rfl
      right_commutes _ := rfl }
    obtain ⟨g,hg,hc⟩ := comparison_involution_to_core m hm (P 1) (P 0)
      (swap.trans e.reverse) x ⟨hx.2,hx.1⟩ hx2
    exact Or.inr ⟨g,hg,plane_comparison_core_le_residual_core m hm _ _ e.left (hr 0) hc⟩

end CFSG.Quasithin.ChapterF.UnitarySource.FourPlacement
