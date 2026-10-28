module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionG2Short

/-!
# Original local factors in the unitary comparison

A point residual centralizes the center of its own two-core. The original
faithful left factor therefore occupies the plane endpoint. Restriction of
the compatible parabolic maps to their solvable residuals identifies both
original factors. The plane quotient is PSL₂(q²), so the original exponent
is n = 2m; the nonsolvable point endpoint also forces q = 2^m > 2.

For the degree-two extension, the previously constructed reduction retains
the actual overlap maps and the original perfect residuals. Consequently
the same identifications hold with S = O₂(N_G(L) ∩ H) kept distinct from
the reduced common Sylow T ∩ L. The original two-cores are elementary of
order q⁴ on the left and special of order q⁵ on the right, whose center
has order q and is centralized by the right factor.

These are the local inputs to the unitary normality argument in 5.2.8.
Right maximality, exhaustive F.1.12 comparison, original uniqueness and
ambient completion recognition remain obligations. The Chapter12 companion
applies these calculations to the literal prepared whole-residual pair.
Source: Aschbacher–Smith 5.2.6–8, printed pp.650–653, and F.1.12(I)(6),
pp.262–264 (`refs/quasithin.pdf`). The central matrix calculation reuses
the argument in RankOneModuleGenericGlobalRecognitionUnitaryModel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour

namespace UnitaryFactors
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
section MatrixCenter
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "κ" => coordinatesOfRadical F σ hσ

omit [Finite F] in
private theorem center_radical_central (hnt : ∃ u, σ u ≠ u) :
    (center R).map (radical F σ hσ).subtype ≤ center L := by
  rintro x ⟨r,hr,rfl⟩
  obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt r).mp hr
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hmat : r.val.val.val.val = radicalMatrix F σ (κ r) := by
    exact congrArg (fun x : R => x.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply r).symm
  have hg := (mem_localSU F _ g.val).mp g.property
  have hl := last_row F σ hσ g.val g.property
  change g.val.val.val * r.val.val.val.val = r.val.val.val.val * g.val.val.val
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix, hx,hy, Matrix.mul_apply, Fin.sum_univ_succ,
      hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,hl.2.1,hl.2.2.1,hl.2.2.2,add_comm]


end MatrixCenter

private theorem core_center_transport
    {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hc : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X) :
    (center (pCore 2 Y)).map (pCore 2 Y).subtype ≤ center Y := by
  let c := (e.subgroupMap (pCore 2 X)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  rw [←center_map_equiv c,Subgroup.map_map,←center_map_equiv e]
  change (center (pCore 2 X)).map (e.toMonoidHom.comp (pCore 2 X).subtype) ≤ _
  rw [←Subgroup.map_map]
  exact map_mono hc

/-- The point residual centralizes the center of its own two-core. -/
private theorem point_core_center_central (m : ℕ) (hm : 1 ≤ m) :
    (center (pCore 2 (PointLocal.ProjectiveLocal m hm))).map
      (pCore 2 (PointLocal.ProjectiveLocal m hm)).subtype ≤
        center (PointLocal.ProjectiveLocal m hm) := by
  apply core_center_transport (PointLocal.localEquiv m hm)
  rw [←PointLocal.radical_eq_twoCore m hm]
  exact center_radical_central (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm) (PointLocal.fieldConj_nontrivial m hm)

private theorem binary_point_solvable : Group.IsSolvable (pointParabolic 1 (Nat.le_refl 1)) := by
  let := PointLocal.matrixLocal_isSolvable_two
  have hsol : Group.IsSolvable (pointParabolicMatrix 1 (Nat.le_refl 1)) := by
    apply Group.isSolvable_of_ker_le_range
      (inclusion (UnitaryFourPointLocal.localSU_le_pointParabolicSU (MatrixField 1) (standardForm 1 (Nat.le_refl 1))))
      (UnitaryFourPointResidual.pointScalarUnits (MatrixField 1) (standardForm 1 (Nat.le_refl 1)))
    rw [inclusion_range, UnitaryFourPointResidual.pointScalarUnits_ker]
  let := hsol
  let e : pointParabolicMatrix 1 (Nat.le_refl 1) ≃* pointParabolic 1 (Nat.le_refl 1) :=
    (pointParabolicMatrix 1 (Nat.le_refl 1)).equivMapOfInjective (projection 1 (Nat.le_refl 1))
      (projection_injective 1 (Nat.le_refl 1))
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

private theorem residual_factor_equiv
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    {P K : Subgroup G} {Q D : Subgroup X}
    (hP : (solvableResidual P).map P.subtype = K)
    (hQ : (solvableResidual Q).map Q.subtype = D) (e : P ≃* Q) :
    Nonempty (K ≃* D) := by
  let a : solvableResidual P ≃* K :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
  let b : solvableResidual Q ≃* D :=
    ((solvableResidual Q).equivMapOfInjective Q.subtype Q.subtype_injective).trans
      (MulEquiv.subgroupCongr hQ)
  exact ⟨a.symm.trans (e.solvableResidualEquiv.trans b)⟩


private instance projective_finite (m : ℕ) (hm : 1 ≤ m) : Finite (ProjectiveGroup m hm) :=
  Finite.of_equiv (MatrixGroup m hm) (Extension.projectEquiv m hm).toEquiv

/-- Determinant on the invariant plane identifies the actual solvable residual. -/
private theorem plane_parabolic_residual (m : ℕ) (hm : 1 ≤ m) :
    (solvableResidual (planeParabolic m hm)).map (planeParabolic m hm).subtype = L2 m hm := by
  let := L2_isPerfect m hm
  open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal in
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

private theorem pair_factors
    {G : Type*} [Group G] [Finite G] {L R : Subgroup G} {n : ℕ}
    (hL : faithfulLocal L)
    (hlin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (P : Fin 2 → Subgroup G)
    (hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,R] i)
    (hns : ∀ i, ¬ Group.IsSolvable (P i))
    (m : ℕ) (hm : 1 ≤ m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧ Nonempty (L ≃* L2 m hm) ∧
      Nonempty (R ≃* PointLocal.ProjectiveLocal m hm) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) := by
  have hlarge (i : Fin 2) (e : P i ≃* pointParabolic m hm) : 1 < m := by
    by_contra hn
    have heq : m = 1 := by omega
    subst m
    let := binary_point_solvable
    exact hns i (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)
  rcases he with he | he
  · obtain ⟨e⟩ := he
    have hm' := hlarge 0 e.left
    obtain ⟨a⟩ := residual_factor_equiv (hr 0)
      (PointLocal.pointParabolic_solvableResidual m hm hm') e.left
    exact (faithful_not_core_center_central hL a (point_core_center_central m hm)).elim
  obtain ⟨e⟩ := he
  have hm' := hlarge 1 e.right
  obtain ⟨a⟩ := residual_factor_equiv (hr 0) (plane_parabolic_residual m hm) e.left
  obtain ⟨b⟩ := residual_factor_equiv (hr 1)
    (PointLocal.pointParabolic_solvableResidual m hm hm') e.right
  let aq := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    ((L2QuotientEquivSL2 m hm).trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := Representation.OrthogonalFourMinus.FiniteModel.Field m)))
  have hn : n = 2*m := by
    obtain ⟨F,_,_,hF,⟨f⟩⟩ := hlin
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hcard := binary_psl_field_card_eq (f.symm.trans aq)
    rw [hF,GaloisField.card 2 (2*m) (by omega)] at hcard
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hcard
  refine ⟨hm',hn,⟨a⟩,⟨b⟩,PointLocal.FixedField m,inferInstance,inferInstance,
    PointLocal.fixedField_card m hm,?_⟩
  exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (PointLocal.projectiveQuotientByTwoCoreEquivPSL m hm)⟩


private theorem binary_extended_point_solvable :
    Group.IsSolvable (Extension.point 1 (Nat.le_refl 1)) := by
  let := binary_point_solvable
  let j : pointParabolic 1 (Nat.le_refl 1) →* Extension.point 1 (Nat.le_refl 1) := {
    toFun x := ⟨SemidirectProduct.inl x.val,(Extension.mem_point 1 (Nat.le_refl 1) _).mpr x.property⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' x y := Subtype.ext (map_mul _ _ _) }
  let q : Extension.point 1 (Nat.le_refl 1) →*
      Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.C2 :=
    SemidirectProduct.rightHom.comp (Extension.point 1 (Nat.le_refl 1)).subtype
  apply Group.isSolvable_of_ker_le_range j q
  intro x hx
  refine ⟨⟨x.val.left,(Extension.mem_point 1 (Nat.le_refl 1) _).mp x.property⟩,?_⟩
  exact Subtype.ext (SemidirectProduct.ext rfl hx.symm)

end UnitaryFactors

variable {G : Type*} [Group G] [Finite G]

/-- Removing the original S preserves both perfect solvable residuals.
The reduced common Sylow is the literal T ∩ L, without identifying it with S. -/
theorem Preparation.reduced_parabolic_residuals
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H))) :
    ∀ i : Fin 2,
      (solvableResidual (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i)).map
        (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i).subtype = ![L,R] i := by
  intro i
  have hle : ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i ≤
      ChapterF.Source.parabolic ![L,R] (sourceS L H) i := by
    rw [d.reduced_source_parabolics h hTH hp hc i]
    exact map_subtype_le _
  apply le_antisymm
    ((map_solvableResidual_mono hle).trans_eq (d.parabolic_residuals h hTH hp i))
  have hpi : Group.IsPerfect (![L,R] i) := by
    fin_cases i
    · exact Chapter1.mem_L_isPerfect h.local_mem.1.1
    · exact hp
  let := hpi
  exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans le_sup_left)

private theorem Preparation.reduced_parabolics_not_solvable
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hp : Group.IsPerfect R) :
    ∀ i : Fin 2, ¬ Group.IsSolvable (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i) := by
  intro i hs
  let := hs
  have hsol : Group.IsSolvable (![L,R] i) :=
    Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show ![L,R] i ≤ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i
        from le_sup_left.trans le_sup_left)) (inclusion_injective _)
  fin_cases i
  · exact Chapter1.mem_L_not_isSolvable h.local_mem.1.1 hsol
  · let := hp
    let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr (fun he => d.right_outside (he ▸ bot_le))
    exact Group.IsPerfect.not_isSolvable R hsol

/-- Both ordinary unitary orientations determine the same original factors.
The point factor is on the right; n = 2m > 2 and its quotient is PSL₂(2^m). -/
theorem Preparation.unitary_local_structure
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 1 ≤ m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H)) (amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧ Nonempty (L ≃* L2 m hm) ∧
      Nonempty (R ≃* PointLocal.ProjectiveLocal m hm) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) :=
  UnitaryFactors.pair_factors h.local_mem.2 h.linear
    (ChapterF.Source.parabolic ![L,R] (sourceS L H))
    (d.parabolic_residuals h hTH hp) (d.parabolics_not_solvable h hp) m hm he

/-- The extended unitary pair has the same original residual factors.
Restricting the actual compatible maps to O² of each endpoint preserves
both overlap maps and gives the ordinary comparison used in the proof. -/
theorem Preparation.unitaryExtension_local_structure
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 1 ≤ m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧ Nonempty (L ≃* L2 m hm) ∧
      Nonempty (R ≃* PointLocal.ProjectiveLocal m hm) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) := by
  have hm' : 1 < m := by
    by_contra hn
    have heq : m = 1 := by omega
    subst m
    let := UnitaryFactors.binary_extended_point_solvable
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact d.parabolics_not_solvable h hp 0
        (Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective)
    · exact d.parabolics_not_solvable h hp 1
        (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
  exact UnitaryFactors.pair_factors h.local_mem.2 h.linear
    (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L))
    (d.reduced_parabolic_residuals h hTH hp (.unitaryExtension m hm he))
    (d.reduced_parabolics_not_solvable h hp) m hm
    (d.unitaryExtension_reduced_amalgam h hTH hp m hm' he)

/-- The original unitary cores have orders q⁴ and q⁵. The latter is special
with center of order q, centralized by the right residual. This applies to
both whole-overlap orientations and to the degree-two extension. -/
theorem Preparation.unitary_core_structure
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 1 ≤ m)
    (he : (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H)) (amalgam m hm).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H)) (Extension.amalgam m hm).reverse))) :
    1 < m ∧ n = 2*m ∧
      IsElementaryAbelian 2 (pCore 2 L) ∧ Nat.card (pCore 2 L) = (2^m)^4 ∧
      Nat.card (pCore 2 R) = (2^m)^5 ∧ Nat.card (center (pCore 2 R)) = 2^m ∧
      center (pCore 2 R) = commutator (pCore 2 R) ∧
      center (pCore 2 R) = frattini (pCore 2 R) ∧
      IsElementaryAbelian 2 (center (pCore 2 R)) ∧
      (center (pCore 2 R)).map (pCore 2 R).subtype ≤ center R := by
  have hf := he.elim (d.unitary_local_structure h hTH hp m hm)
    (d.unitaryExtension_local_structure h hTH hp m hm)
  obtain ⟨hm',hn,⟨a⟩,⟨b⟩,_⟩ := hf
  let ac := (a.subgroupMap (pCore 2 L)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 a))
  let bc := (b.subgroupMap (pCore 2 R)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 b))
  have hl : IsElementaryAbelian 2 (pCore 2 L) :=
    IsElementaryAbelian.of_injective ac.toMonoidHom ac.injective
  have hz : IsElementaryAbelian 2 (center (pCore 2 R)) := by
    let := PointLocal.projectiveTwoCore_center_elementary m hm
    exact IsElementaryAbelian.of_injective (centerCongr bc).toMonoidHom (centerCongr bc).injective
  refine ⟨hm',hn,hl,(Nat.card_congr ac.toEquiv).trans (L2TwoCore_card m hm),
    (Nat.card_congr bc.toEquiv).trans (PointLocal.projectiveTwoCore_card m hm),
    (Nat.card_congr (centerCongr bc).toEquiv).trans (PointLocal.projectiveTwoCore_center_card m hm),
    ?_,?_,hz,?_⟩
  · apply map_injective (f := bc.toMonoidHom) bc.injective
    rw [center_map_equiv bc,map_commutator_eq,
      MonoidHom.range_eq_top.mpr bc.surjective,←_root_.commutator_def]
    exact PointLocal.projectiveTwoCore_center_eq_commutator m hm
  · apply map_injective (f := bc.toMonoidHom) bc.injective
    rw [center_map_equiv bc,frattini_map_equiv bc]
    exact PointLocal.projectiveTwoCore_center_eq_frattini m hm
  · exact UnitaryFactors.core_center_transport b.symm (UnitaryFactors.point_core_center_central m hm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
