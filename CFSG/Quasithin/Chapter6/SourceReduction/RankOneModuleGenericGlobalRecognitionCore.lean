module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue
public import Theory.GroupTheory.PCoreRestriction

/-!
# Core and Sylow consequences of concrete generic comparisons

For Q = O₂(RS), restriction gives R ∩ Q ≤ O₂(R). Thus the desired
index is bounded by the image of Q in the right parabolic modulo its
solvable residual R. In the ordinary nonbinary models the residual
contains a Sylow two-subgroup and hence every two-subgroup of the
parabolic. The binary exceptions have a solvable endpoint and are
incompatible with the original perfect factors.

In the degree-two unitary extension, the literal parity map has target
C₂. Every two-subgroup in its kernel lies in the ordinary residual, so
its index modulo the extended residual is at most two. This avoids the
incorrect full-overlap core identity discussed in UnitaryFourExtension.
The proof retains the whole overlap, both odd Cartans, the U₅(4) row,
and the general Ree parameter.

The same model calculations put the original S inside both local factors
in every ordinary row. The remaining degree-two unitary comparison keeps
both actual maps and has parameter greater than one, since its binary
point endpoint is solvable. The ordinary containment supplies the common
Sylow and enlarged-core calculations of 5.2.7 in the Sylow extension.
For the degree-two extension, a two-element belongs to either residual
exactly when its parity is trivial. Both amalgam maps preserve that parity
on the whole overlap. Thus S ∩ L = S ∩ R, and Sylow maximality identifies
the reduced common subgroup with both T ∩ L and T ∩ R. Moreover a normal
two-subgroup of the whole overlap has trivial parity by the diagonal-torus
calculation in UnitaryCore. It therefore lies in both factors, providing
the containment needed for the enlarged cores in 5.2.7.

The Chapter12 consumer removes the separate core-bound assumption from
its whole-residual deduction. An actual concrete comparison remains an
input: this module proves its numerical consequence, not exhaustive
F.1.12 recognition. Exhaustive classification and ambient completion
recognition remain with qt-d-1222-rankone-generic-global; original
uniqueness retains its independent producer.

Source: Aschbacher–Smith 5.2.6, printed pp.650–651; F.1.12, pp.262–264,
and F.4.29 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace CoreComparison

private theorem two_subgroup_le_normal_of_sylow
    {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (P : Sylow 2 X) (hP : (P : Subgroup X) ≤ N)
    (U : Subgroup X) (hU : IsPGroup 2 U) : U ≤ N := by
  have hn : ¬ 2 ∣ N.index := fun hd => P.not_dvd_index
    (hd.trans (index_dvd_of_le hP))
  obtain ⟨k,hk⟩ := hU.exists_card_eq
  apply (relIndex_eq_one).mp
  exact Nat.eq_one_of_dvd_coprimes
    (by rw [hk]; exact Nat.prime_two.coprime_pow_of_not_dvd hn)
    (N.relIndex_dvd_index_of_normal U) (N.relIndex_dvd_card U)

private theorem two_subgroup_le_residual_of_model_sylow
    {X : Type*} [Group X] [Finite X] (P K : Subgroup X)
    (hr : (solvableResidual P).map P.subtype = K)
    (T : Sylow 2 X) (hT : (T : Subgroup X) ≤ K)
    (U : Subgroup P) (hU : IsPGroup 2 U) : U ≤ solvableResidual P := by
  have hKP : K ≤ P := hr ▸ map_subtype_le _
  apply two_subgroup_le_normal_of_sylow (solvableResidual P)
    (T.subtype (hT.trans hKP)) ?_ U hU
  intro x hx
  have hxK : (x : X) ∈ K := hT hx
  rw [←hr] at hxK
  obtain ⟨y,hy,he⟩ := hxK
  exact (Subtype.ext he : y = x) ▸ hy

private theorem source_core_index_le_of_parabolic
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 ≃* X)
    (hb : ∀ U : Subgroup X, IsPGroup 2 U → (solvableResidual X).relIndex U ≤ 2) :
    (R.pCoreIn 2).relIndex ((R ⊔ sourceS L H).pCoreIn 2) ≤ 2 := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  let Q := (R ⊔ sourceS L H).pCoreIn 2
  have hQP : Q ≤ P := (pCoreIn_le 2 _).trans le_sup_left
  have hr : R.subgroupOf P = solvableResidual P := by
    have hr' : (solvableResidual P).map P.subtype = R :=
      d.parabolic_residuals h hTH hp 1
    rw [←hr']
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have he := hb ((Q.subgroupOf P).map e.toMonoidHom)
    ((isPGroup_pCoreIn 2 _).comap_subtype.map e.toMonoidHom)
  rw [← map_solvableResidual_eq e.toMonoidHom e.surjective,
    relIndex_map_map_of_injective _ _ e.injective, ←hr,
    relIndex_subgroupOf hQP] at he
  have hc : R ⊓ Q ≤ R.pCoreIn 2 := inf_pCoreIn_le_of_le 2 le_sup_left
  have hi := relIndex_le_of_le_left (L := Q) hc index_ne_zero_of_finite
  rw [inf_relIndex_right] at hi
  exact hi.trans he

private theorem two_residual_index_bound_of_extension
    {X Y Z : Type*} [Group X] [Finite X] [Group Y] [Finite Y] [Group Z] [Finite Z]
    (j : Y →* X) (hj : Function.Injective j) (f : X →* Z)
    (hker : j.range = f.ker) (hZ : Nat.card Z ≤ 2)
    (hY : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ solvableResidual Y)
    (U : Subgroup X) (hU : IsPGroup 2 U) : (solvableResidual X).relIndex U ≤ 2 := by
  have hle : U ⊓ f.ker ≤ solvableResidual X := by
    rw [←hker, inf_comm, ←map_comap_eq]
    exact (map_mono (hY (U.comap j) (hU.comap_of_injective j hj))).trans
      (map_solvableResidual_le j)
  have hi := relIndex_le_of_le_left (L := U) hle index_ne_zero_of_finite
  rw [inf_relIndex_left, relIndex_ker] at hi
  exact hi.trans ((Nat.card_le_card_of_injective (U.map f).subtype
    (U.map f).subtype_injective).trans hZ)

open ChapterF.GreenBook.LieModels

private theorem linear_two_subgroup_le_residual
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) (j : Bool)
    (U : Subgroup (Matrix.PSL3.LinearThree.CoveredLocals.parabolic F j))
    (hU : IsPGroup 2 U) : U ≤ solvableResidual _ := by
  open Matrix.PSL3.LinearThree in
  have hc : 4 ≤ Nat.card F := by
    rw [hF]; exact Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hr : (solvableResidual (CoveredLocals.parabolic F j)).map
      (CoveredLocals.parabolic F j).subtype = CoveredLocals.localProjective F j := by
    cases j
    · exact ParabolicResiduals.lineParabolic_residual F hc
    · exact ParabolicResiduals.pointParabolic_residual F hc
  apply two_subgroup_le_residual_of_model_sylow _ _ hr
    (unipotentSylow F (by omega) hF) ?_ U hU
  cases j
  · exact (LinearThree.sylow_le_localFactors F (by omega) hF).2
  · exact (LinearThree.sylow_le_localFactors F (by omega) hF).1

private theorem symplectic_two_subgroup_le_residual
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) (j : Bool)
    (U : Subgroup (if j then Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)
      else Theory.SpecificGroups.SymplecticFour.planeParabolic : Subgroup _))
    (hU : IsPGroup 2 U) : U ≤ solvableResidual _ := by
  open Theory.SpecificGroups.SymplecticFour in
  have hr : (solvableResidual (if j then pointParabolic (F := F) else planeParabolic : Subgroup (Sp F))).map
      (if j then pointParabolic (F := F) else planeParabolic : Subgroup (Sp F)).subtype =
      (if j then pointLocal (F := F) else planeLocal : Subgroup (Sp F)) := by
    cases j
    · let := planeLocal_perfect hF hm
      exact planeParabolic_solvableResidual_eq_of_perfect
    · let := pointLocal_perfect hF hm
      exact pointParabolic_solvableResidual_eq_of_perfect
  apply two_subgroup_le_residual_of_model_sylow _ _ hr (unipotentSylow hF hm.le) ?_ U hU
  cases j
  · exact SymplecticFour.sylow_le_planeLocal hF hm.le
  · exact SymplecticFour.sylow_le_pointLocal hF hm.le

private theorem two_subgroup_le_residual_of_perfect
    {X : Type*} [Group X] (P K : Subgroup X) [Group.IsPerfect K]
    (hKP : K ≤ P) (U : Subgroup P)
    (hU : U.map P.subtype ≤ K) : U ≤ solvableResidual P := by
  have hh := hU.trans (le_map_solvableResidual_of_isPerfect K P hKP)
  exact (map_le_map_iff_of_injective P.subtype_injective).mp hh

open UnitaryFour

private instance unitaryProjectiveFinite (m : ℕ) (hm : 1 ≤ m) :
    Finite (ProjectiveGroup m hm) :=
  Finite.of_equiv (MatrixGroup m hm) (Extension.projectEquiv m hm).toEquiv

private instance unitaryExtensionFinite (m : ℕ) (hm : 1 ≤ m) :
    Finite (Extension.ProjectiveExtension m hm) :=
  Finite.of_injective (fun x : Extension.ProjectiveExtension m hm => (x.left,x.right))
    (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

private theorem unitary_point_two_subgroup_le_residual (m : ℕ) (hm : 1 < m)
    (U : Subgroup (pointParabolic m hm.le)) (hU : IsPGroup 2 U) :
    U ≤ solvableResidual _ := by
  let := PointLocal.projectiveLocal_isPerfect m hm.le hm
  apply two_subgroup_le_residual_of_perfect _ (PointLocal.ProjectiveLocal m hm.le)
    (by rw [←PointLocal.pointParabolic_solvableResidual m hm.le hm]; exact map_subtype_le _) U
  exact PointLocal.twoSubgroup_le_projectiveLocal m hm.le _ (hU.map _)
    (map_subtype_le _)

private theorem unitary_plane_two_subgroup_le_residual (m : ℕ) (hm : 1 ≤ m)
    (U : Subgroup (planeParabolic m hm)) (hU : IsPGroup 2 U) :
    U ≤ solvableResidual _ := by
  let := L2_isPerfect m hm
  exact two_subgroup_le_residual_of_perfect _ (L2 m hm) (L2_le_planeParabolic m hm) U
    (two_subgroup_le_L2 m hm _ (hU.map _) (map_subtype_le _))

private def unitaryOrdinaryEmbedding (m : ℕ) (hm : 1 ≤ m) (j : Bool) :
    (if j then pointParabolic m hm else planeParabolic m hm : Subgroup _) →*
      (if j then Extension.point m hm else Extension.plane m hm : Subgroup _) where
  toFun x := ⟨SemidirectProduct.inl x.val, by
    cases j
    · exact (Extension.mem_plane m hm _).mpr x.property
    · exact (Extension.mem_point m hm _).mpr x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

private theorem unitaryOrdinaryEmbedding_injective (m : ℕ) (hm : 1 ≤ m) (j : Bool) :
    Function.Injective (unitaryOrdinaryEmbedding m hm j) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z => z.val.left) he)

private def unitaryParity (m : ℕ) (hm : 1 ≤ m) (j : Bool) :
    (if j then Extension.point m hm else Extension.plane m hm : Subgroup _) →*
      Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.C2 :=
  SemidirectProduct.rightHom.comp
    (if j then Extension.point m hm else Extension.plane m hm : Subgroup _).subtype

private theorem unitaryOrdinaryEmbedding_range (m : ℕ) (hm : 1 ≤ m) (j : Bool) :
    (unitaryOrdinaryEmbedding m hm j).range = (unitaryParity m hm j).ker := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    rfl
  · intro hx
    refine ⟨⟨x.val.left,?_⟩,?_⟩
    · cases j
      · exact (Extension.mem_plane m hm _).mp x.property
      · exact (Extension.mem_point m hm _).mp x.property
    · exact Subtype.ext (SemidirectProduct.ext rfl hx.symm)

private theorem unitary_extension_two_index (m : ℕ) (hm : 1 < m) (j : Bool)
    (U : Subgroup (if j then Extension.point m hm.le else Extension.plane m hm.le : Subgroup _))
    (hU : IsPGroup 2 U) : (solvableResidual _).relIndex U ≤ 2 := by
  apply two_residual_index_bound_of_extension (unitaryOrdinaryEmbedding m hm.le j)
    (unitaryOrdinaryEmbedding_injective m hm.le j) (unitaryParity m hm.le j)
    (unitaryOrdinaryEmbedding_range m hm.le j) ?_ ?_ U hU
  · change Nat.card (Multiplicative (ZMod 2)) ≤ 2
    norm_num
  · intro V hV
    cases j
    · exact unitary_plane_two_subgroup_le_residual m hm.le V hV
    · exact unitary_point_two_subgroup_le_residual m hm V hV

private theorem unitary_binary_point_solvable : Group.IsSolvable (pointParabolic 1 (Nat.le_refl 1)) := by
  open Theory.SpecificGroups.ClassicalUnitary in
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

private theorem unitary_binary_extended_point_solvable : Group.IsSolvable (Extension.point 1 (Nat.le_refl 1)) := by
  let : Group.IsSolvable (if true then pointParabolic 1 (Nat.le_refl 1)
      else planeParabolic 1 (Nat.le_refl 1) : Subgroup _) := unitary_binary_point_solvable
  apply Group.isSolvable_of_ker_le_range (unitaryOrdinaryEmbedding 1 (Nat.le_refl 1) true)
    (unitaryParity 1 (Nat.le_refl 1) true)
  exact (unitaryOrdinaryEmbedding_range 1 (Nat.le_refl 1) true).symm.le

end CoreComparison

open ChapterF.GreenBook

/-- Every concrete catalogue comparison bounds the original right core
extension by two. Exhaustive comparison is not assumed as a theorem, and
no core bound, Sylow identification with the whole overlap, or restriction
of the whole residual quotient to PSL₂ is added to the source inputs. -/
theorem Preparation.core_index_le_two_of_comparison
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H))) :
    (R.pCoreIn 2).relIndex ((R ⊔ sourceS L H).pCoreIn 2) ≤ 2 := by
  have simple_bound {X : Type} [Group X] [Finite X]
      (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 ≃* X)
      (hb : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ solvableResidual X) :=
    CoreComparison.source_core_index_le_of_parabolic d h hTH hp e
      (fun U hU => (relIndex_eq_one.mpr (hb U hU)).le.trans (by decide : 1 ≤ 2))
  cases hc with
  | linear F m hm hF he =>
    have hmn := (d.linear_amalgam_blocks h hTH hp F hm hF he).1
    have hm' : 1 < m := hmn ▸ h.exponent
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact simple_bound e.right (CoreComparison.linear_two_subgroup_le_residual F hm' hF false)
    · exact simple_bound e.right (CoreComparison.linear_two_subgroup_le_residual F hm' hF true)
  | symplectic F m hm hF he =>
    have hmn := (d.symplectic_amalgam_blocks h hTH hp F hm hF he).1
    have hm' : 1 < m := hmn ▸ h.exponent
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact simple_bound e.right (CoreComparison.symplectic_two_subgroup_le_residual F hm' hF false)
    · exact simple_bound e.right (CoreComparison.symplectic_two_subgroup_le_residual F hm' hF true)
  | g2 F he =>
    open Atlas.G2.LieParabolicSetup in
    rcases he with he | he
    · exact (d.not_g2_short_left_parabolic h hTH hp (he.map fun e => e.left)).elim
    · obtain ⟨e⟩ := he
      have hq : 2 < Nat.card F := by
        by_contra hn
        have hF : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
        let := G2Short.parabolic_solvable_of_card_two hF
        exact d.parabolics_not_solvable h hp 1
          (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
      exact simple_bound e.right (CoreComparison.two_subgroup_le_residual_of_model_sylow
        (parabolic₁ (F := F)) (local₁ (F := F))
        (Atlas.G2.HigherFieldResiduals.parabolic₁_residual hq)
        (Atlas.G2.LieParabolicSetup.sylow (F := F)) (sylow_le_local₁ (F := F)))
  | triality m hm he =>
    open _root_.Triality.Standard _root_.Triality.Standard.Parabolics in
    rcases he with he | he
    · exact (d.not_triality_arms_left_amalgam h hTH hp (binaryParameters m hm) rfl he).elim
    · obtain ⟨e⟩ := he
      have hm' := d.triality_parameter_gt_one h hp m hm e
      let P := binaryParameters m hm
      have hq : 2 < P.q := by
        change 2 < 2^m
        exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hm'
      exact simple_bound e.right (CoreComparison.two_subgroup_le_residual_of_model_sylow
        (parabolic P .arms) (localFactor P .arms)
        (parabolic_solvableResidual_map P rfl hq .arms)
        (LieModels.Triality.sylow P rfl) (LieModels.Triality.sylow_le_localFactor P rfl .arms))
  | ree m he =>
    rcases he with he | he
    · exact (d.not_ree_unreversed h hTH hp m he).elim
    · obtain ⟨e⟩ := he
      have hm := d.ree_parameter_positive h hp m 1 .suzuki e.right
      exact simple_bound e.right (CoreComparison.two_subgroup_le_residual_of_model_sylow
        (ReeF4.Parabolics.parabolic m .suzuki) (ReeF4.Parabolics.localFactor m .suzuki)
        (ReeF4.Parabolics.parabolic_solvableResidual_map hm .suzuki)
        (LieModels.ReeFour.sylow m) (LieModels.ReeFour.sylow_le_localFactor m .suzuki))
  | unitary m hm he =>
    have hm' : 1 < m := by
      by_contra hn
      have hm1 : m = 1 := by omega
      subst m
      let := CoreComparison.unitary_binary_point_solvable
      rcases he with he | he <;> obtain ⟨e⟩ := he
      · exact d.parabolics_not_solvable h hp 0
          (Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective)
      · exact d.parabolics_not_solvable h hp 1
          (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact simple_bound e.right (CoreComparison.unitary_plane_two_subgroup_le_residual m hm)
    · exact simple_bound e.right (CoreComparison.unitary_point_two_subgroup_le_residual m hm')
  | unitaryExtension m hm he =>
    have hm' : 1 < m := by
      by_contra hn
      have hm1 : m = 1 := by omega
      subst m
      let := CoreComparison.unitary_binary_extended_point_solvable
      rcases he with he | he <;> obtain ⟨e⟩ := he
      · exact d.parabolics_not_solvable h hp 0
          (Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective)
      · exact d.parabolics_not_solvable h hp 1
          (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact CoreComparison.source_core_index_le_of_parabolic d h hTH hp e.right
        (CoreComparison.unitary_extension_two_index m hm' false)
    · exact CoreComparison.source_core_index_le_of_parabolic d h hTH hp e.right
        (CoreComparison.unitary_extension_two_index m hm' true)
  | unitaryFive M he =>
    rcases he with he | he
    · exact (d.not_unitaryFive_unreversed h hTH hp M he).elim
    · obtain ⟨e⟩ := he
      apply simple_bound e.right
      intro U hU
      exact IsPGroup.le_normal_of_index_primeTo M.leftLocal U hU
        (by rw [M.leftLocal_index_eq_three]; decide)
  | exceptional c he =>
    have hn := d.not_exceptional_parabolic_models h hp c
    exact (he.elim hn.1 hn.2).elim


namespace CoreComparison

private theorem source_sylow_le_factor_of_parabolic
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R) (i : Fin 2)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* X)
    (hb : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ solvableResidual X) :
    sourceS L H ≤ ![L,R] i := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have he := hb (((sourceS L H).subgroupOf P).map e.toMonoidHom)
    (((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map e.toMonoidHom)
  rw [← map_solvableResidual_eq e.toMonoidHom e.surjective,
    map_le_map_iff_of_injective e.injective] at he
  have hm := map_mono (f := P.subtype) he
  rwa [map_subgroupOf_eq_of_le hSP,d.parabolic_residuals h hTH hp i] at hm

end CoreComparison

/-- The L₃ comparison puts the original S in both local factors,
in either orientation. This is the ordinary-row containment used in 5.2.8. -/
theorem Preparation.linear_sourceS_le_factors
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (LieModels.LinearThree.amalgam F).reverse)) :
    ∀ i : Fin 2, sourceS L H ≤ ![L,R] i := by
  have hmn := (d.linear_amalgam_blocks h hTH hp F hm hF he).1
  have hm' : 1 < m := hmn ▸ h.exponent
  rcases he with he | he <;> obtain ⟨e⟩ := he <;> intro i <;> fin_cases i
  · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 0 e.left
      (CoreComparison.linear_two_subgroup_le_residual F hm' hF true)
  · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 1 e.right
      (CoreComparison.linear_two_subgroup_le_residual F hm' hF false)
  · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 0 e.left
      (CoreComparison.linear_two_subgroup_le_residual F hm' hF false)
  · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 1 e.right
      (CoreComparison.linear_two_subgroup_le_residual F hm' hF true)

/-- The Sp₄ comparison puts the original S in both local factors,
in either orientation. This is the ordinary-row containment used in 5.2.8. -/
theorem Preparation.symplectic_sourceS_le_factors
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (LieModels.SymplecticFour.amalgam F).reverse)) :
    ∀ i : Fin 2, sourceS L H ≤ ![L,R] i := by
  have hmn := (d.symplectic_amalgam_blocks h hTH hp F hm hF he).1
  have hm' : 1 < m := hmn ▸ h.exponent
  rcases he with he | he <;> obtain ⟨e⟩ := he <;> intro i <;> fin_cases i
  · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 0 e.left
      (CoreComparison.symplectic_two_subgroup_le_residual F hm' hF true)
  · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 1 e.right
      (CoreComparison.symplectic_two_subgroup_le_residual F hm' hF false)
  · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 0 e.left
      (CoreComparison.symplectic_two_subgroup_le_residual F hm' hF false)
  · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 1 e.right
      (CoreComparison.symplectic_two_subgroup_le_residual F hm' hF true)

/-- The triality comparison puts the original S in both factors. The impossible
arms-left orientation is excluded using the original faithful left action. -/
theorem Preparation.triality_sourceS_le_factors
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    ∀ i : Fin 2, sourceS L H ≤ ![L,R] i := by
  open _root_.Triality.Standard _root_.Triality.Standard.Parabolics in
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hTH hp (binaryParameters m hm) rfl he).elim
  · obtain ⟨e⟩ := he
    have hm' := d.triality_parameter_gt_one h hp m hm e
    let P := binaryParameters m hm
    have hq : 2 < P.q := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hm'
    intro i
    fin_cases i
    · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 0 e.left (CoreComparison.two_subgroup_le_residual_of_model_sylow
        (parabolic P .central) (localFactor P .central)
        (parabolic_solvableResidual_map P rfl hq .central)
        (LieModels.Triality.sylow P rfl) (LieModels.Triality.sylow_le_localFactor P rfl .central))
    · exact CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp 1 e.right (CoreComparison.two_subgroup_le_residual_of_model_sylow
        (parabolic P .arms) (localFactor P .arms)
        (parabolic_solvableResidual_map P rfl hq .arms)
        (LieModels.Triality.sylow P rfl) (LieModels.Triality.sylow_le_localFactor P rfl .arms))

/-- In every ordinary concrete row, the original S lies in both factors.
The actual degree-two unitary comparison is retained as the other alternative.
This proves the Sylow part of 5.2.6 from a comparison; it does not prove
exhaustiveness of the comparison catalogue. -/
theorem Preparation.sourceS_le_factors_or_unitaryExtension
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H))) :
    (∀ i : Fin 2, sourceS L H ≤ ![L,R] i) ∨
      ∃ (m : ℕ) (hm : 1 < m),
        Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
          (LieModels.UnitaryFour.Extension.amalgam m hm.le)) ∨
        Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
          (LieModels.UnitaryFour.Extension.amalgam m hm.le).reverse) := by
  have transfer {X : Type} [Group X] [Finite X] (i : Fin 2)
      (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* X)
      (hb : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ solvableResidual X) :=
    CoreComparison.source_sylow_le_factor_of_parabolic d h hTH hp i e hb
  cases hc with
  | linear F m hm hF he =>
    exact Or.inl (d.linear_sourceS_le_factors h hTH hp F hm hF he)
  | symplectic F m hm hF he =>
    exact Or.inl (d.symplectic_sourceS_le_factors h hTH hp F hm hF he)
  | g2 F he =>
    open Atlas.G2.LieParabolicSetup in
    rcases he with he | he
    · exact (d.not_g2_short_left_parabolic h hTH hp (he.map fun e => e.left)).elim
    · obtain ⟨e⟩ := he
      have hq : 2 < Nat.card F := by
        by_contra hn
        have hF : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
        let := G2Short.parabolic_solvable_of_card_two hF
        exact d.parabolics_not_solvable h hp 1
          (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
      left
      intro i
      fin_cases i
      · exact transfer 0 e.left (CoreComparison.two_subgroup_le_residual_of_model_sylow
          (parabolic₂ (F := F)) (local₂ (F := F))
          (Atlas.G2.HigherFieldResiduals.parabolic₂_residual hq)
          (Atlas.G2.LieParabolicSetup.sylow (F := F)) (sylow_le_local₂ (F := F)))
      · exact transfer 1 e.right (CoreComparison.two_subgroup_le_residual_of_model_sylow
          (parabolic₁ (F := F)) (local₁ (F := F))
          (Atlas.G2.HigherFieldResiduals.parabolic₁_residual hq)
          (Atlas.G2.LieParabolicSetup.sylow (F := F)) (sylow_le_local₁ (F := F)))
  | triality m hm he =>
    exact .inl (d.triality_sourceS_le_factors h hTH hp m hm he)
  | ree m he =>
    rcases he with he | he
    · exact (d.not_ree_unreversed h hTH hp m he).elim
    · obtain ⟨e⟩ := he
      have hm := d.ree_parameter_positive h hp m 1 .suzuki e.right
      left
      intro i
      fin_cases i
      · exact transfer 0 e.left (CoreComparison.two_subgroup_le_residual_of_model_sylow
          (ReeF4.Parabolics.parabolic m .linear) (ReeF4.Parabolics.localFactor m .linear)
          (ReeF4.Parabolics.parabolic_solvableResidual_map hm .linear)
          (LieModels.ReeFour.sylow m) (LieModels.ReeFour.sylow_le_localFactor m .linear))
      · exact transfer 1 e.right (CoreComparison.two_subgroup_le_residual_of_model_sylow
          (ReeF4.Parabolics.parabolic m .suzuki) (ReeF4.Parabolics.localFactor m .suzuki)
          (ReeF4.Parabolics.parabolic_solvableResidual_map hm .suzuki)
          (LieModels.ReeFour.sylow m) (LieModels.ReeFour.sylow_le_localFactor m .suzuki))
  | unitary m hm he =>
    have hm' : 1 < m := by
      by_contra hn
      have hm1 : m = 1 := by omega
      subst m
      let := CoreComparison.unitary_binary_point_solvable
      rcases he with he | he <;> obtain ⟨e⟩ := he
      · exact d.parabolics_not_solvable h hp 0
          (Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective)
      · exact d.parabolics_not_solvable h hp 1
          (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
    left
    rcases he with he | he <;> obtain ⟨e⟩ := he <;> intro i <;> fin_cases i
    · exact transfer 0 e.left (CoreComparison.unitary_point_two_subgroup_le_residual m hm')
    · exact transfer 1 e.right (CoreComparison.unitary_plane_two_subgroup_le_residual m hm)
    · exact transfer 0 e.left (CoreComparison.unitary_plane_two_subgroup_le_residual m hm)
    · exact transfer 1 e.right (CoreComparison.unitary_point_two_subgroup_le_residual m hm')
  | unitaryExtension m hm he =>
    have hm' : 1 < m := by
      by_contra hn
      have hm1 : m = 1 := by omega
      subst m
      let := CoreComparison.unitary_binary_extended_point_solvable
      rcases he with he | he <;> obtain ⟨e⟩ := he
      · exact d.parabolics_not_solvable h hp 0
          (Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective)
      · exact d.parabolics_not_solvable h hp 1
          (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
    exact Or.inr ⟨m,hm',he⟩
  | unitaryFive M he =>
    rcases he with he | he
    · exact (d.not_unitaryFive_unreversed h hTH hp M he).elim
    · obtain ⟨e⟩ := he
      left
      intro i
      fin_cases i
      · apply transfer 0 e.left
        intro U hU
        exact IsPGroup.le_normal_of_index_primeTo M.rightLocal U hU
          (by rw [M.rightLocal_index]; decide)
      · apply transfer 1 e.right
        intro U hU
        exact IsPGroup.le_normal_of_index_primeTo M.leftLocal U hU
          (by rw [M.leftLocal_index_eq_three]; decide)
  | exceptional c he =>
    have hn := d.not_exceptional_parabolic_models h hp c
    exact (he.elim hn.1 hn.2).elim


namespace CoreComparison
open ChapterF.GreenBook.LieModels.UnitaryFour

private theorem two_subgroup_residual_iff_kernel
    {X Y Z : Type*} [Group X] [Group Y] [Group Z] [Group.IsSolvable Z]
    (j : Y →* X) (hj : Function.Injective j) (f : X →* Z)
    (hker : j.range = f.ker)
    (hY : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ solvableResidual Y)
    (U : Subgroup X) (hU : IsPGroup 2 U) {x : X} (hx : x ∈ U) :
    x ∈ solvableResidual X ↔ f x = 1 := by
  constructor
  · intro hr
    have hm := map_solvableResidual_le f (mem_map_of_mem f hr)
    simpa only [solvableResidual_eq_bot, mem_bot] using hm
  · intro hk
    have hr : x ∈ j.range := hker.symm ▸ hk
    obtain ⟨y,rfl⟩ := hr
    exact map_solvableResidual_le j (mem_map_of_mem j
      (hY (U.comap j) (hU.comap_of_injective j hj) hx))

private theorem unitary_extension_two_subgroup_residual_iff
    (m : ℕ) (hm : 1 < m) (j : Bool)
    (U : Subgroup (if j then Extension.point m hm.le else Extension.plane m hm.le : Subgroup _))
    (hU : IsPGroup 2 U) {x} (hx : x ∈ U) :
    x ∈ solvableResidual _ ↔ unitaryParity m hm.le j x = 1 := by
  apply two_subgroup_residual_iff_kernel (unitaryOrdinaryEmbedding m hm.le j)
    (unitaryOrdinaryEmbedding_injective m hm.le j) (unitaryParity m hm.le j)
    (unitaryOrdinaryEmbedding_range m hm.le j) ?_ U hU hx
  intro V hV
  cases j
  · exact unitary_plane_two_subgroup_le_residual m hm.le V hV
  · exact unitary_point_two_subgroup_le_residual m hm V hV

private theorem source_factor_mem_iff_unitary_parity
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (i : Fin 2) (m : ℕ) (hm : 1 < m) (j : Bool)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃*
      (if j then Extension.point m hm.le else Extension.plane m hm.le : Subgroup _))
    {x : G} (hx : x ∈ sourceS L H) :
    x ∈ ![L,R] i ↔ unitaryParity m hm.le j (e ⟨x,(show sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) i from
        le_sup_right.trans le_sup_left) hx⟩) = 1 := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  let y : P := ⟨x,hSP hx⟩
  have hy : y ∈ (sourceS L H).subgroupOf P := hx
  have hh := unitary_extension_two_subgroup_residual_iff m hm j
    (((sourceS L H).subgroupOf P).map e.toMonoidHom)
    (((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map e.toMonoidHom)
    (mem_map_of_mem e.toMonoidHom hy)
  rw [← map_solvableResidual_eq e.toMonoidHom e.surjective,
    mem_map_iff_mem e.injective] at hh
  have hr := d.parabolic_residuals h hTH hp i
  have hrx : x ∈ ![L,R] i ↔ y ∈ solvableResidual P := by
    rw [← hr]
    exact mem_map_iff_mem (x := y) P.subtype_injective
  exact hrx.trans hh

end CoreComparison

/-- In the degree-two unitary comparison, the same parity map on the whole
intersection detects both residuals. Thus their intersections with the original
S agree, without identifying that S with the reduced common Sylow. -/
theorem Preparation.unitaryExtension_source_intersections
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 1 < m)
    (he : Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (LieModels.UnitaryFour.Extension.amalgam m hm.le)) ∨
      Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (LieModels.UnitaryFour.Extension.amalgam m hm.le).reverse)) :
    sourceS L H ⊓ L = sourceS L H ⊓ R := by
  have hSP (i : Fin 2) : sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) i :=
    le_sup_right.trans le_sup_left
  have hmemb {x : G} (hx : x ∈ sourceS L H) : x ∈ L ↔ x ∈ R := by
    let b : (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 : Subgroup G) :=
      ⟨x,hSP 0 hx,hSP 1 hx⟩
    change x ∈ ![L,R] 0 ↔ x ∈ ![L,R] 1
    rcases he with he | he
    · obtain ⟨e⟩ := he
      rw [CoreComparison.source_factor_mem_iff_unitary_parity d h hTH hp
        0 m hm true e.left hx,
        CoreComparison.source_factor_mem_iff_unitary_parity d h hTH hp
        1 m hm false e.right hx]
      change (e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left b)).val.right = 1 ↔
        (e.right ((sourceParabolicAmalgam ![L,R] (sourceS L H)).right b)).val.right = 1
      rw [e.left_commutes,e.right_commutes]
      rfl
    · obtain ⟨e⟩ := he
      rw [CoreComparison.source_factor_mem_iff_unitary_parity d h hTH hp
        0 m hm false e.left hx,
        CoreComparison.source_factor_mem_iff_unitary_parity d h hTH hp
        1 m hm true e.right hx]
      change (e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left b)).val.right = 1 ↔
        (e.right ((sourceParabolicAmalgam ![L,R] (sourceS L H)).right b)).val.right = 1
      rw [e.left_commutes,e.right_commutes]
      rfl
  ext x
  exact ⟨fun hx => ⟨hx.1,(hmemb hx.1).mp hx.2⟩,
    fun hx => ⟨hx.1,(hmemb hx.1).mpr hx.2⟩⟩

/-- The common Sylow in 5.2.7 exists for every concrete catalogue row,
including the degree-two unitary extension. Its definition uses the original
ambient Sylow T; in the extension it need not be the original sourceS. -/
theorem Preparation.common_sylow_of_comparison
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H))) :
    (T : Subgroup G) ⊓ L = (T : Subgroup G) ⊓ R := by
  have hi : sourceS L H ⊓ L = sourceS L H ⊓ R := by
    rcases d.sourceS_le_factors_or_unitaryExtension h hTH hp hc with hs | ⟨m,hm,he⟩
    · exact (inf_eq_left.mpr (hs 0)).trans (inf_eq_left.mpr (hs 1)).symm
    · exact d.unitaryExtension_source_intersections h hTH hp m hm he
  obtain ⟨P,hP⟩ := (show ∃ P : Sylow 2 R,
    (P : Subgroup R).map R.subtype = sourceS L H ⊓ R from d.sylow 1)
  have hPT : (P : Subgroup R) ≤ (T : Subgroup G).subgroupOf R := by
    intro x hx
    exact sourceS_le_sylow h.sylow_normalizes hTH
      (hP ▸ mem_map_of_mem R.subtype hx).1
  have he := congrArg (Subgroup.map R.subtype)
    (P.is_maximal' T.isPGroup'.comap_subtype hPT)
  change ((T : Subgroup G).subgroupOf R).map R.subtype = (P : Subgroup R).map R.subtype at he
  rw [subgroupOf_map_subtype,hP] at he
  exact d.left_intersection.symm.trans (hi.trans he.symm)

/-- Normal two-subgroups of the whole source overlap lie in both factors
in either unitary-extension orientation. The subgroup need not be sourceS;
this applies to the enlarged cores, whose normality is already available. -/
theorem Preparation.unitaryExtension_normal_two_subgroup_le_factors
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R Q : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hQ : IsPGroup 2 Q) (hQS : Q ≤ sourceS L H)
    (hN : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 ≤ normalizer (Q : Set G))
    (m : ℕ) (hm : 1 < m)
    (he : Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (LieModels.UnitaryFour.Extension.amalgam m hm.le)) ∨
      Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (LieModels.UnitaryFour.Extension.amalgam m hm.le).reverse)) :
    ∀ i : Fin 2, Q ≤ ![L,R] i := by
  let I := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
    ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hSP (i : Fin 2) : sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) i :=
    le_sup_right.trans le_sup_left
  let : (Q.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hN
  have hparity (e : I ≃* LieModels.UnitaryFour.Extension.overlap m hm.le)
      (x : I) (hx : x.val ∈ Q) : (e x).val.right = 1 := by
    let U := (Q.subgroupOf I).map e.toMonoidHom
    let : U.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
    have hcore : U ≤ pCore 2 (LieModels.UnitaryFour.Extension.overlap m hm.le) :=
      le_sSup ⟨inferInstance,hQ.comap_subtype.map e.toMonoidHom⟩
    exact UnitaryCore.unitaryExtension_overlap_twoCore_parity m hm.le (e x)
      (hcore (mem_map_of_mem e.toMonoidHom hx))
  intro i x hx
  let b : I := ⟨x,hSP 0 (hQS hx),hSP 1 (hQS hx)⟩
  rcases he with he | he
  · obtain ⟨e⟩ := he
    have hb := hparity e.middle b hx
    fin_cases i
    · apply (CoreComparison.source_factor_mem_iff_unitary_parity d h hTH hp
        0 m hm true e.left (hQS hx)).mpr
      change (e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left b)).val.right = 1
      rw [e.left_commutes]
      exact hb
    · apply (CoreComparison.source_factor_mem_iff_unitary_parity d h hTH hp
        1 m hm false e.right (hQS hx)).mpr
      change (e.right ((sourceParabolicAmalgam ![L,R] (sourceS L H)).right b)).val.right = 1
      rw [e.right_commutes]
      exact hb
  · obtain ⟨e⟩ := he
    have hb := hparity e.middle b hx
    fin_cases i
    · apply (CoreComparison.source_factor_mem_iff_unitary_parity d h hTH hp
        0 m hm false e.left (hQS hx)).mpr
      change (e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left b)).val.right = 1
      rw [e.left_commutes]
      exact hb
    · apply (CoreComparison.source_factor_mem_iff_unitary_parity d h hTH hp
        1 m hm true e.right (hQS hx)).mpr
      change (e.right ((sourceParabolicAmalgam ![L,R] (sourceS L H)).right b)).val.right = 1
      rw [e.right_commutes]
      exact hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
