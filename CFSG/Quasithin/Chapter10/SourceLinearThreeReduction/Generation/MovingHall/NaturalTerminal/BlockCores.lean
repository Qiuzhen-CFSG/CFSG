module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OriginalAxes
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.CoreEquality
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.SymmetricGeometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.ResidualBaumann
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SylowBorel
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BorelNormalizer

/-!
# General-field block cores in the original moving pair

Whole-core Thompson movement and the vanishing fixed center identify the
entire original two-core with its residual commutator. The natural marking
then recovers the intrinsic block over the original field. The same argument
on the H-star side uses its actual seed centralizer and residual cover.
These equalities discharge the core premises of the literal odd-commutator
Sylow calculation in either block orientation.

Simultaneous blockhood and terminal overcomponent geometry remain with
`qt-d-10-nona5-moving-hall-three`, which also discharges natural marking
and the original Hall placement.

Source: Aschbacher–Smith 10.2.3(4), printed pp.746–747; this reuses the
field-independent parts of original block recovery and E.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterC ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]
local instance blockCoreFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
include D in
private theorem original_full_core_fixed_residual
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    pCore 2 (localJoin T L) ⊓ centralizer (pResidual 2 (localJoin T L) : Set (localJoin T L)) = ⊥ := by
  let X := localJoin T L
  apply (map_eq_bot_iff_of_injective _ X.subtype_injective).mp
  apply bot_unique
  apply le_trans ?_ (source_orbit_core_centralizer_eq_bot hz).le
  apply le_inf (map_mono inf_le_left)
  have hh := (map_mono (f := X.subtype) (show
    pCore 2 X ⊓ centralizer (pResidual 2 X : Set X) ≤
      centralizer (pResidual 2 X : Set X) from inf_le_right)).trans
    (map_centralizer_le_centralizer_image _ X.subtype)
  change _ ≤ centralizer ((pResidual 2 X).map X.subtype : Set G) at hh
  rwa [source_join_residual D] at hh

/-- Actual movement and vanishing fixed center make the entire core residual-generated. -/
theorem Context.original_block_full_core_moved
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    pCore 2 (localJoin T L) = ⁅pCore 2 (localJoin T L),pResidual 2 (localJoin T L)⁆ := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let Q := pCore 2 X
  have hQ : IsPReduced 2 Q := by
    refine ⟨inferInstance,source_original_block_local_core_elementary D ctx.nonnormal hb hz,?_⟩
    have hc : centralizer (Q : Set X) = Q := by
      let := source_original_block_local_core_elementary D ctx.nonnormal hb hz
      apply le_antisymm
      · exact (centralizer_le (source_parabolic_module_reduced D).le_pCore).trans_eq
          (source_natural_local_module_kernel_eq_twoCore D degree hdegree hF e ctx.nonnormal
            (source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving))
      · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
    let f := QuotientGroup.quotientMulEquivOfEq hc.symm
    rw [←pCore_map_iso 2 f,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
  let := hQ.normal
  let := hQ.elementary
  let C := centralizer (Q : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation Q q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hJ := source_original_full_core_thompson_moves D ctx.hstar ctx.moving
  have hP := source_natural_minimal_parabolic D e degree hdegree hF ctx.nonnormal
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun Z _ _ => ChapterA.Section02.theoremA_knownSimple (G := Z))
    (fun Z _ _ => ChapterA.Section02.theoremC_knownSimple (G := Z))
    D.simpleQTKE T D.maximal
  have hs := ChapterE.ThompsonAction.source_nonsolvable_natural_factors
    (D.local_internal_module hu).sqtk S hP Q hQ (source_join_not_solvable D) hJ
  rcases hs with ⟨hqs,_⟩ | ⟨d,_,_⟩
  · have hcore : pCore 2 (X ⧸ C) = ⊥ := hQ.quotient_pCore_eq_bot
    have hne : q.ker ≠ ⊤ := by
      intro he
      apply hJ
      change elementaryAbelianMaxJ (S : Subgroup X) ≤ C
      rw [←hk,he]
      exact le_top
    have hp := (ChapterB.minimalParabolic_reduced_image S hP q hq hcore hne).2
    have hff : IsFFModule α := source_original_full_core_ff D ctx.nonnormal hb hz ctx.hstar ctx.moving
    have hr := (ChapterB.source_quasisimple_fitting_eq_residual (S.mapSurjective hq) hp Y
      (ChapterB.offender_generation (S.mapSurjective hq) hp α hff hcore).2 hqs).2
    have hker : q.ker ≤ ChapterB.minimalParabolicCore S hP := by
      rw [hk]
      exact ChapterB.RankOneBaumann.reduced_centralizer_le_core S hP Q hQ hJ
    let : Group.IsSolvable (ChapterB.minimalParabolicCore S hP) :=
      ChapterB.minimalParabolic_core_solvable S hP
    let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hker)
    have hL : (L.subgroupOf X).IsCComponent := by
      change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
      rw [componentOrbit_sup]
      exact D.maximal.1.1
    have hnormal := hL.normal_of_solvable_kernel_quasisimple_residual _ q hq hr
    exact (ctx.nonnormal (le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      ((le_componentOrbit L T).trans le_sup_left)).mp hnormal))).elim
  · have hh := ChapterE.ThompsonAction.paired_module_le_moved_sup_alpha_fixed
      S hP Q hQ hJ q hq hk d Q inf_le_left
    rw [original_full_core_fixed_residual D hz,sup_bot_eq] at hh
    exact le_antisymm hh (commutator_le_left _ _)

theorem Context.original_block_core_eq
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    pCore 2 L = blockU L := by
  let X := localJoin T L
  let A := L.subgroupOf X
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 ctx.nonnormal
  let tX : X := ⟨t,(show (T : Subgroup G) ≤ X from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tX).toMonoidHom
  have hbB : IsBlock B := hb.map_equiv (MulAut.conj tX)
  have hmapA : A.map X.subtype = L := map_subgroupOf_eq_of_le hLX
  have hmapB : B.map X.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tX).toMonoidHom from rfl,map_map]
    rw [show X.subtype.comp (MulAut.conj tX).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp X.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map X.subtype) he).symm.trans hmapA)
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLX).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLX).symm))
  have hc := hb.commutator_eq_bot_of_quasisimple_quotient hbB hqA hne
  have hmapPair : (A ⊔ B).map X.subtype = localOrbit T L := by
    rw [Subgroup.map_sup,hmapA,hmapB,hpair]
  have hR : pResidual 2 X = A ⊔ B := by
    apply map_injective X.subtype_injective
    exact (source_join_residual D).trans hmapPair.symm
  let a : A ≃* L := subgroupOfEquivOfLe hLX
  let b : A ≃* B := (MulAut.conj tX).subgroupMap A
  let f : B ≃* L := b.symm.trans a
  have hZB : center B = ⊥ := by
    apply bot_unique
    intro z hzB
    have hzL : f z ∈ center L := (centerCongr f ⟨z,hzB⟩).property
    rw [source_original_block_center_eq_bot D ctx.nonnormal hb hz,mem_bot] at hzL
    exact mem_bot.mpr (f.injective (hzL.trans f.map_one.symm))
  have hmov : pCore 2 X = ⁅pCore 2 X,A ⊔ B⁆ := by
    rw [←hR]
    exact ctx.original_block_full_core_moved D degree hdegree hF e hb hz
  have hcore := hb.core_eq_blockU_of_pair_core_generated hbB hc hZB hmov
  have hm := congrArg (map a.toMonoidHom) hcore
  rw [pCore_map_iso,RankOne.Solvable.blockU_map_equiv] at hm
  exact hm



omit [Finite G] in
/-- Recover the intrinsic natural block marking from the actual moved section. -/
private theorem natural_block_of_moved_section
    (K U : Subgroup G) (hK : ChapterC.IsShort K)
    (hmoved : (ChapterC.blockU K).map K.subtype = ⁅U,K⁆)
    (e : (K ⧸ pCore 2 K) ≃* SL(2,F))
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (c : BinaryConjugationSection K ⁅U,K⁆ (⁅U,K⁆ ⊓ centralizer (K : Set G))
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) :
    ChapterC.IsL2EvenBlock K n := by
  let ρ := SL2.BinarySmall.natural (K := F)
  let r : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)) := {
    toFun := fun g => (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toAddEquiv.toMultiplicative
    map_one' := by apply MulEquiv.ext; intro w; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun ρ.map_one w.toAdd)
    map_mul' := fun g k => by apply MulEquiv.ext; intro w; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (ρ.map_mul g k) w.toAdd) }
  let m := ChapterC.blockModelOfIdentifiedMovedSection K U hmoved e ρ r (fun _ _ => rfl) c
  refine ⟨hn,hK,F,inferInstance,inferInstance,by simpa using hF,
    ⟨F,inferInstance,inferInstance,by simpa using hF,⟨e.trans (Theory.PSL2.sl2QuotientEquiv F)⟩⟩,
    r,⟨m⟩,fun _ _ => rfl⟩

/-- The original natural coordinates identify the entire block two-core. -/
theorem Context.original_natural_block_core
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L))) :
    IsL2EvenBlock L n ∧ pCore 2 L = blockU L ∧ center L = ⊥ := by
  have hz := (ctx.fixed_centers_of_natural_marking D n hn hF e mark hBR).1
  have hLX : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hs := RankOne.Solvable.isShort_of_equiv (subgroupOfEquivOfLe hLX) hb.short
  exact ⟨natural_block_of_moved_section L D.fullModule hs
    (source_original_blockU_eq_full_moved D hb) e n hn hF mark.1.some,
    ctx.original_block_core_eq D n hn hF e hb hz,
    source_original_block_center_eq_bot D ctx.nonnormal hb hz⟩

omit [Finite G] in
private theorem local_center_trivial
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥) :
    omegaCenterIn (T.subtype hTH : Subgroup H) ⊓ center H = ⊥ := by
  apply bot_unique
  intro z hz'
  have hzm : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    have hh := mem_map_of_mem H.subtype hz'.1
    change (z : G) ∈ (omegaOneCenterAmbient (T.subtype hTH : Subgroup H)).map H.subtype at hh
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective] at hh
    have hSm : (T.subtype hTH : Subgroup H).map H.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le hTH
    rwa [hSm] at hh
  have hzc : (z : G) ∈ centralizer (H : Set G) := by
    intro h hh
    exact congrArg H.subtype (mem_center_iff.mp hz'.2 ⟨h,hh⟩)
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hz ▸ ⟨hzm,hzc⟩)))

/-- In the comparison block orientation the entire H-star core is moved. -/
theorem Context.comparison_block_full_core_moved
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (K : Subgroup H) (hb : IsBlock K)
    (hR : pResidual 2 H = K ∨
      ∃ t : H, pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    IsElementaryAbelian 2 (pCore 2 H) ∧ pCore 2 H = ⁅pCore 2 H,pResidual 2 H⁆ := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H
  have hz := local_center_trivial H ctx.hstar.1.1.2
    (ctx.fixed_centers_of_natural_marking D n hn hF e mark hBR).2
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (ChapterE.generationParameter_le_one_of_solvable (G := H))) ctx.large
  exact source_block_residual_full_core_moved
    (Chapter3.sqtk_of_mem_H D.simpleQTKE ctx.hstar.1.1.1) S
    (source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large) U
    (source_hstar_omega_orbit_reduced D ctx.hstar) hs
    (ctx.hstar_thompson_moves_omega_orbit D n hn hF e)
    (source_hstar_fitting_eq_core D ctx.hstar) Z
    (subgroupOf_mono H (le_conjugateSpanBy _ _))
    (ctx.seed_centralizer_eq_sylow D n hn hF e mark hBR) hz K hb hR

/-- The selected block has its actual U-core and a full common Baumann Sylow. -/
theorem Context.comparison_block_core_and_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (K : Subgroup H) (hb : IsBlock K)
    (hR : pResidual 2 H = K ∨
      ∃ t : H, pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    center K = ⊥ ∧ pCore 2 K = blockU K ∧
      Chapter1.IsSylowIn 2 (baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ⊓ K) K := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H
  have hz := local_center_trivial H ctx.hstar.1.1.2
    (ctx.fixed_centers_of_natural_marking D n hn hF e mark hBR).2
  have hm := (ctx.comparison_block_full_core_moved D n hn hF e mark hBR K hb hR).2
  obtain ⟨hcenter,hcore⟩ := source_block_center_and_core_of_residual_cover
    (source_hstar_fitting_eq_core D ctx.hstar) K hb hR
    (core_residual_fixed_eq_bot_of_omega_center S hz) hm
  have hCZ := ctx.seed_centralizer_eq_sylow D n hn hF e mark hBR
  have hkr : centralizer (U : Set H) ≤ pResidual 2 H := by
    rw [source_hstar_action_kernel_eq_core_of_seed_centralizer D ctx.hstar hCZ,hm]
    exact Subgroup.commutator_le_right (H₁ := pCore 2 H) (H₂ := pResidual 2 H)
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (ChapterE.generationParameter_le_one_of_solvable (G := H))) ctx.large
  have hS := source_baumann_sylow_in_residual_of_seed_centralizer
    (Chapter3.sqtk_of_mem_H D.simpleQTKE ctx.hstar.1.1.1) S
    (source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large) U
    (source_hstar_omega_orbit_reduced D ctx.hstar) hs
    (ctx.hstar_thompson_moves_omega_orbit D n hn hF e)
    Z (subgroupOf_mono H (le_conjugateSpanBy _ _)) hCZ hkr
  have hKR : K ≤ pResidual 2 H := by
    rcases hR with he | ⟨t,he⟩
    · exact he.ge
    · exact he ▸ le_sup_left
  exact ⟨hcenter,hcore,
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hKR hb.subnormal.subgroupOf⟩


/-- The original natural block removes the core premise in the odd-axis Sylow theorem. -/
theorem Context.original_block_axis_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (A : Subgroup G) (hAL : A ≤ L) (hAB : A ≤ B.map H.subtype)
    (hne : A ≠ ⊥) (hAS : A ≤ normalizer (baumann (T : Subgroup G) : Set G)) :
    ⁅baumann (T : Subgroup G),A⁆ = baumann (T : Subgroup G) ⊓ L ∧
      Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),A⁆ L := by
  obtain ⟨hL,hcore,_⟩ := ctx.original_natural_block_core D n hn hF e mark hBR hb
  let X := localOrbit T L ⊔ baumann (T : Subgroup G)
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  have hXM : X ≤ D.maximalLocal := sup_le (localOrbit T L).le_normalizer
    (inf_le_left.trans (le_normalizer_componentOrbit L T))
  have hsub := (D.component_in_maximalLocal.subgroupOf_of_le hLX hXM).subnormal
  exact IsL2EvenBlock.ambient_odd_commutator_sylow_of_subnormal
    L (baumann (T : Subgroup G)) A X hL hcore
    (ctx.original_baumann_sylow D n hn hF e) hLX hsub hAL
    (ctx.odd_card_of_le_hall_image A hAB) hne hAS
    (ctx.baumann_normalizes_original D n hn hF e)


/-- Whole-core recovery puts the actual Baumann subgroup inside the original orbit. -/
theorem Context.original_block_baumann_le_orbit
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L))) :
    baumann (T : Subgroup G) ≤ localOrbit T L := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hP := source_natural_minimal_parabolic D e n hn hF ctx.nonnormal
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving
  obtain ⟨d,E,⟨c⟩,hexchange⟩ := ctx.original_paired_linear D n hn hF e
  obtain ⟨_,_,_,_,⟨_,hBq⟩,_⟩ :=
    RankOneBaumann.PairedFactorOrbit.source_images_and_fixedSpace S hP
      U hU hJ q hq hk d E c hexchange
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [source_natural_paired_field_card D n hn hF e ctx.nonnormal hJ d E c hexchange,hF]
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hp
    omega
  let A := SL(2,E.Carrier)
  let : Group.IsPerfect A := GorensteinWalter.sl2_isPerfect_of_card_gt_three E.Carrier hlarge
  let : Group.IsPerfect (A × A) := ⟨by
    rw [commutator_def,←top_prod_top,commutator_prod_prod]
    simp only [←commutator_def,Group.IsPerfect.commutator_eq_top]⟩
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := c.action.groupEquiv.symm.toMonoidHom) c.action.groupEquiv.symm.surjective
  let : Group.IsNilpotent ((X ⧸ C) ⧸ pResidual 2 (X ⧸ C)) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  have hY : Y ≤ (pResidual 2 X).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact le_of_isPerfect_of_solvable_quotient Y _
  have hkr : q.ker ≤ pResidual 2 X := by
    rw [hk]
    change centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) ≤ _
    rw [source_natural_local_module_kernel_eq_twoCore D n hn hF e ctx.nonnormal hJ,
      ctx.original_block_full_core_moved D n hn hF e hb
        (ctx.fixed_centers_of_natural_marking D n hn hF e mark hBR).1]
    exact commutator_le_right _ _
  have hB : baumann (S : Subgroup X) ≤ pResidual 2 X := by
    have hm := map_le_iff_le_comap.mp (hBq.le.trans (inf_le_right.trans hY))
    rwa [comap_map_eq,sup_eq_left.mpr hkr] at hm
  have hBm := map_mono (f := X.subtype) hB
  have hSm : (S : Subgroup X).map X.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le le_sup_right
  have hBmEq := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
  change (baumann (S : Subgroup X)).map X.subtype = baumann ((S : Subgroup X).map X.subtype) at hBmEq
  rw [hSm] at hBmEq
  rwa [source_join_residual D,hBmEq] at hBm

/-- The original Borel now supplies the normalization premise of the axis Sylow theorem. -/
theorem Context.original_block_hall_normalizes_baumann
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L))) :
    B.map H.subtype ≤ normalizer (baumann (T : Subgroup G) : Set G) := by
  have hBR := hBB.trans ((map_subtype_le _).trans inf_le_left)
  have hBS := ctx.original_baumann_sylow D n hn hF e
  have hBO := ctx.original_block_baumann_le_orbit D n hn hF e mark hBR hb
  have hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (localOrbit T L) := by
    simpa only [sup_eq_left.mpr hBO] using hBS
  have he : baumann (T : Subgroup G) = (T : Subgroup G) ⊓ localOrbit T L :=
    ((Chapter1.isSylowIn_iff.mp hS).2.2 _ (T.isPGroup'.to_le inf_le_left)
      (le_inf inf_le_left hBO) inf_le_right).symm
  rw [he]
  exact hBB.trans ((map_subtype_le _).trans inf_le_right)


private theorem natural_odd_sylow_faithful
    {X : Type*} [Group X] [Finite X] {n : ℕ}
    (hX : IsL2EvenBlock X n) (hcore : pCore 2 X = blockU X)
    (hz : center X = ⊥) (P : Sylow 2 X) (A : Subgroup X)
    (hodd : Odd (Nat.card A)) : A ⊓ centralizer (P : Set X) = ⊥ := by
  let D := A ⊓ centralizer (P : Set X)
  by_contra hne
  have hfixed := hX.sylow_odd_fixed_le_center hcore P D
    (hodd.of_dvd_nat (card_dvd_of_le (show D ≤ A from inf_le_left))) hne
  have hp : (P : Subgroup X) ≤ center X := by
    intro x hx
    exact hfixed ⟨hx,fun d hd => (hd.2 x hx).symm⟩
  have hUP : blockU X ≤ (P : Subgroup X) := blockU_le_core.trans
    (pCore_isPGroup.le_sylow_of_normal P)
  have hu : blockU X = ⊥ := bot_unique (hUP.trans (hp.trans hz.le))
  have hh := hX.2.1.irreducible.1
  rw [hu,bot_inf_eq] at hh
  exact lt_irrefl _ hh

private theorem ambient_natural_odd_sylow_faithful
    (K P A : Subgroup G) {n : ℕ} (hK : IsL2EvenBlock K n)
    (hcore : pCore 2 K = blockU K) (hz : center K = ⊥)
    (hP : Chapter1.IsSylowIn 2 P K) (hAK : A ≤ K)
    (hodd : Odd (Nat.card A)) : A ⊓ centralizer (P : Set G) = ⊥ := by
  obtain ⟨Q,hQ⟩ := hP
  have ho : Odd (Nat.card (A.subgroupOf K)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv]
  have hf := natural_odd_sylow_faithful hK hcore hz Q (A.subgroupOf K) ho
  apply bot_unique
  intro a ha
  have hm : (⟨a,hAK ha.1⟩ : K) ∈ A.subgroupOf K ⊓ centralizer (Q : Set K) := by
    refine ⟨ha.1,?_⟩
    intro q hq
    exact Subtype.ext (ha.2 q (hQ ▸ mem_map_of_mem K.subtype hq))
  rw [hf,mem_bot] at hm
  exact mem_bot.mpr (congrArg K.subtype hm)

/-- Core recovery and Borel placement discharge the actual terminal faithfulness
and local SQTK premises on each original first-factor Hall axis. -/
theorem Context.original_block_axis_borel
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (A : Subgroup G) (hAL : A ≤ L) (hAB : A ≤ B.map H.subtype) (hne : A ≠ ⊥) :
    ⁅baumann (T : Subgroup G),A⁆ = baumann (T : Subgroup G) ⊓ L ∧
      Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),A⁆ L ∧
      A ⊓ centralizer ((⁅baumann (T : Subgroup G),A⁆ : Subgroup G) : Set G) = ⊥ ∧
      IsSQTK KnownSimple.IsKnownSimple
        (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) := by
  have hBR := hBB.trans ((map_subtype_le _).trans inf_le_left)
  obtain ⟨hLn,hcore,hz⟩ := ctx.original_natural_block_core D n hn hF e mark hBR hb
  have hAS := hAB.trans (ctx.original_block_hall_normalizes_baumann D n hn hF e mark hBB hb)
  obtain ⟨he,hP⟩ := ctx.original_block_axis_sylow D n hn hF e mark hBR hb A hAL hAB hne hAS
  have hf := ambient_natural_odd_sylow_faithful L _ A hLn hcore hz hP hAL
    (ctx.odd_card_of_le_hall_image A hAB)
  have hc := IsShort.borel_core_ne_bot L _ A hLn.2.1 hP
    (normalizer_commutator_ge_right (baumann (T : Subgroup G)) A)
  exact ⟨he,hP,hf,source_natural_borel_normalizer_sqtk D _ hc⟩


/-- The source terminal assembly now needs only the overcomponent geometry in
this block orientation. This task retains that geometry and blockhood. -/
theorem Context.terminal_of_original_block_overcomponent
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (A K : Subgroup G) (hAL : A ≤ L) (hAB : A ≤ B.map H.subtype)
    (hA : Nat.card A = 2 ^ n - 1)
    (hK : K ∈ Chapter1.cComponentsIn
      (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)))
    (hmodel : Chapter1.Section02.LocalModels.IsSL K 3 (2 ^ n) ∨ ClassicalGroup.IsPSL K 3 (2 ^ n))
    (hcentral : K ≤ centralizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) :
    Nonempty (TerminalConfiguration T L (B.map H.subtype) n) := by
  have hlarge : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
  have hne : A ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hA
    omega
  obtain ⟨_,_,hf,hsq⟩ := ctx.original_block_axis_borel D n hn hF e mark hBB hb A hAL hAB hne
  exact ⟨⟨A,K,hAB,hAL.trans (le_componentOrbit L T),Or.inl hAL,hA,hf,hsq,hK,hmodel,hcentral⟩⟩

private theorem natural_degree_eq_of_quotient
    {X E : Type*} [Group X] [Field E] [Finite E]
    {m n : ℕ} (h : IsL2EvenBlock X m)
    (e : (X ⧸ pCore 2 X) ≃* SL(2,E)) (hE : Nat.card E = 2 ^ n) : m = n := by
  obtain ⟨_,_,F',_,_,hF',_,ρ,⟨d⟩,_⟩ := h
  have hSL : Nat.card SL(2,F') = Nat.card SL(2,E) :=
    (Nat.card_congr d.quotientIso.toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
    BenderSuzuki.External.huppert614_card_specialLinearGroup] at hSL
  have ha : 1 < Nat.card F' := Finite.one_lt_card
  have hb : 1 < Nat.card E := Finite.one_lt_card
  have hsa : 1 ≤ Nat.card F' ^ 2 := by nlinarith
  have hsb : 1 ≤ Nat.card E ^ 2 := by nlinarith
  have hpa := Nat.sub_add_cancel hsa
  have hpb := Nat.sub_add_cancel hsb
  have heq : Nat.card F' = Nat.card E := by
    apply le_antisymm <;> by_contra! hh
    · have hmul := Nat.mul_lt_mul_of_lt_of_le hh
        (by nlinarith : Nat.card E ^ 2 - 1 ≤ Nat.card F' ^ 2 - 1)
        (by nlinarith : 0 < Nat.card F' ^ 2 - 1)
      omega
    · have hmul := Nat.mul_lt_mul_of_lt_of_le hh
        (by nlinarith : Nat.card F' ^ 2 - 1 ≤ Nat.card E ^ 2 - 1)
        (by nlinarith : 0 < Nat.card E ^ 2 - 1)
      omega
  rw [hF',hE] at heq
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) heq

/-- The selected block's retained quotient fixes its natural degree to the
original degree; its core and Sylow premises are simultaneously discharged. -/
theorem Context.comparison_natural_block_core
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (K : Subgroup H) (hb : IsBlock K) (hnat : ∃ m, IsL2EvenBlock K m)
    {E : Type*} [Field E] [Finite E] (hE : Nat.card E = Nat.card F)
    (eK : (K ⧸ pCore 2 K) ≃* SL(2,E))
    (hR : pResidual 2 H = K ∨
      ∃ t : H, pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    IsL2EvenBlock K n ∧ pCore 2 K = blockU K ∧ center K = ⊥ ∧
      Chapter1.IsSylowIn 2 (baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ⊓ K) K := by
  obtain ⟨m,hm⟩ := hnat
  have heq := natural_degree_eq_of_quotient hm eK (hE.trans hF)
  obtain ⟨hz,hcore,hS⟩ := ctx.comparison_block_core_and_sylow D n hn hF e mark hBR K hb hR
  exact ⟨heq ▸ hm,hcore,hz,hS⟩

end CFSG.Quasithin.Chapter10.MovingHall
