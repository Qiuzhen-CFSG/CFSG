module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.SuzukiPairCentralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.ThompsonCentralizer
public import Theory.Representation.Suzuki.ComponentPairDegree
public import Theory.Representation.CliffordSubquotient
public import Theory.SpecificGroups.PSL2.PrimeCubicRank
public import Theory.SpecificGroups.FFLinearPrimeCore
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# Comparing the quiet local and full Thompson actions in every component family

The literal Suzuki component pair has zero common fixed space on the faithful
irreducible full module. If either component has fixed vectors, its fixed space
and the conjugate fixed space are disjoint, invariant under the pair, and each
has degree at least twelve. If neither does, the fully moving pair bound gives
the same full degree of at least twenty-four. The normal offender subgroup of
the pair centralizer is therefore excluded by the proved Suzuki-pair B.5
classification, retaining both individual fixed spaces and the full action kernel.

Every maximal elementary subgroup of the original Sylow fixing the local
module consequently fixes the full module. The other component families use
the cubic residual comparison, so the result applies to every original minimal
setup without a model, point-centralizer or small-offender premise. Source
uses it to assemble all selected fixed-support rows and module choice.

Source: Aschbacher--Smith B.5.6, 3.2.6 and10.1.1--3, printed pp.105,581,741--742.
Only the intrinsic Suzuki-pair calculation and literal local-kernel/offender
transfer are reused from the sibling point-control and small-offender modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterB.SourceInduction ChapterB.InternalThompsonAction BenderSuzuki.MatrixGroups

private theorem suzuki_pair_full_degree
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) Q V) (hi : ρ.IsIrreducible)
    (S : Subgroup Q) (a : Q)
    (hS : IsComponent Q S) (hne : S ≠ S.map (MulAut.conj a).toMonoidHom)
    {m : ℕ} (hm : 0 < m) (eS : S ≃* SuzukiMatrixGroup m)
    (hfix : fixedSpace ρ (S ⊔ S.map (MulAut.conj a).toMonoidHom) = ⊥) :
    24 ≤ Module.finrank (ZMod 2) V := by
  let K := S.map (MulAut.conj a).toMonoidHom
  let eK : K ≃* SuzukiMatrixGroup m := ((MulAut.conj a).subgroupMap S).symm.trans eS
  have hK : IsComponent Q K := hS.map_conj a
  let : Fact (0 < m) := ⟨hm⟩
  let : IsSimpleGroup S := eS.isSimpleGroup
  let : IsQuasisimple S := hS.2
  let : IsSimpleGroup K := eK.isSimpleGroup
  let : IsQuasisimple K := hK.2
  have hdim : Module.finrank (ZMod 2) (fixedSpace ρ S) =
      Module.finrank (ZMod 2) (fixedSpace ρ K) :=
    (fixedSpaceConjEquiv ρ S a).finrank_eq
  by_cases hzS : fixedSpace ρ S = ⊥
  · have hzK : fixedSpace ρ K = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      rw [←hdim,hzS,finrank_bot]
    have hZS : center S = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
        (fun h => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h))
    have hZK : center K = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
        (fun h => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h))
    let : ρ.IsIrreducible := hi
    let : IsSemisimpleModule (ZMod 2)[S] (Representation.asModule (ρ.comp S.subtype)) :=
      subnormal_restriction_semisimple ρ S hS.1
    have hh := Suzuki.pair_subrepresentation_finrank_ge ρ S K hS hK hne hZS hZK
      hzS hzK m hm eS ⊤ top_ne_bot
    change 8*(2*m+1) ≤ Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) at hh
    rw [finrank_top] at hh
    omega
  · have hnorm : S ⊔ K ≤ normalizer (S : Set Q) :=
      sup_le S.le_normalizer
        ((commutator_eq_bot_iff_le_centralizer.mp
          (hK.commutator_eq_bot_of_ne hS hne.symm)).trans (Subgroup.centralizer_le_normalizer _))
    let W : Subrepresentation (ρ.comp (S ⊔ K).subtype) := {
      toSubmodule := fixedSpace ρ S
      apply_mem_toSubmodule x v hv :=
        (normalizer_le_stabilizer_fixedSpace ρ S (hnorm x.property) v).mpr hv }
    have hW : W ≠ ⊥ := fun h => hzS (congrArg Subrepresentation.toSubmodule h)
    have hd := Constrained.SuzukiCentralizer.pair_submodule_degree ρ S K hm eS eK hfix W hW
    change 12 ≤ Module.finrank (ZMod 2) (fixedSpace ρ S) at hd
    have hdis : Disjoint (fixedSpace ρ S) (fixedSpace ρ K) := by
      apply disjoint_iff.mpr
      exact (ρ.invariants_comp_sup S K).symm.trans hfix
    have hh := Submodule.finrank_add_finrank_le_of_disjoint hdis
    omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original Suzuki pair centralizer has no offender on the full module. -/
theorem quiet_suzuki_full_centralizer_not_ff
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (m : ℕ) (hm : 0 < m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    letI := (source_full_module_reduced D).normal
    letI := (source_full_module_reduced D).elementary
    let q := actionMk U
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    ¬ IsFFModule ((action U).comp (centralizer (X : Set (ActionQuotient U))).subtype) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := ActionQuotient U
  let q := actionMk U
  let ρ := action U
  let X := (R.subgroupOf M).map q
  let C := centralizer (X : Set Q)
  let N := offenderSubgroup (ρ.comp C.subtype)
  let f := C.subtype.comp N.subtype
  let A := L.subgroupOf M
  let S := A.map q
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hnon
  let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let K := S.map (MulAut.conj (q tM)).toMonoidHom
  have hLM : L ≤ M := (le_componentOrbit L T).trans R.le_normalizer
  have hpair : R = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hnon)
      inf_le_right ht htn
  have hLtM : L.map (MulAut.conj t).toMonoidHom ≤ M :=
    (le_sup_right.trans hpair.ge).trans R.le_normalizer
  have hmap : (A.map (MulAut.conj tM).toMonoidHom).map q = K := by
    dsimp only [K,S]
    rw [map_map,map_map]
    congr 1
  have hsub : (L.map (MulAut.conj t).toMonoidHom).subgroupOf M =
      A.map (MulAut.conj tM).toMonoidHom := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hLtM,map_map,
      show M.subtype.comp (MulAut.conj tM).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp M.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hLM]
  have hX : X = S ⊔ K := by
    change (R.subgroupOf M).map q = _
    rw [hpair,subgroupOf_sup hLM hLtM,Subgroup.map_sup,hsub,hmap]
  obtain ⟨a⟩ := full_action_original_component_equiv D hnon
  let eS : S ≃* SuzukiMatrixGroup m := a.trans e
  let eK : K ≃* SuzukiMatrixGroup m := ((MulAut.conj (q tM)).subgroupMap S).symm.trans eS
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect R := isPerfect_iSup_conjugates L T
  let : Group.IsPerfect (R.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe R.le_normalizer).symm.toMonoidHom)
    (subgroupOfEquivOfLe R.le_normalizer).symm.surjective
  let : Group.IsPerfect X := Group.IsPerfect.map q
  let : Group.IsPerfect (S ⊔ K : Subgroup Q) := hX ▸ inferInstance
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : C.Normal := inferInstance
  have hfix : fixedSpace ρ X = ⊥ := by
    apply bot_unique
    intro z hz
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    apply (source_fullModule_fixed_eq_bot_of_many D hmany hJ).le
    refine ⟨z.toMul.property,?_⟩
    intro r hr
    let rM : M := ⟨r,R.le_normalizer hr⟩
    have hh := hz ⟨q rM,mem_map_of_mem q hr⟩
    have hact := action_apply U rM z
    exact mul_inv_eq_iff_eq_mul.mp
      ((congrArg (fun x : M => (x : G)) hact).symm.trans
        (congrArg (fun x : Additive U => ((x.toMul : M) : G)) hh))
  have hfix' : fixedSpace ρ (S ⊔ K) = ⊥ := hX ▸ hfix
  have hf := action_faithful U
  have hi := quiet_full_action_irreducible D hmany hmin hJ
  obtain ⟨hS,hK,hne⟩ := full_action_component_pair D ht htn
  rw [hmap] at hK hne
  let : Nontrivial (Additive U) := Subrepresentation.irreducible_module_nontrivial ρ
  have hfull := suzuki_pair_full_degree ρ hi S (q tM) hS hne hm eS hfix'
  let cover : SQTKQuotient KnownSimple.IsKnownSimple Q := {
    Cover := M
    kernel := centralizer (U : Set M)
    sqtk := D.simpleQTKE.twoLocal_sqtk
      (source_module_nonsolvable_uniqueness D).normalizer_maximal.1
    equiv := MulEquiv.refl Q }
  intro hff
  have hcore := normal_subgroup_twoCore_eq_bot C hu.quotient_pCore_eq_bot
  obtain ⟨B,hB⟩ := (isFFModule_iff_exists_bestOffender (ρ.comp C.subtype)).mp hff
  have hffN : IsFFModule ((ρ.comp C.subtype).comp N.subtype) :=
    ⟨B.subgroupOf N,(hB.isOffender _).subgroupOf _ (hB.le_offenderSubgroup _)⟩
  have hrange : f.range = N.map C.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  let : f.range.Normal := hrange.symm ▸ normal_restriction_offender_image ρ C
  have hzN := normal_restriction_offender_fixed_eq_bot ρ hf hi C
    (offenderSubgroup_ne_bot_of_ff _ hff)
  exact Constrained.SuzukiCentralizer.no_ff_of_normal_commuting_suzuki_pair ρ hf hi S K hm eS eK hfix'
    (Constrained.SuzukiCentralizer.pair_submodule_degree ρ S K hm eS eK hfix') hfull
    f (C.subtype_injective.comp N.subtype_injective)
    (by rintro _ ⟨x,rfl⟩; rw [←hX]; exact x.val.property)
    (offenderSubgroup_twoCore _ hcore) ((cover.subgroup C).subgroup N)
    (offenderSubgroup_restrict_eq_top _) hzN hffN


/-- Local and full Thompson centralization agree for the remaining Suzuki row. -/
theorem full_thompson_centralizes_of_local_suzuki
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (m : ℕ) (hm : 0 < m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
  by_contra h
  exact quiet_suzuki_full_centralizer_not_ff D hmany hmin hnon hJ m hm e
    (SmallOffender.Recognition.full_orbit_centralizer_ff_of_local_quiet D hnon hJ h)


open scoped MatrixGroups in
/-- Local Thompson centralization extends to the full module in every actual
non-A5 component family. Minimality is retained for the Suzuki case. -/
theorem full_thompson_centralizes_of_local
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
  cases component_quotient_model D hnon with
  | linear_even n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    apply full_thompson_centralizes_of_local_three D hnon _ hJ
    rw [Nat.card_congr e.toEquiv,←Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  | suzuki m hm he =>
    exact full_thompson_centralizes_of_local_suzuki D hmany hmin hnon hJ m (by omega) he.some
  | linear_prime p hp ho hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact full_thompson_centralizes_of_local_three D hnon
      (Theory.PSL2.prime_model_three_dvd_card hp ho hF e) hJ
  | janko he =>
    apply full_thompson_centralizes_of_local_three D hnon _ hJ
    rw [Nat.card_congr he.some.toEquiv,Janko1.card_model]
    norm_num

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
