module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Radical.Intersection
public import CFSG.Quasithin.Chapter3.Section02.SourceSelection
public import Theory.GroupTheory.ReducedNormal.QuasisimpleKernel
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.Chapter3.Section02.QrcInput

/-!
# The canonical reduced module in the 13.1.9 qrc argument

Let Y=N_L(R)^∞ and W=YT, where R=C_T(L/O∞(L)). The proved
canonical faithfulness and quasisimple quotient make Y move R₂(W).
The actual simple quotient is Y/O₂(Y). Its normal embedding in W,
with two-group quotient W/Y, forces C_W(R₂(W))=O₂(W), hence
C_T(R₂(W))=R. No simplicity assertion about W/R is needed.

The two-residual of W is the embedded Y. These results supply the module
and centralizer clauses of Hypothesis 3.1.5 and their literal maximal
counterexample application. The intersection-normalizer clause remains
a separate step of the same 13.1.9 assembly.

Source: Aschbacher--Smith, 13.1.9, printed p.869; A.4.11 and B.2.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

theorem canonical_reduced_commutator_ne_bot (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ⁅reducedTwoSubgroup (canonicalSupplement T L ⊔ (T : Subgroup G) : Subgroup G),
      (canonicalSupplement T L).subgroupOf (canonicalSupplement T L ⊔ (T : Subgroup G))⁆ ≠ ⊥ := by
  have hf := (Adequate.mem_faithfulLocalComponents_iff T _).mp
    (canonical_mem_faithfulLocalComponents h hmany hL hn)
  exact Chapter3.Section02.source_component_reduced_commutator_ne_bot T _ hf.1 hf.2
    (canonical_quasisimple h hmany hL hn)

theorem canonical_simple_twoCore_quotient (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    IsSimpleGroup (XiQuotient (canonicalSupplement T L)) := by
  let Y := canonicalSupplement (T : Subgroup G) L
  let C := Y.subgroupOf (Y ⊔ (T : Subgroup G))
  have hY := (canonical_frattini_geometry h hmany hL hn).1.1
  let : IsSimpleGroup (C ⧸ solvableRadical C) := hY.1.isSimpleGroup_quotient_solvableRadical
  let e : C ≃* Y := subgroupOfEquivOfLe le_sup_left
  let er : (C ⧸ solvableRadical C) ≃* (Y ⧸ solvableRadical Y) :=
    QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)
  let eq : (C ⧸ solvableRadical C) ≃* XiQuotient Y :=
    er.trans (QuotientGroup.quotientMulEquivOfEq (canonical_radical_eq_twoCore h hmany hL hn))
  exact eq.symm.isSimpleGroup

theorem canonical_reduced_centralizer (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    centralizer (reducedTwoSubgroup (canonicalSupplement T L ⊔ (T : Subgroup G) : Subgroup G) :
      Set (canonicalSupplement T L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (canonicalSupplement T L ⊔ (T : Subgroup G) : Subgroup G) := by
  let Y := canonicalSupplement (T : Subgroup G) L
  let W := Y ⊔ (T : Subgroup G)
  let C := Y.subgroupOf W
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    sylow_normalizes_canonicalSupplement hTL
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hTY)
  let e : C ≃* Y := subgroupOfEquivOfLe le_sup_left
  let eq : (C ⧸ pCore 2 C) ≃* XiQuotient Y :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsSimpleGroup (XiQuotient Y) := canonical_simple_twoCore_quotient h hmany hL hn
  let : IsSimpleGroup (C ⧸ pCore 2 C) := eq.isSimpleGroup
  let : IsQuasisimple (XiQuotient Y) := canonical_quasisimple h hmany hL hn
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv eq.symm
  have hz : center (C ⧸ pCore 2 C) = ⊥ :=
    (inferInstance : (center (C ⧸ pCore 2 C)).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  have hgen : C ⊔ (T : Subgroup G).subgroupOf W = ⊤ := by
    rw [← subgroupOf_sup (show Y ≤ W from le_sup_left)
      (show (T : Subgroup G) ≤ W from le_sup_right)]
    exact subgroupOf_self _
  exact reduced_quasisimple_centralizer_eq_pCore (reducedTwoSubgroup W) C
    isPReduced_reducedPSubgroup hz (canonical_reduced_commutator_ne_bot h hmany hL hn)
    (isPGroup_quotient_of_sup_eq_top C _ T.isPGroup'.comap_subtype hgen)

/-- The actual embedded source module, without any choice of constituent. -/
abbrev canonicalReducedModule (T L : Subgroup G) : Subgroup G :=
  (reducedTwoSubgroup (canonicalSupplement T L ⊔ T : Subgroup G)).map
    (canonicalSupplement T L ⊔ T).subtype

theorem canonicalReducedModule_ne_bot (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    canonicalReducedModule T L ≠ ⊥ := by
  intro hz
  let W := canonicalSupplement (T : Subgroup G) L ⊔ (T : Subgroup G)
  have hzero : reducedTwoSubgroup W = ⊥ :=
    (map_eq_bot_iff_of_injective (reducedTwoSubgroup W) W.subtype_injective).mp hz
  apply canonical_reduced_commutator_ne_bot h hmany hL hn
  rw [hzero, commutator_bot_left]

theorem canonical_sylow_centralizer (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (T : Subgroup G) ⊓ centralizer (canonicalReducedModule T L : Set G) =
      radicalSylowCentralizer T L := by
  let W := canonicalSupplement T L ⊔ (T : Subgroup G)
  have he := congrArg (map W.subtype) (canonical_reduced_centralizer h hmany hL hn)
  rw [map_centralizer_subtype] at he
  have hh := congrArg (fun A : Subgroup G => (T : Subgroup G) ⊓ A) he
  rw [← inf_assoc, inf_eq_left.mpr (show (T : Subgroup G) ≤ W from le_sup_right)] at hh
  change (T : Subgroup G) ⊓ centralizer (canonicalReducedModule T L : Set G) =
    (T : Subgroup G) ⊓ W.pCoreIn 2 at hh
  rw [(canonical_frattini_geometry h hmany hL hn).2.1,
    inf_eq_right.mpr (radicalSylowCentralizer_le _ _)] at hh
  exact hh

theorem canonical_embedded_twoResidual (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    let Y := canonicalSupplement (T : Subgroup G) L
    let W := Y ⊔ (T : Subgroup G)
    (pResidual 2 W).map W.subtype = Y := by
  have hf := (Adequate.mem_faithfulLocalComponents_iff T _).mp
    (canonical_mem_faithfulLocalComponents h hmany hL hn)
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  exact embedded_pResidual_join_pGroup _ _ hf.2.1.2.1 T.isPGroup'
    (sylow_normalizes_canonicalSupplement hTL)

/-- The radical Sylow intersection inside L is the literal Sylow
intersection with O∞(L), using relative normality in LT. -/
theorem radicalSylowCentralizer_inf_component (T : Sylow 2 G) {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    radicalSylowCentralizer T L ⊓ L =
      (T : Subgroup G) ⊓ (solvableRadical L).map L.subtype := by
  let W := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf W
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  have he : ((solvableRadical A).map A.subtype).map W.subtype =
      (solvableRadical L).map L.subtype := by
    rw [map_map, show W.subtype.comp A.subtype = L.subtype.comp e.toMonoidHom from rfl,
      ← map_map, map_solvableRadical_equiv e]
  have hi := congrArg (map W.subtype)
    (congrArg (map A.subtype) (radical_subgroupOf_normal A))
  rw [subgroupOf_map_subtype, map_inf _ _ _ W.subtype_injective,
    map_subgroupOf_eq_of_le (show L ≤ W from le_sup_left), he] at hi
  rw [radicalSylowCentralizer_eq_inf_radical T hTL, inf_assoc, hi]

/-- The subgroup whose normality is needed in case (I) is Sylow in the
actual embedded solvable radical of L. -/
theorem radicalSylowCentralizer_inf_component_isSylow (T : Sylow 2 G) {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsSylowIn 2 (radicalSylowCentralizer T L ⊓ L)
      ((solvableRadical L).map L.subtype) := by
  rw [radicalSylowCentralizer_inf_component T hTL]
  let W := L ⊔ (T : Subgroup G)
  let D := (solvableRadical L).map L.subtype
  have hWD : W ≤ normalizer (D : Set G) :=
    (sup_le L.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  let : (D.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer hWD
  exact IndexTwo.isSylowIn_inf_of_subnormal
    ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩
    ((map_subtype_le _).trans le_sup_left)
    (inferInstance : (D.subgroupOf W).Normal).isSubnormal

/-- All module clauses of the qrc configuration, with the literal action
image and Sylow centralizer. The intersection-normalizer clause is separate. -/
theorem canonical_reduced_action (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    let W := canonicalSupplement T L ⊔ (T : Subgroup G)
    let V := canonicalReducedModule T L
    W ≤ normalizer (L : Set G) ∧ V ≠ ⊥ ∧ V ≤ W ∧
      ∃ hWV : W ≤ normalizer (V : Set G),
        IsElementaryAbelian 2 V ∧
        pCore 2 (ChapterD.internalActionImage W V hWV) = ⊥ ∧
        W.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let W := canonicalSupplement T L ⊔ (T : Subgroup G)
  let V := canonicalReducedModule (T : Subgroup G) L
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hv : IsPReduced 2 (reducedTwoSubgroup W) := isPReduced_reducedPSubgroup
  let := hv.elementary
  have hWV : W ≤ normalizer (V : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (reducedTwoSubgroup W).le_normalizer_map W.subtype
  have hi : V.subgroupOf W = reducedTwoSubgroup W :=
    comap_map_eq_self_of_injective W.subtype_injective _
  refine ⟨sup_le ((canonicalSupplement_le _ _).trans L.le_normalizer) hTL,
    canonicalReducedModule_ne_bot h hmany hL hn, map_subtype_le _, hWV,
    IsElementaryAbelian.map W.subtype, ?_, ?_⟩
  · exact Chapter3.Section02.internalActionImage_core_of_reduced W V
      (map_subtype_le _) hWV (hi.symm ▸ hv)
  · exact (canonical_frattini_geometry h hmany hL hn).2.1.trans
      (canonical_sylow_centralizer h hmany hL hn).symm

/-- The failure-of-movement branch makes J(T) centralize the actual reduced module. -/
theorem thompson_centralizes_canonicalReducedModule (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 0 ≤ radicalSylowCentralizer T L) :
    ChapterB.thompsonJ (T : Subgroup G) 0 ≤ centralizer (canonicalReducedModule T L : Set G) :=
  hJ.trans ((canonical_sylow_centralizer h hmany hL hn).symm.le.trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple.Supplements
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The original maximal-counterexample application constructs the same
nonzero reduced module and its entire Sylow centralizer, with no uniqueness premise. -/
theorem Hypothesis1331.canonical_reduced_action_of_many
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ L : Subgroup G, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      ¬ IsQuasisimple (XiQuotient L) ∧
      let W := canonicalSupplement T L ⊔ (T : Subgroup G)
      let V := canonicalReducedModule T L
      IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      W ≤ normalizer (L : Set G) ∧ V ≠ ⊥ ∧ V ≤ W ∧
      ∃ hWV : W ≤ normalizer (V : Set G), IsElementaryAbelian 2 V ∧
        pCore 2 (ChapterD.internalActionImage W V hWV) = ⊥ ∧
        W.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  obtain ⟨L,_,hL₀,hL,hLn,hM,_⟩ := h.maximal_counterexample_of_many hmany hn
  exact ⟨L,hL₀,hL,hLn.2,hM,canonical_reduced_action h.hypothesis1311 hmany hL hLn.2⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
