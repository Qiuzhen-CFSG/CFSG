module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Noncontainment
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.IndexTwoNormalizer
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# Preparing the small terminal component rows

For the specified lifted component, the original flag geometry supplies the
literal G.10 action, constituent selection, orthogonal pairing and point
Sylow. The lift is either its T-conjugate span or has two conjugates exchanged
by an actual member of T. Its dotted span is the full normal component orbit.

The restricted action kernel is solvable. When the given image is A₅ or A₆,
it is exactly the solvable radical, with an equivalence induced by the original
quotient map. The final row consumer therefore marks K/R(K). No identification
with K/O₂(K), A₆ diagram action, or paired symplectic normalizer is assumed.
Those remain obligations of the small-row exclusion, not conclusions here.

Source: Aschbacher--Smith 1.2.1(3), G.10.6--7, and the nonsolvable paragraph
of 14.3.15, printed pp.504, 359--360, and 994. The three small-row exclusions
use 14.3.6(1--3) and G.11.2(2),(7),(9),(10), pp.991--992 and 364--367.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The supplied image component forces nonsolvability of the actual terminal group. -/
theorem ComponentLift.terminal_not_solvable
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) : ¬ Group.IsSolvable F.TerminalHdot := by
  intro hs
  let := hs
  exact not_isComponent_of_solvable (F.terminalDot K) hK.image_component

/-- The original lift either is its T-span, or has a literal exchanged pair
of conjugates. The exchange element belongs to T, not necessarily to K. -/
theorem ComponentLift.orbit_alternative
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2}
    [IsElementaryAbelian 2 V] {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) :
    K = conjugateSpanBy K (T : Subgroup G) ∨
      ((normalizer (K : Set G)).relIndex F.H = 2 ∧
       (normalizer (K : Set G)).relIndex (T : Subgroup G) = 2 ∧
       ∃ t ∈ (T : Subgroup G), t ∉ normalizer (K : Set G) ∧
         conjugateSpanBy K (T : Subgroup G) = K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
         K.map (MulAut.conj t).toMonoidHom ≠ K ∧
         (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K) := by
  classical
  by_cases hn : (T : Subgroup G) ≤ normalizer (K : Set G)
  · exact Or.inl (le_antisymm (le_conjugateSpanBy K _)
      (conjugateSpanBy_le le_rfl hn))
  right
  have hiH : (normalizer (K : Set G)).relIndex F.H = 2 := by
    rcases Chapter1.Section02.component_normal_or_index_two_source
      (pointNormalizer_sqtk hG F (by decide)) hK.component with hnormal | hi
    · exact (hn ((F.invariant 1).trans
        ((normal_subgroupOf_iff_le_normalizer hK.le_pointNormalizer).mp hnormal))).elim
    · change ((normalizer (K : Set G)).subgroupOf F.H).index = 2
      rwa [subgroupOf_normalizer_eq hK.le_pointNormalizer]
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  have hiT : (normalizer (K : Set G)).relIndex (T : Subgroup G) = 2 := by
    have hi := normalizer_relIndex_eq_two_of_index_two_overgroup
      (T : Subgroup G) F.H (normalizer (K : Set G)) K (F.invariant 1) hiH le_rfl
      ⟨t,ht,htn⟩
    simpa only [inf_relIndex_left] using hi
  refine ⟨hiH,hiT,t,ht,htn,?_,?_,?_⟩
  · rw [conjugateSpanBy_eq_iSup_conj]
    exact componentOrbit_eq_sup_of_index_two K (T : Subgroup G)
      (normalizer (K : Set G)) hiT inf_le_right ht htn
  · exact fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he)
  · exact conjugate_twice_eq_of_index_two K (T : Subgroup G)
      (normalizer (K : Set G)) hiT inf_le_right ht

omit [Finite G] in
/-- The dotted image of the actual T-span is the full normal component orbit.
This identifies the subgroup whose symplectic normalizer is used in the paired row. -/
theorem ComponentLift.terminalDot_span_eq_componentOrbit
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) :
    F.terminalDot (conjugateSpanBy K (T : Subgroup G)) =
      componentOrbit (F.terminalDot K) ⊤ := by
  let D := conjugateSpanBy K (T : Subgroup G)
  have hDH : D ≤ F.H := conjugateSpanBy_le hK.le_pointNormalizer
    ((F.invariant 1).trans F.H.le_normalizer)
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hsub : D.subgroupOf F.H =
      conjugateSpanBy (K.subgroupOf F.H) ((T : Subgroup G).subgroupOf F.H) := by
    apply Subgroup.map_injective F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hDH, map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hK.le_pointNormalizer,
      map_subgroupOf_eq_of_le hTH]
  have hmap : F.terminalDot D =
      conjugateSpanBy (F.terminalDot K) (F.terminalDot (T : Subgroup G)) := by
    change (D.subgroupOf F.H).map _ = _
    rw [hsub,map_conjugateSpanBy]
    rfl
  let : (F.terminalDot D).Normal := Normal.map hK.normal_span _ (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  apply le_antisymm
  · rw [hmap,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le fun t => le_iSup_of_le (⟨t,mem_top _⟩ : (⊤ : Subgroup F.TerminalHdot)) le_rfl
  · apply iSup_conjugates_le_of_le_normalizer
      (F.terminalDot K) ⊤ (F.terminalDot D)
    · exact map_mono (comap_mono (le_conjugateSpanBy K (T : Subgroup G)))
    · exact le_normalizer_of_normal

/-- The action kernel on the particular C-component is solvable. This does
not assert that it is a two-group. -/
theorem ComponentLift.terminal_kernel_solvable
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) :
    Group.IsSolvable ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap
      (K.subgroupOf F.H)).ker := by
  let f := (QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap (K.subgroupOf F.H)
  have hk : f.ker ≠ ⊤ := by
    intro ht
    have hb : F.terminalDot K = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro k hk
      have he : f ⟨k,hk⟩ = 1 := by
        change (⟨k,hk⟩ : K.subgroupOf F.H) ∈ f.ker
        rw [ht]
        exact mem_top _
      exact congrArg Subtype.val he
    exact hK.image_moved (by rw [hb,commutator_bot_left])
  exact hK.component.isSolvable_of_subnormal_lt_top
    (inferInstance : f.ker.Normal).isSubnormal hk

/-- For an actual small simple image the kernel is precisely the intrinsic
solvable radical of the lifted component. Identifying it with O₂ still needs
the source radical argument. -/
theorem ComponentLift.terminal_kernel_eq_radical
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hsmall : SmallImageRow F K) :
    ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap
      (K.subgroupOf F.H)).ker = solvableRadical (K.subgroupOf F.H) := by
  let : IsSimpleGroup (F.terminalDot K) := by
    rcases hsmall with h5 | h6
    · obtain ⟨e⟩ := h5
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := h6
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
  let := hK.image_component.2
  have hR : solvableRadical (F.terminalDot K) = ⊥ := by
    rcases (inferInstance : (solvableRadical (F.terminalDot K)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsSolvable (⊤ : Subgroup (F.terminalDot K)) := ht ▸ inferInstanceAs
        (Group.IsSolvable (solvableRadical (F.terminalDot K)))
      have hs : Group.IsSolvable (F.terminalDot K) := Group.isSolvable_of_surjective
        (f := (topEquiv : (⊤ : Subgroup (F.terminalDot K)) ≃* F.terminalDot K).toMonoidHom)
        topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable (F.terminalDot K) hs).elim
  let := hK.terminal_kernel_solvable
  have he := comap_solvableRadical_eq_of_solvable_ker
    ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap (K.subgroupOf F.H))
    ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap_surjective (K.subgroupOf F.H))
  change (solvableRadical (F.terminalDot K)).comap _ = _ at he
  rw [hR] at he
  exact he

/-- The equivalence uses the literal terminal quotient map on K. It is a
radical quotient identification, without an unproved two-core comparison. -/
@[expose] def ComponentLift.radicalQuotientEquiv
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hsmall : SmallImageRow F K) :
    (K ⧸ solvableRadical K) ≃* F.terminalDot K :=
  let e := (subgroupOfEquivOfLe hK.le_pointNormalizer).symm
  (QuotientGroup.congr (solvableRadical K)
    (solvableRadical (K.subgroupOf F.H)) e (map_solvableRadical_equiv e)).trans
    (QuotientGroup.liftEquiv _
      ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap_surjective (K.subgroupOf F.H))
      (hK.terminal_kernel_eq_radical hsmall).symm)

/-- Evaluation retains the original inclusion into H and its quotient map. -/
theorem ComponentLift.radicalQuotientEquiv_apply_mk
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hsmall : SmallImageRow F K) (k : K) :
    (hK.radicalQuotientEquiv hsmall (QuotientGroup.mk' (solvableRadical K) k) : F.TerminalHdot) =
      QuotientGroup.mk' F.terminalHatAction.ker ⟨k,hK.le_pointNormalizer k.property⟩ := rfl

/-- The small dotted component is the radical quotient of the same K. -/
theorem ComponentLift.radical_quotient_equiv
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hsmall : SmallImageRow F K) :
    Nonempty ((K ⧸ solvableRadical K) ≃* F.terminalDot K) :=
  ⟨hK.radicalQuotientEquiv hsmall⟩

/-- Apply the proved kernel identification to the exact small-row disjunction.
The quotient here is by the solvable radical, not by an assumed two-core. -/
theorem source_small_radical_rows
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hsmall : SmallImageRow F K) :
    Nonempty ((K ⧸ solvableRadical K) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((K ⧸ solvableRadical K) ≃* alternatingGroup (Fin 6)) := by
  let eK := hK.radicalQuotientEquiv hsmall
  rcases hsmall with h5 | h6
  · obtain ⟨e⟩ := h5
    exact Or.inl ⟨eK.trans e⟩
  · obtain ⟨e⟩ := h6
    exact Or.inr ⟨eK.trans e⟩

/-- Construct the full original G.10 constituent geometry for the particular
K in the supplied contract, without choosing a replacement component. -/
theorem source_component_lift_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (K : Subgroup G) (hK : ComponentLift F g K) :
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      (let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
        (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
       (P : Subgroup F.TerminalHdot) ≤ ChapterG.Section10.pointCentralizer F.terminalRepresentation v ∧
       F.terminalDot (F.X g) ≤ (P : Subgroup F.TerminalHdot) ∧
       ((F.terminalDot (F.X g)).subgroupOf (P : Subgroup F.TerminalHdot)).Normal) ∧
      ComponentOrbitSelection F.terminalRepresentation B (F.terminalDot K) (F.terminalDot (F.X g)) ∧
      ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B (F.terminalDot K) ∧
      (normalizer (F.terminalDot K : Set F.TerminalHdot)).index ≤ 2 := by
  let hrank := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨_,_,hx,B,v,hyp,_⟩ := rankTwo_terminal_hypothesis hrank F hne g hgP hgH
  let := hx
  have hn := hK.terminal_not_solvable
  refine ⟨hx,B,v,hyp,source_terminal_actor_normal_in_point_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp,?_,
    hyp.component_orthogonal_data hn (F.terminalDot K),
    terminal_component_normalizer_index_le_two hG F (by decide) _ hK.image_component⟩
  exact componentOrbit_selection F.terminalRepresentation hyp.faithful
    (hyp.irreducible_of_not_solvable hn) B hyp.alternating hyp.preserves hK.image_component
    (IsElementaryAbelian.isPGroup 2 _)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
