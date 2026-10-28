module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Basic
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.GroupTheory.PCoreOvergroup

/-!
# The literal Thompson reduction and faithful action in 14.7.70

The core of I lies in O₂(L₁T), since L₁T contains the prescribed Sylow T.
Consequently a hypothetical J(T) ≤ O₂(I) lies in R₁. Literal 14.3.9(2)
then makes J(T) normal in LT; uniqueness of the maximal two-local over LT
puts its normalizer inside M = N_G(L). The already proved I-normalization
of J(T) contradicts the independent source escape Y ≰ M. No commutator
identity is attributed to 14.3.9(2).

On the original elementary conjugate span V_I, the exact kernel identity
O₂(I) = C_I(V_I) gives a faithful action of the actual plus quotient.
The nested subgroup carrier has its explicit equivalence with ambient V_I,
and the action formula retains ambient conjugation and the original plus
map. Thompson escape supplies a genuine FF-offender. Restricting to the
actual offender subgroup gives the full B.5.3 hypotheses; its SQTK cover
is the full preimage in I. We apply the complete adequate B.5.6 contract,
including its corrected outer A₆–C₃ alternative. The symmetric-three case
already yields an actual normal S₃ in the plus quotient.

The universal 14.3.9(2) input belongs to qt-14-03-prelim; the universal
setup inputs to qt-12-02 and qt-1-02-adequate-assembly; the adequate B.5.6
input to qt-b05-general-classification/qt-b-05. Their discharge stays with
the earlier-source assembly owners. This is a conditional stage: the
projection–residual escape and the remaining component selection and
faithful-family arguments must still be supplied by ThompsonWitness's
assembly. No complete proof of 14.7.70 is asserted here.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.3.9(2), printed p.992; 14.7.70, pp.1074–1075 (PDF pp.1091–1092);
B.2.4 and B.5.3–6, pp.75–76 and 104–105.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness
open Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- Literal 14.3.9(2), universally over the original case (1) configurations.
The conclusion is relative normality in LT. Producer: qt-14-03-prelim. -/
def EarlierThompsonNormality : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (A U : Subgroup X),
    Counterexample S A → HigherRankHypothesis KnownSimple.IsKnownSimple S A U 3 →
    ∀ f : InvariantFlag S U 3,
      elementaryAbelianMaxJ (S : Subgroup X) ≤ f.Ri A 1 →
      ((elementaryAbelianMaxJ (S : Subgroup X)).subgroupOf
        (A ⊔ (S : Subgroup X))).Normal

omit [Finite G] in
/-- The two-core of I lies in the two-core of its Sylow overgroup L₁T. -/
theorem core_le_R₁ : (I c).pCoreIn 2 ≤ F.Ri L 1 := by
  have hh := pCore_le_map_of_sylow_le (sylow c) (left c)
    (show (sylow c : Subgroup (I c)) ≤ left c from fun _ hx => mem_sup_right hx)
  have hm := map_mono (f := (I c).subtype) hh
  let e : left c ≃* group F L := subgroupOfEquivOfLe le_sup_left
  have he : (I c).subtype.comp (left c).subtype = (group F L).subtype.comp e.toMonoidHom := rfl
  rw [map_map, he, ← map_map, pCore_map_iso] at hm
  exact hm

include d in
/-- The actual Thompson subgroup is nonzero, since the original seed point
is a nonidentity element of the original Sylow. -/
theorem thompson_ne_bot : elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ := by
  have hzT : d.z ∈ (T : Subgroup G) :=
    d.natural.chosen.le_sylow ((F.le_seed 1) (d.point ▸ mem_zpowers d.z))
  let : Nontrivial (T : Subgroup G) :=
    ⟨⟨⟨d.z, hzT⟩, 1, fun he => d.z_ne_one (congrArg Subtype.val he)⟩⟩
  have hn := elementaryAbelianMaxJ_top_ne_bot_of_isPGroup T.isPGroup'
  have hm := elementaryAbelianMaxJ_map_injective (T : Subgroup G).subtype
    (T : Subgroup G).subtype_injective ⊤
  rw [← MonoidHom.range_eq_map, range_subtype] at hm
  rw [hm]
  exact fun he => hn ((map_eq_bot_iff_of_injective _ (T : Subgroup G).subtype_injective).mp he)

include d in
/-- Literal 14.3.9(2) and uniqueness over LT suffice for the Thompson step.
The independent projection argument must still supply the displayed escape. -/
theorem thompson_not_le_core_of_escape
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (thompson : EarlierThompsonNormality.{u})
    (escape : ¬ Y c ≤ normalizer (L : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2 := by
  intro hJ
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hn := thompson G T L V d.counterexample d.natural F
    (hJ.trans (core_le_R₁ c))
  have hLT : L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hn
  have hu := (d.natural.maximal_unique earlier.structural earlier.uniqueness).2
  have hNM := normalizer_le_of_unique_maximalTwoLocal
    (J := L ⊔ (T : Subgroup G))
    (fun N hN hLN => Set.mem_singleton_iff.mp (hu ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN, hLN⟩))
    (T.isPGroup'.to_le hJT) (thompson_ne_bot d) hLT
  exact escape ((Y_le_I c).trans ((I_normalizes_thompson_of_le_core c hJ).trans hNM))

section Action
variable (h : Geometry d c) (k : CoreFacts c)

/-- The module is the literal V_I, viewed as a subgroup of its actor I. -/
def moduleEquiv : (VI c).subgroupOf (I c) ≃* VI c :=
  subgroupOfEquivOfLe (VI_le_I d c)

include d k in
theorem module_elementary : IsElementaryAbelian 2 ((VI c).subgroupOf (I c)) := by
  let := k.elementary
  exact IsElementaryAbelian.subgroupOf (VI_le_I d c)

include h k in
/-- The original plus map has precisely the centralizer of this module as kernel. -/
theorem plus_kernel : (plusMap c).ker =
    centralizer ((VI c).subgroupOf (I c) : Set (I c)) := by
  rw [plusMap, QuotientGroup.ker_mk']
  exact h.core_eq_centralizer k.centralizes

/-- Actual conjugation on V_I descends through the actual plus map. -/
def action : letI := module_elementary d c k
    Representation (ZMod 2) ((I c) ⧸ pCore 2 (I c))
      (Additive ((VI c).subgroupOf (I c))) := by
  let := module_elementary d c k
  let := VI_normal d c
  exact NormalElementaryQuotient.representation _ (plusMap c)
    (QuotientGroup.mk'_surjective _) (plus_kernel d c h k)

/-- The formula keeps the original ambient elements and original quotient map. -/
theorem action_apply (i : I c) (v : Additive ((VI c).subgroupOf (I c))) :
    (((action d c h k (plusMap c i) v).toMul : I c) : G) =
      (i : G) * ((v.toMul : I c) : G) * (i : G)⁻¹ := by
  let := module_elementary d c k
  let := VI_normal d c
  exact congrArg (fun x : I c => (x : G))
    (NormalElementaryQuotient.representation_apply _ (plusMap c)
      (QuotientGroup.mk'_surjective _) (plus_kernel d c h k) i v)

theorem action_faithful : Function.Injective (action d c h k) := by
  let := module_elementary d c k
  let := VI_normal d c
  exact NormalElementaryQuotient.representation_injective _ (plusMap c)
    (QuotientGroup.mk'_surjective _) (plus_kernel d c h k)

include d k in
/-- Normal elementary V_I lies in the prescribed restriction of T. -/
theorem module_le_sylow : (VI c).subgroupOf (I c) ≤ (sylow c : Subgroup (I c)) := by
  let := module_elementary d c k
  let := VI_normal d c
  exact (IsElementaryAbelian.isPGroup 2 ((VI c).subgroupOf (I c))).le_sylow_of_normal (sylow c)

/-- A nonzero original Thompson image gives a genuine FF-offender in this action. -/
theorem action_ff_of_thompson_escape
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2) :
    let := module_elementary d c k
    IsFFModule (action d c h k) := by
  let := module_elementary d c k
  let := VI_normal d c
  apply NormalElementaryQuotient.isFFModule_of_thompson_not_le _ (plusMap c)
    (QuotientGroup.mk'_surjective _) (plus_kernel d c h k)
    (sylow c : Subgroup (I c)) (module_le_sylow d c k)
  intro hj
  apply hJ
  rw [plusMap, QuotientGroup.ker_mk'] at hj
  have hm := map_mono (f := (I c).subtype) hj
  rw [← elementaryAbelianMaxJ_map_injective (I c).subtype (I c).subtype_injective, sylow_coe,
    map_subgroupOf_eq_of_le (T_le_I c)] at hm
  exact hm

/-- The full preimage in I is a genuine SQTK cover of the offender actor. -/
def offenderCover : letI := module_elementary d c k
    ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (offenderSubgroup (action d c h k)) := by
  let := module_elementary d c k
  exact {
    Cover := (offenderSubgroup (action d c h k)).comap (plusMap c)
    kernel := ((plusMap c).subgroupComap (offenderSubgroup (action d c h k))).ker
    sqtk := (core_consequences d c h k).1.subgroup _
    equiv := QuotientGroup.quotientKerEquivOfSurjective _
      ((plusMap c).subgroupComap_surjective_of_surjective _ (QuotientGroup.mk'_surjective _)) }

/-- All B.5.3 hypotheses on the literal offender subgroup, with the full
known-simple catalogue and the actual SQTK preimage cover. -/
theorem offender_hypothesis : letI := module_elementary d c k
    ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple
      ((action d c h k).comp (offenderSubgroup (action d c h k)).subtype) := by
  let := module_elementary d c k
  let ρ := action d c h k
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  have hjcore : pCore 2 J = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ J.subtype_injective).mp
    apply bot_unique
    rw [← pCore_quotient_pCore_eq_bot (p := 2) (G := I c)]
    exact le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  exact ⟨Module.Finite.of_finite, (action_faithful d c h k).comp J.subtype_injective,
    hjcore, offenderSubgroup_restrict_eq_top ρ, ⟨offenderCover d c h k⟩⟩

/-- Apply the complete corrected B.5.6 contract. The universal producer is
qt-b05-general-classification/qt-b-05; no legacy splitting contract is used. -/
theorem adequate_alternative
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple) :
    let := module_elementary d c k
    ChapterB.SourceInduction.AdequateAlternative
      ((action d c h k).comp (offenderSubgroup (action d c h k)).subtype) := by
  let := module_elementary d c k
  exact b5 _ _ _ (offender_hypothesis d c h k)

/-- The Thompson escape removes precisely the trivial-actor alternative. -/
theorem nontrivial_adequate_alternative
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2) :
    let := module_elementary d c k
    ChapterB.SourceInduction.NontrivialAdequateAlternative
      ((action d c h k).comp (offenderSubgroup (action d c h k)).subtype) := by
  let := module_elementary d c k
  have hn := offenderSubgroup_ne_bot_of_ff (action d c h k)
    (action_ff_of_thompson_escape d c h k hJ)
  let : Nontrivial (offenderSubgroup (action d c h k)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hn
  exact (adequate_alternative d c h k b5).of_nontrivial _

/-- In the symmetric-three alternative the actual offender subgroup is
already a normal S₃ in the actual plus quotient. -/
theorem smallSubnormal_of_symmetricThree
    (s : letI := module_elementary d c k
      ChapterB.SourceInduction.SymmetricThreeCase
        ((action d c h k).comp (offenderSubgroup (action d c h k)).subtype)) :
    SmallSubnormal c := by
  let := module_elementary d c k
  exact ⟨offenderSubgroup (action d c h k),
    (offenderSubgroup_normal (action d c h k)).isSubnormal, Or.inl ⟨s.equiv⟩⟩

end Action
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness
