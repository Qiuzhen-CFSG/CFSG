module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.FFExclusion
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.Representation.SL3FourNaturalDual.NoFF.RepeatedGraph

/-!
# The actual best-offender subgroup satisfies B.5.1

For F*(D)=K quasisimple and K≅SL₃(4), the odd scalar center makes O₂(D)
trivial. A nontrivial best offender generates K by commutation, so K lies
in J(D,V). Normality of J gives O₂(J)=1; its quotient over K embeds in D/K,
and therefore F*(J)=K when D/K is a two-group. Restricting the original
faithful representation retains faithfulness and best-offender generation.
Thus every hypothesis of the genuine B.5.1 implication is discharged on J.

The final theorem applies the complete universal B.5.1 input, which is
explicit and remains the obligation of its existing source-theorem owner.
No irreducibility of the original module or equality D=J is assumed.

Source: Aschbacher–Smith, B.1.5(8), pp.69–70; B.5.1, pp.99–103;
application F.9.18(7) and 13.8.20, pp.325–326 and 955.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.SL3FourNaturalDual
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF
universe u v
variable {D : Type u} [Group D] [Finite D]

/-- The odd center of the actual component forces the ambient two-core to vanish. -/
theorem twoCore_eq_bot (K : Subgroup D) [IsQuasisimple K]
    (hK : generalizedFitting D = K) (e : K ≃* SL) : pCore 2 D = ⊥ := by
  have hcenter : Nat.card (center K) ∣ 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact Matrix.SL3.card_center_dvd_three F
  have hZ : IsPGroup 3 (center K) := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hcenter)
  have hpc : pCore 2 K = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 K) (center K)
      pCore_isPGroup hZ
    exact hd.eq_bot_of_le (IsQuasisimple.pCore_le_center 2)
  have hle : pCore 2 D ≤ K :=
    (pCore_le_fitting D 2).trans (hK ▸ fitting_le_generalizedFitting D)
  have hsub : (pCore 2 D).subgroupOf K ≤ pCore 2 K :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  rw [hpc] at hsub
  have hh := congrArg (Subgroup.map K.subtype) (le_bot_iff.mp hsub)
  simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using hh

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]

/-- Every FF witness puts the full quasisimple component in J(D,V). -/
theorem component_le_offenderSubgroup (ρ : Representation (ZMod 2) D V)
    (K : Subgroup D) [IsQuasisimple K] (hK : generalizedFitting D = K)
    (e : K ≃* SL) (hff : IsFFModule ρ) : K ≤ offenderSubgroup ρ := by
  obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
  have hAJ : A ≤ offenderSubgroup ρ := le_iSup_of_le A (le_iSup_of_le ⟨hA, le_top⟩ le_rfl)
  have hq : IsQuasisimple (generalizedFitting D) := by rw [hK]; infer_instance
  let : IsElementaryAbelian 2 A := hA.1.2
  have hc := ChapterB.QuasisimpleSections.commutator_fitting_eq
    (twoCore_eq_bot K hK e) hq hA.1.1 (IsElementaryAbelian.isPGroup 2 A)
  rw [hK] at hc
  rw [← hc]
  exact (commutator_mono le_rfl hAJ).trans (commutator_le_right _ _)

omit [Finite D] [Module.Finite (ZMod 2) V] in
/-- The actual quotient inside J inherits the ambient two-group quotient. -/
theorem offender_quotient_two (ρ : Representation (ZMod 2) D V)
    (K : Subgroup D) [K.Normal] (hquot : IsPGroup 2 (D ⧸ K)) :
    IsPGroup 2 ((offenderSubgroup ρ) ⧸ K.subgroupOf (offenderSubgroup ρ)) := by
  let f : offenderSubgroup ρ →* D ⧸ K :=
    (QuotientGroup.mk' K).comp (offenderSubgroup ρ).subtype
  have hk : f.ker = K.subgroupOf (offenderSubgroup ρ) := by
    ext x
    change QuotientGroup.mk' K (x : D) = 1 ↔ (x : D) ∈ K
    exact QuotientGroup.eq_one_iff _
  have hp : IsPGroup 2 ((offenderSubgroup ρ) ⧸ f.ker) :=
    (hquot.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  exact hp.of_equiv (QuotientGroup.quotientMulEquivOfEq hk)

/-- All source B.5.1 hypotheses hold after restricting to J(D,V). -/
theorem offender_B51_hypotheses (ρ : Representation (ZMod 2) D V)
    {κ : GroupClass.{u}} (hsqtk : IsSQTK κ D)
    (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hK : generalizedFitting D = K) (e : K ≃* SL)
    (hquot : IsPGroup 2 (D ⧸ K)) (hfaith : Function.Injective ρ) (hff : IsFFModule ρ) :
    K ≤ offenderSubgroup ρ ∧
      QuasisimpleSourceHypothesis (ρ.comp (offenderSubgroup ρ).subtype) κ
        (K.subgroupOf (offenderSubgroup ρ)) := by
  have hKJ := component_le_offenderSubgroup ρ K hK e hff
  let L := K.subgroupOf (offenderSubgroup ρ)
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKJ).symm
  have hcore := offender_restriction_twoCore ρ (twoCore_eq_bot K hK e)
  have hfit : generalizedFitting (offenderSubgroup ρ) = L :=
    generalizedFitting_eq_of_quasisimple_two_quotient L (offender_quotient_two ρ K hquot) hcore
  have hcent : center (offenderSubgroup ρ) ≤ L := by
    rw [← hfit]
    apply le_trans _ ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    exact center_le_centralizer _
  refine ⟨hKJ, {
    finite_module := inferInstance
    faithful := hfaith.comp (offenderSubgroup ρ).subtype_injective
    quasisimple := inferInstance
    sqtk := (IsSQTK.equiv (subgroupOfEquivOfLe hKJ).symm).mp (hsqtk.subgroup K)
    fitting := ?_
    twoCore := hcore
    generated := offender_restriction_generated ρ }⟩
  rw [hfit, sup_eq_left.mpr hcent]
/-- Apply the full universal classification only after establishing its source hypotheses.
The source classification is an explicit remaining input. -/
theorem offender_B51_conclusion (ρ : Representation (ZMod 2) D V)
    {κ : GroupClass.{u}} (classification : QuasisimpleClassificationInput.{u,v} κ)
    (hsqtk : IsSQTK κ D) (K : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hK : generalizedFitting D = K) (e : K ≃* SL)
    (hquot : IsPGroup 2 (D ⧸ K)) (hfaith : Function.Injective ρ) (hff : IsFFModule ρ) :
    K ≤ offenderSubgroup ρ ∧
      Nonempty (QuasisimpleSourceConclusion (ρ.comp (offenderSubgroup ρ).subtype)
        (K.subgroupOf (offenderSubgroup ρ))) := by
  obtain ⟨hKJ, hyp⟩ := offender_B51_hypotheses ρ hsqtk K hK e hquot hfaith hff
  exact ⟨hKJ, classification (offenderSubgroup ρ) V
    (ρ.comp (offenderSubgroup ρ).subtype) (K.subgroupOf (offenderSubgroup ρ)) hyp⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF
