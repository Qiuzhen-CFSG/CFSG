module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup

/-!
# Center geometry for the actual nonextraspecial L₃(2) branch

The original selected counterexample supplies the Chapter12 commutator form,
full binary action, squares and plane generation. Applying the parabolic
calculations identifies Z(I₂) with Z(U) ∩ Z(U)^g and computes Z(U) ∩ U^g.
These are consequences for the original flag and right conjugator; no local
recognition or extra module premise is assumed.

If the subsequent 14.3.31 argument makes Z(I₂) trivial, a nonextraspecial
center cannot have its conjugate contained in U: such containment would
force its order to be at most two and hence force Z(U)=V₁. This is a consumer
of the centerlessness result, whose proof remains a separate source task.
The point centralizer is also proved to have generalized Fitting subgroup
equal to its two-core, as needed in the final I.4.8 application.

Source: Aschbacher--Smith, 12.8.10(1--2), printed pp.853--854;
14.3.28--32, printed pp.1002--1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
theorem source_point_centralizer (F : InvariantFlag T V 3) :
    ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
      F.H = centralizer ({z} : Set G) := by
  obtain ⟨z, _, hz⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hc : Nat.card (zpowers z) = 2 := by
    rw [← hz]
    simpa using F.card 1 (by decide)
  exact ⟨z, (Nat.card_zpowers z).symm.trans hc, hz,
    F.H_eq_centralizer (by decide) z hz⟩

/-- Even characteristic identifies the actual intrinsic core of H. -/
theorem source_fitting (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) : generalizedFitting F.H = pCore 2 F.H := by
  let h := higherRankHypothesis d earlier hq chosen
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (F.localKernel_characteristicTwo d.qtke L (normalizer (L : Set G)) F.H
      (h.point_mem_Hz F alternatives))

/-- The full normalizer of the original nonzero seed has characteristic two,
since it contains the original Sylow subgroup. No uniqueness input is needed. -/
theorem source_normalizer_fitting (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3) :
    generalizedFitting (normalizer (V : Set G)) = pCore 2 (normalizer (V : Set G)) := by
  let := chosen.elementary
  have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hv : V ≠ ⊥ := by intro he; simp [he] at hc
  have hlocal : IsTwoLocal (normalizer (V : Set G)) :=
    ⟨V, hv, IsElementaryAbelian.isPGroup 2 V, rfl⟩
  obtain ⟨M, hVM, hM⟩ := Finite.exists_le_maximal hlocal
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := F.last ▸ F.invariant 3
  exact generalizedFitting_eq_pCore_of_sylow_overgroup T (normalizer (V : Set G)) M
    hTV hVM (d.qtke.evenCharacteristic T M hM (hTV.trans hVM))

/-- Both center identities, with every earlier local algebra input discharged. -/
theorem source_center_intersections (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.ZU ⊓ conjugate F.ZU g = Chapter12.Section08.centerIn (F.I₂ L) ∧
      F.ZU ⊓ conjugate F.U g = Chapter12.Section08.centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
      conjugate F.ZU g ⊓ F.U = Chapter12.Section08.centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, hphi, hc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F alternatives)
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let B := F.localKernel_markedForm (by decide) htwo hphi hcomm
  obtain ⟨e, _, hgen, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural)
    hcomm hsquare hspan hne g hgP hgH
  have hi := F.parabolic_center_eq L g hgP hgen e (by decide) hc
    (F.binary_source_fixedSpace_pullback (by decide) L chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT structural)
      hcomm hsquare hspan hne g hgP hgH)
  refine ⟨hi, ?_, ?_⟩
  · rw [F.center_intersection (by decide) L chosen.normalizes hc hcomm
      (F.plane_centralizer_center B) g hgP hgH, hi]
  · rw [F.conjugate_center_intersection (by decide) L chosen.normalizes hc hcomm
      (F.plane_centralizer_center B) g hgP hgH, inf_comm (conjugate F.ZU g), hi]

/-- The original nonextraspecial center escapes U after 14.3.31.
The remaining centerlessness premise is precisely the source input used. -/
theorem source_center_escape_of_centerless (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ¬ conjugate F.ZU g ≤ F.U := by
  let := chosen.elementary
  have hi := (source_center_intersections d earlier hq chosen structural alternatives
    F hne g hgP hgH).2.2
  rw [hI, bot_sup_eq] at hi
  intro hle
  rw [inf_eq_left.mpr hle] at hi
  exact hZ (Subgroup.map_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective hi)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
