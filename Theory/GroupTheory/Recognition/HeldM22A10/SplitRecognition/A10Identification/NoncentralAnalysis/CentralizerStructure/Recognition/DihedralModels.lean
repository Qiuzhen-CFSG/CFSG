module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.DihedralModels.NormalCore
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.DihedralModels.FieldCard
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import GorensteinWalter.PSL2PerfectOfCard
public import GorensteinWalter.LinearRingEquiv

/-!
# Identifying Held's dihedral quotient core

The quotient core M has a dihedral Sylow subgroup of order eight equal to the
centralizer of its involution p, trivial odd core, and no normal subgroup of
index two. The abstract recognition argument identifies M with PSL2 over an
odd field; its involution centralizer restricts the field order to seven or
nine. The exceptional comparison PSL2(9) = A6 uses the actual compatible
permutation actions from the attributed ATLAS port. Field transport identifies
the other case with PSL2(ZMod 7). Both models are perfect.

These are the alternatives before splitting the inverse image and excluding
the PSL2(7) case in Held, "A Characterization of some multiply transitive
permutation groups, I", Illinois J. Math. 13 (1969), Lemma 4.2, printed p.234,
DOI 10.1215/ijm/1256053756. No recognition or splitting conclusion is assumed.
-/

open Subgroup GorensteinWalter
noncomputable section
namespace Theory.GroupTheory.DihedralEightRecognition
universe u

/-- Recognition from the intrinsic dihedral-centralizer hypotheses. -/
public theorem perfect_and_models {H : Type u} [Group H] [Finite H]
    (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S)
    (hno : ∀ N : Subgroup H, N.Normal → N.index ≠ 2)
    (hO : pPrimeCore 2 H = ⊥) :
    Group.IsPerfect H ∧
      (Nonempty (H ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))) := by
  obtain ⟨F, iF, finF, hF, ⟨eF⟩⟩ := exists_psl2_model S eS t ht hC hno hO
  let : Field F := iF
  let : Finite F := finF
  have hCcard : Nat.card (centralizer ({t} : Set H)) = 8 := by
    rw [hC]
    exact (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  have hcard := field_card_of_model hF eF t ht hCcard
  have hlarge : 3 < Nat.card F := by omega
  let : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F hlarge
  refine ⟨Group.IsPerfect.ofSurjective (f := eF.symm.toMonoidHom) eF.symm.surjective, ?_⟩
  rcases hcard with hseven | hnine
  · right
    let : Fintype F := Fintype.ofFinite F
    let eK : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
      (by simpa only [Nat.card_eq_fintype_card] using hseven)
    exact ⟨eF.trans (psl2RingEquiv eK).symm⟩
  · left
    exact ⟨eF.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hnine)⟩

end Theory.GroupTheory.DihedralEightRecognition

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The exact alternatives for the quotient core on Held's printed p.234. -/
public theorem QuotientCore.perfect_and_models
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) (c : QuotientCore D e) :
    Group.IsPerfect c.subgroup ∧
      (Nonempty (c.subgroup ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (c.subgroup ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))) := by
  apply DihedralEightRecognition.perfect_and_models c.sylow c.sylowEquiv
    (⟨p D e, c.p_mem⟩ : c.subgroup) _ c.centralizer_eq c.no_index_two c.oddCore
  exact (Subgroup.orderOf_mk _ _).trans (p_order D e hfusion)

/-- Perfectness needed to make the derived inverse image surject onto the core. -/
public theorem QuotientCore.isPerfect
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) (c : QuotientCore D e) :
    Group.IsPerfect c.subgroup :=
  (c.perfect_and_models D e hfusion).1

/-- Actual A6 or PSL2(7) equivalences, before the separate PSL2(7) exclusion. -/
public theorem QuotientCore.model_alternative
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) (c : QuotientCore D e) :
    Nonempty (c.subgroup ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (c.subgroup ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :=
  (c.perfect_and_models D e hfusion).2

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
