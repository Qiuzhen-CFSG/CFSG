module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaChief
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.IntrinsicOvergroupCore
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalOvergroupFF

/-!
# The original Omega and overgroup conclusions from marked symplectic recognition

The genuine QRC numerical alternatives on Ω₁Z(O₂(L₀T)) leave only the
literal E.2.7 marked pair. Its recognition gives the upper bound, the chief
argument gives commutator containment, and the proved H¹ splitting and
center-freeness give V=Ω₁Z(O₂(L₀T)). The original interval, tensor-line,
overgroup-core and FF consumers are then applied with that premise removed.

The sole additional earlier-source input here is geometric E.2.7 recognition
on the displayed H/core quotient; no Omega equality or numerical callback is
assumed. Source: Aschbacher--Smith 9.2.2 and 9.3.6--7.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
  {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
  (hrec : (m.omegaCenter_core_qrcHypotheses hH).HasSymplecticMiddleOutsideCoreModel →
    ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
      let S := T.subtype hH.1.1.2
      let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
      ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
        (S.mapSurjective (QuotientGroup.mk'_surjective _))
        ((ChapterB.minimalParabolicMax S hp).map q)
        (((omegaCenterIn ((localJoin T L).pCoreIn 2)).subgroupOf H).map q))
include m hH hrec

theorem omegaCenter_core_commutator_le_of_symplectic_recognition :
    ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),localOrbit T L⁆ ≤ D.fullModule :=
  m.omegaCenter_core_commutator_le_of_cubicRatio_le_two
    (m.omegaCenter_core_cubicRatio_le_two_of_symplectic_recognition hH hrec)

theorem fullModule_eq_omegaCenter_core_of_symplectic_recognition
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    D.fullModule = omegaCenterIn ((localJoin T L).pCoreIn 2) :=
  m.fullModule_eq_omegaCenter_core_of_outside_of_commutator_le hout
    (m.omegaCenter_core_commutator_le_of_symplectic_recognition hH hrec)

theorem omegaCenter_eq_fullModule_inf_of_symplectic_recognition
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (S : Subgroup G) (hQS : (localJoin T L).pCoreIn 2 ≤ S)
    (hST : S ≤ (T : Subgroup G)) :
    omegaCenterIn S = D.fullModule ⊓ centralizer (S : Set G) :=
  m.omegaCenter_eq_fullModule_inf_of_outside_of_commutator_le hout
    (m.omegaCenter_core_commutator_le_of_symplectic_recognition hH hrec) S hQS hST

theorem omegaCenter_stabilizer_le_tensorLine_of_symplectic_recognition
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    omegaCenterIn ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤ m.tensorLine :=
  m.omegaCenter_stabilizer_le_tensorLine m.sylow_not_normalizes_component hout
    (m.omegaCenter_core_commutator_le_of_symplectic_recognition hH hrec)

theorem outside_core_and_center_of_symplectic_recognition
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hLH : L ≤ M₀) (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ M₀)
    (hout : ¬ M₀ ≤ D.maximalLocal) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ :=
  m.outside_core_and_center_of_original_tensor m.sylow_not_normalizes_component houtside
    (m.omegaCenter_core_commutator_le_of_symplectic_recognition hH hrec)
    M₀ hcore hLH hRH hout
theorem old_residual_overgroup_core_and_ff_of_symplectic_recognition
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (M₀ A : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hAH : A ≤ M₀) (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (m.tensorLine : Set G))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N)) :=
  m.old_residual_overgroup_core_and_ff m.sylow_not_normalizes_component houtside
    (m.omegaCenter_core_commutator_le_of_symplectic_recognition hH hrec)
    hH eK hSyl M₀ A hcore hgen hAH hAU d hdA hd3 hdC hKU hmove
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
