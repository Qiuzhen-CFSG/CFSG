module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.MovingOffenders
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Invariance

/-!
# One offender preserving every central constituent

For C_Q(K)=1, the existing moving quadratic offender is disjoint from the
centralizer of the whole central-omega covering component. Passing to an
equal-weight minimal best offender preserves this disjointness, its movement
of the component, and its injection into the literal initial action.
B.7.2 then makes this one offender preserve every Irr⁺ section. Each section
has an FF action under its actual component/offender overgroup; invariance
under the entire original actor is no longer an assumption.

ConstituentRecognition applies this construction to recognize the faithful
section images. The complete covering kernel is retained: neither offender
containment in the component nor whole-section semisimplicity is asserted.
Source: Aschbacher--Smith B.1.5(3), B.7.2(1), and C.1.34,
printed pp.69,119,136--137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentOffenders
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E :=
  CentralSections.coreOmegaLayer_elementary
local notation "H" => (J ⧸ centralizer (E : Set J))
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* H)
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* H)
local notation "rho" => CentralSections.coreOmegaRepresentation h hn
local notation "f" => NoncoreOffenders.toInitial h hn E
  (CentralSections.coreOmegaLayer_centralizer_le h hn)

include h hn

/-- One minimal offender in the specified original overgroup preserves every
Irr⁺ section of the whole covering component. -/
theorem exists_minimal_section_offender
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (S : Subgroup J) (hRS : R.subgroupOf J ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ D ≤ A.map q,
      IsMinimalBestOffender rho D ∧ IsQuadratic rho D ∧
      weight rho D = weight rho (A.map q) ∧ ⁅B,D⁆ = B ∧
      D ⊓ centralizer (B : Set H) = ⊥ ∧
      Function.Injective ((f).comp D.subtype) ∧
      ∀ I, IsIrrPlus rho B I → D ≤ subspaceStabilizer rho I := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  have hc : IsComponent H B := ⟨(inferInstance : (B).Normal).isSubnormal,inferInstance⟩
  obtain ⟨A,hA,X,hXA,hX,_,hw,_,hdis,hfi⟩ :=
    MovingOffenders.exists_quadratic_moving_offender h hn hfixed S hRS
  obtain ⟨D,hD,hDX⟩ := hX.exists_minimal rho
  have hd : D ⊓ centralizer (B : Set H) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hDX.1).trans_eq hdis)
  have hm : ⁅B,D⁆ = B := by
    rcases hc.commutator_dichotomy D with hz | he
    · have hDC : D ≤ centralizer (B : Set H) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
      exact (hD.1.1.1 (by simpa only [inf_of_le_left hDC] using hd)).elim
    · exact le_antisymm (commutator_le_left _ _)
        ((le_iSup_conjugates B D).trans_eq he.symm)
  refine ⟨A,hA,D,hDX.1.trans hXA,hD,hD.isQuadratic rho,hDX.2.trans hw,
    hm,hd,?_,?_⟩
  · exact hfi.comp (inclusion_injective hDX.1)
  · intro I hI
    exact ChapterB.SourceInduction.ComponentReduction.minimalOffender_stabilizes_irrPlus
      rho (CentralSections.coreOmegaRepresentation_injective h hn) hD hc hm hI

/-- Every Irr⁺ section has a genuine local FF action. Its invariance under
the same minimal offender is proved, rather than required of the whole actor. -/
theorem irrPlus_local_isFF
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (S : Subgroup J) (hRS : R.subgroupOf J ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ D ≤ A.map q,
      IsMinimalBestOffender rho D ∧
      ∀ (I : Submodule (ZMod 2) (Additive E)) (_hI : IsIrrPlus rho B I),
        ∃ hDI : B ⊔ D ≤ subspaceStabilizer rho I,
        ∃ hDN : B ⊔ D ≤ normalizer (B : Set H),
          IsFFModule (imageRepresentation
            (centralSectionRepresentation rho B (B ⊔ D) I hDI hDN)) := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  obtain ⟨A,hA,D,hDA,hD,_,_,_,hd,_,hs⟩ :=
    exists_minimal_section_offender h hn hfixed S hRS
  refine ⟨A,hA,D,hDA,hD,?_⟩
  intro I hI
  have hi := sup_le hI.choose (hs I hI)
  have hnB : B ⊔ D ≤ normalizer (B : Set H) := by rw [normalizer_eq_top]; exact le_top
  exact ⟨hi,hnB,centralSection_isFFModule_of_offender rho B D (B ⊔ D) hD.1
    le_sup_left le_sup_right (disjoint_iff.mpr hd) I hI hi hnB⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentOffenders
