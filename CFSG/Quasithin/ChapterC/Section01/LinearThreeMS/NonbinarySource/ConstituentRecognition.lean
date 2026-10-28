module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ConstituentOffenders
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import Theory.Representation.BinaryOffender.CentralSectionSplitting
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ChiefImages

/-!
# Natural constituents of the whole central omega

One minimal moving offender preserves every Irr⁺ subspace of the whole
covering component. On each literal central section, its faithful action
image is FF, is irreducible on the component image, and has that image as
its generalized Fitting subgroup. The original full SL₃ covering supplies
the projective marking. K.3.2 then gives natural coordinates over the
original coefficient field, including field four.

When C_Q(K)=1 the central quotient has no fixed kernel, so each actual
Irr⁺ subspace has order |F|³ and binary dimension 3n. Such a subspace exists.
The original nonblock application is in NonblockConstituentRecognition.

The group covering kernel remains in the original actor. Recognition here
is on the faithful constituent images; it does not identify the entire
center or Frattini sections, align the constituent markings, or eliminate
the exceptional covering kernel required for full C.1.34.
Source: Aschbacher--Smith B.1.5, B.7.2, K.3.2 and C.1.34,
printed pp.69--70,119,454--456,136--137.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped MatrixGroups

/-- Natural coordinates on the faithful component image of the literal
central section under its component/offender overgroup. -/
@[expose] def HasNaturalCentralSection
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (B D : Subgroup X)
    (I : Submodule (ZMod 2) W) (F : BinaryField) : Prop :=
  ∃ hs : B ⊔ D ≤ subspaceStabilizer ρ I,
    ∃ hn : B ⊔ D ≤ normalizer (B : Set X),
      IsLinearNatural
        ((KernelQuotient.action (centralSectionRepresentation ρ B (B ⊔ D) I hs hn)).comp
          (ChapterB.QuasisimpleSource.SourceCompletion.ChiefImage.component
            (centralSectionRepresentation ρ B (B ⊔ D) I hs hn)
            (B.subgroupOf (B ⊔ D))).subtype) F 3

/-- A local FF action recognizes the literal central quotient of any Irr⁺
section as a natural SL₃ module over the prescribed field. The original
covering component is not identified with its faithful image. -/
theorem centralSection_natural
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (B D : Subgroup X) [B.Normal] [IsQuasisimple B]
    (hD : IsElementaryTwo D) (I : Submodule (ZMod 2) W) (hI : IsIrrPlus ρ B I)
    (hs : B ⊔ D ≤ subspaceStabilizer ρ I) (hnorm : B ⊔ D ≤ normalizer (B : Set X))
    (hff : IsFFModule (imageRepresentation (centralSectionRepresentation ρ B (B ⊔ D) I hs hnorm)))
    (hsq : IsSQTK KnownSimple.IsKnownSimple B) (F : BinaryField)
    (mark : B ⧸ center B ≃* PSL(3,F.Carrier)) :
    IsLinearNatural
      ((KernelQuotient.action (centralSectionRepresentation ρ B (B ⊔ D) I hs hnorm)).comp
        (ChapterB.QuasisimpleSource.SourceCompletion.ChiefImage.component
          (centralSectionRepresentation ρ B (B ⊔ D) I hs hnorm) ((B).subgroupOf (B ⊔ D))).subtype) F 3 := by
  let U := B ⊔ D
  let C := B.subgroupOf U
  let e : C ≃* B := subgroupOfEquivOfLe (show B ≤ U from le_sup_left)
  let : C.Normal := inferInstance
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
  let τ := centralSectionRepresentation ρ B U I hs hnorm
  let π := KernelQuotient.projection τ
  let C' := ChapterB.QuasisimpleSource.SourceCompletion.ChiefImage.component τ C
  let δ := KernelQuotient.action τ
  have hi : IsIrreducible (τ.comp C.subtype) :=
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective
      (centralQuotientRepresentation ρ B I hI.choose)).mpr hI.choose_spec.2
  have hτ : IsIrreducible τ := irreducible_of_subgroup_restriction τ C hi
  have hnon : ¬ C ≤ τ.ker := by
    intro hk
    apply hI.not_le_fixedSpace ρ
    apply le_fixedSpace_of_commutator_le_fixedSpace ρ B I hI.choose
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,v,hv,rfl⟩
    exact (centralSectionRepresentation_ker_iff ρ B U I hs hnorm
      ⟨b,mem_sup_left hb⟩).mp (hk hb) v hv
  have hm : subspaceCommutator τ ⊤ C ≠ ⊥ := by
    intro hz
    apply hnon
    intro c hc
    apply LinearMap.ext
    intro v
    exact (subspaceCommutator_eq_bot_iff τ ⊤ C).mp hz (Submodule.mem_top) ⟨c,hc⟩
  let := SourceCompletion.ChiefImage.component_normal τ C
  let := SourceCompletion.ChiefImage.component_quasisimple τ C hm
  have hquot : IsPGroup 2 (U ⧸ C) :=
    IrreducibleBranch.local_quotient_isTwoGroup B D (hD.2.isPGroup 2 D)
  have hfit : generalizedFitting (KernelQuotient.Actor τ) = C' :=
    SourceCompletion.ChiefImage.fitting_eq_component τ C hτ hm hquot
  have hsqC : IsSQTK KnownSimple.IsKnownSimple C := (IsSQTK.equiv e).mpr hsq
  have hsq' : IsSQTK KnownSimple.IsKnownSimple C' :=
    SourceCompletion.ChiefImage.component_sqtk τ
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) C hsqC hm
  have hq' := SourceCompletion.ChiefImage.component_quotient_isTwoGroup τ C hquot
  have hsqX : IsSQTK KnownSimple.IsKnownSimple (KernelQuotient.Actor τ) := by
    have hsqU := IrreducibleBranch.local_sqtk
      ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups
      B D hsq (hD.2.isPGroup 2 D)
    refine ⟨?_,hsqU.isKGroup.quotient _⟩
    · intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_le_of_normal_two_quotient C' hq' p ho).trans
        (hsq'.stronglyQuasithin p hp ho)
  have hirr : IsIrreducible (δ.comp C'.subtype) :=
    (irreducible_comp_surjective_iff (π.subgroupMap C) (π.subgroupMap_surjective C)
      (δ.comp C'.subtype)).mp hi
  have hff' : IsFFModule δ := by
    obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender _).mp hff
    exact ⟨_,(KernelQuotient.bestOffender_transport τ hA).isOffender _⟩
  let hsource : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple δ C' :=
    ⟨inferInstance,inferInstance,hsqX,hfit,inferInstance,KernelQuotient.faithful τ,hirr,
      (cubicRatio_le_quadraticRatio δ).trans
        (((isFFModule_iff_quadraticRatio_le_one δ).mp hff').trans (by norm_num))⟩
  let : Nontrivial (C.map π) := (nontrivial_iff_ne_bot _).mpr
    (SourceCompletion.ChiefImage.component_ne_bot τ C hm)
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  let ep : C' ⧸ center C' ≃* PSL(3,F.Carrier) :=
    (IsQuasisimple.centralQuotientEquiv (π.subgroupMap C)
      (π.subgroupMap_surjective C)).symm.trans
      ((IsQuasisimple.centralQuotientEquiv e.toMonoidHom e.surjective).trans mark)
  obtain ⟨d⟩ := ChapterK.Linear.Recognition.SourceFF.naturalSourceInput_of_quotient_ff hsource ep hff'
  exact ⟨d.natural⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition
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

open ChapterB.QuasisimpleSource

/-- The coefficient field retains the supplied carrier, characteristic and degree. -/
@[expose] def coefficientField : BinaryField := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  exact { Carrier := F, degree := n, degree_pos := by omega, card_eq := h.field_card }

private theorem omega_component_sqtk
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) : IsSQTK KnownSimple.IsKnownSimple B := by
  let := (KernelOffenders.omegaCover h hn e).isQuasisimple
  exact
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) (h.sqtk.subgroup L)
      (ChapterA.Section02.IsSectionOf.of_surjective ((q).comp (L).subtype).rangeRestrict
        ((q).comp (L).subtype).rangeRestrict_surjective)

/-- Every actual Irr⁺ section of the whole central omega has a natural
faithful component image, over the original coefficient field. One minimal
offender in the specified source overgroup preserves all these sections. -/
theorem irrPlus_local_natural
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (S : Subgroup J) (hRS : R.subgroupOf J ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ D ≤ A.map q,
      IsMinimalBestOffender rho D ∧
      ∀ (I : Submodule (ZMod 2) (Additive E)) (_hI : IsIrrPlus rho B I),
        HasNaturalCentralSection rho B D I (coefficientField h hn) := by
  obtain ⟨A,hA,D,hDA,hD,hsections⟩ :=
    ConstituentOffenders.irrPlus_local_isFF h hn hfixed S hRS
  refine ⟨A,hA,D,hDA,hD,?_⟩
  intro I hI
  obtain ⟨hs,hnB,hff⟩ := hsections I hI
  let : (L).Normal := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple B := (KernelOffenders.omegaCover h hn e).isQuasisimple
  exact ⟨hs,hnB,centralSection_natural rho B D hD.1.1 I hI hs hnB hff (omega_component_sqtk h hn e)
    (coefficientField h hn) (KernelOffenders.omegaCover h hn e).quotientCenterEquiv⟩

/-- The whole covering component has a noncentral irreducible central section;
recognition of its Irr⁺ members is therefore nonvacuous. -/
theorem exists_irrPlus :
    ∃ I : Submodule (ZMod 2) (Additive E), IsIrrPlus rho B I := by
  let : IsQuasisimple B :=
    (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  apply exists_isIrrPlus_of_not_fixed rho B
  intro hz
  obtain ⟨b,hb⟩ := exists_ne (1 : B)
  apply hb
  apply Subtype.ext
  apply CentralSections.coreOmegaRepresentation_injective h hn
  apply LinearMap.ext
  intro v
  change rho (b : H) v = rho (1 : H) v
  rw [map_one]
  exact hz (Submodule.mem_top : v ∈ ⊤) b

/-- Every actual Irr⁺ subspace, rather than only its quotient by fixed vectors,
has natural order and binary dimension when C_Q(K)=1. -/
theorem irrPlus_card_finrank
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I) :
    Nat.card I = Nat.card F ^ 3 ∧ Module.finrank (ZMod 2) I = 3*n := by
  obtain ⟨A,_,D,_,_,hs⟩ := irrPlus_local_natural h hn hfixed e (R.subgroupOf J) le_rfl
  obtain ⟨hDI,hDN,⟨a⟩⟩ := hs I hI
  have hd : Disjoint I (fixedSpace rho B) := by
    rw [KernelOffenders.omega_fixedSpace_eq_bot h hn hfixed]
    exact disjoint_bot_right
  have hc : Nat.card I = Nat.card F ^ 3 := by
    calc
      Nat.card I = Nat.card (centralQuotient rho B I) :=
        Nat.card_congr (centralSectionEquiv rho B I hd).toEquiv
      _ = Nat.card (Fin 3 → (coefficientField h hn).Carrier) :=
        Nat.card_congr a.linearEquiv.toEquiv
      _ = Nat.card F ^ 3 := by rw [Nat.card_fun,Nat.card_fin]; rfl
  refine ⟨hc,?_⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h.field_card,←pow_mul] at hc
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc).trans (Nat.mul_comm n 3)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentRecognition
