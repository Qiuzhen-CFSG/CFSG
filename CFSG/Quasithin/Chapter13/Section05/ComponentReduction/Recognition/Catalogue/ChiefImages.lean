module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.Sections
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.ComponentAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import Theory.Representation.BinaryOffender.QuasisimpleImage
public import Theory.Representation.BinaryOffender.CubicCenterSections
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SQTKSectionImage
public import Theory.Representation.NormalConstituentDisplacement.FixedLine

/-!
# Faithful chief images for the catalogue step

This file supplies the missing action interface in 13.5.21.  A noncentral
chief section is sent to its literal binary action image.  The image retains
the marked component, and the B.4 hypotheses are discharged from the actual
two-group quotient and kernel data.  The Clifford split alternative is
resolved by the displacement-one exclusion supplied by the source
configuration; it is not replaced by an irreducibility assumption.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 13.5.21,
printed pp.923--924 (PDF pp.940--941), and B.4.2.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue

open Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
open CFSG.Quasithin.ChapterB.ComponentRecognition.SQTKSectionImage
open Section08.Source

universe u v

/-- The source clauses needed to eliminate the permutation case in Clifford
restriction.  `no_rank_one` is the actual displacement bound for the marked
component; it is discharged by the quasisimple/source configuration argument
in the enclosing recognition proof. -/
structure CliffordComponentInput {E W : Type*} [Group E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E) (v : E) where
  T : Subgroup E
  d : ℕ
  normal : L.Normal
  two : IsPGroup 2 T
  commutes : ∀ t : T, Commute v (t : E)
  fixed : ∀ w : W, (∀ t : T, ρ t w = w) →
    w ∈ LinearMap.range (ρ v - LinearMap.id)
  small : ∀ J : Subrepresentation (ρ.comp L.subtype),
    J.toRepresentation.IsIrreducible →
      3 ≤ Module.finrank (ZMod 2) J.toSubmodule
  displacement_rank : Module.finrank (ZMod 2)
      (LinearMap.range (ρ v - LinearMap.id)) = 2
  dimension : Module.finrank (ZMod 2) W = 2 * d
  no_rank_one : ∀ J : Subrepresentation (ρ.comp L.subtype),
    J.toRepresentation.IsIrreducible →
      Module.finrank (ZMod 2)
        (LinearMap.range ((ρ v - LinearMap.id).comp J.toSubmodule.subtype)) ≠ 1

@[simp] theorem action_kernel_eq {E W : Type*} [Group E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) :
    ρ.ker = (actionHom ρ).ker := by
  ext g
  constructor
  · intro hg
    apply (actionHom_eq_one_iff ρ g).2
    intro w
    have hh : ρ g = 1 := hg
    exact congrArg (fun f : Module.End (ZMod 2) W => f w) hh
  · intro hg
    have hh : actionHom ρ g = 1 := hg
    have hw : ∀ w, ρ g w = w := (actionHom_eq_one_iff ρ g).mp hh
    exact LinearMap.ext hw

/-- The marked component action is irreducible once the genuine fixed-plane
input is supplied.  The second branch of Clifford's alternative is removed
by the source displacement bound on each constituent. -/
theorem component_irreducible_of_clifford
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) E W)
    (hρ : ρ.IsIrreducible) (L : Subgroup E) (v : E)
    (h : CliffordComponentInput ρ L v) :
    IsIrreducible (ρ.comp L.subtype) := by
  let : L.Normal := h.normal
  rcases Representation.NormalConstituentDisplacement.constituent_alternative
      ρ hρ L h.T v h.d h.two h.commutes h.fixed h.small h.displacement_rank h.dimension with
    ⟨_, hirr | ⟨J, J', _, hJ, hJ', _, _, _, _, hdisp, hdisp'⟩⟩
  · exact hirr
  ·
    exact False.elim ((h.no_rank_one J hJ) hdisp)

/-- An actual binary action image of an SQTK group is SQTK when its kernel is
a two-group.  This is the precise quotient input used for the chief sections;
the homomorphism is the displayed action map, so no abstract replacement of
the section is made. -/
theorem image_sqtk_of_two_kernel
    {E W : Type u} [Group E] [Finite E] [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    {𝒦 : GroupClass.{u}} (ρ : Representation (ZMod 2) E W)
    (hE : IsSQTK 𝒦 E)
    (hker : IsPGroup 2 ρ.ker) :
    IsSQTK 𝒦 (actionImage ρ) := by
  constructor
  · intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [← primeRank_congr p
      (QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
        ρ.asGroupHom.rangeRestrict_surjective)]
    have hker' : IsPGroup 2 (actionHom ρ).ker := by
      rwa [← action_kernel_eq ρ]
    exact (primeRank_quotient_le_of_isTwoGroup p ho (actionHom ρ).ker hker').trans
      (hE.stronglyQuasithin p hp ho)
  · exact hE.isKGroup.of_surjective (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective

/-- B.4.2 for the literal chief action image.  The kernel centrality is kept
as an explicit source fact, while quasisimplicity of the marked image is
proved from the displayed surjection from the original component. -/
theorem b4_hypotheses_of_component
    {E W : Type u} [Group E] [Finite E] [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) E W)
    (L : Subgroup E) [L.Normal] [IsQuasisimple L]
    (hρ : IsIrreducible ρ)
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (hquot : IsPGroup 2 (E ⧸ L))
    (hkernel_central : (ρ.comp L.subtype).ker ≤ center L)
    (hkernel_two : IsPGroup 2 ρ.ker)
    (hcomponent : ¬ L ≤ ρ.ker)
    (hirr : IsIrreducible (ρ.comp L.subtype)) :
    Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple (imageRepresentation ρ) := by
  have _hcentral := hkernel_central
  let M : Subgroup (actionImage ρ) := actionSubgroup ρ L
  let f := actionHom ρ
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  let : M.Normal := Subgroup.Normal.map inferInstance f hf
  have hmap : L ≤ M.comap f := fun _ hl => mem_map_of_mem f hl
  have hqM : IsPGroup 2 (actionImage ρ ⧸ M) :=
    hquot.of_surjective (QuotientGroup.map L M f hmap)
      (QuotientGroup.map_surjective_of_surjective L M f
        ((QuotientGroup.mk'_surjective M).comp hf) hmap)
  have hE' : IsSQTK KnownSimple.IsKnownSimple E :=
    sqtk_of_twoGroup_quotient knownSimple_containsSimpleTwoGroups L hquot hL
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple (actionImage ρ) := by
    exact image_sqtk_of_two_kernel ρ hE' hkernel_two
  have hMbot : M ≠ ⊥ := by
    intro hbot
    apply hcomponent
    have hmapbot : L ≤ (actionHom ρ).ker :=
      (Subgroup.map_eq_bot_iff L).mp hbot
    simpa [action_kernel_eq ρ] using hmapbot
  let : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMbot
  let : IsQuasisimple M := IsQuasisimple.of_surjective
    (f.subgroupMap L) (f.subgroupMap_surjective L)
  have hcore : pCore 2 (actionImage ρ) = ⊥ := by
    let _ : IsIrreducible (imageRepresentation ρ) :=
      imageRepresentation_irreducible ρ hρ
    exact actionImage_twoCore_eq_bot ρ hρ
  have hfit : generalizedFitting (actionImage ρ) = M :=
    generalizedFitting_eq_of_quasisimple_two_quotient M hqM hcore
  have hirrM : IsIrreducible ((imageRepresentation ρ).comp M.subtype) := by
    change IsIrreducible
      ((imageRepresentation ρ).comp (actionSubgroup ρ L).subtype)
    let fL : L →* actionSubgroup ρ L := (actionHom ρ).subgroupMap L
    apply (irreducible_comp_surjective_iff fL
      (f.subgroupMap_surjective L)
      ((imageRepresentation ρ).comp (actionSubgroup ρ L).subtype)).mp
    have heq :
        ((imageRepresentation ρ).comp (actionSubgroup ρ L).subtype).comp fL =
          ρ.comp L.subtype := by
      ext x w
      rfl
    rw [heq]
    exact hirr
  have hfitqs : IsQuasisimple (generalizedFitting (actionImage ρ)) := by
    rw [hfit]
    infer_instance
  have hfitirr : IsIrreducible
      ((imageRepresentation ρ).comp (generalizedFitting (actionImage ρ)).subtype) := by
    rw [hfit]
    exact hirrM
  exact ⟨hsqtk, imageRepresentation_injective ρ, hfitqs, hfitirr⟩

/-- Apply the preceding construction to a literal selected section.  Every
chief-action premise remains visible in this application, so the enclosing
recognition theorem can discharge the source configuration one clause at a
time. -/
theorem classified_section_with_chief_images
    {G : Type u} [Group G] [Finite G]
    (D : ChapterF.Section09.Setup G) (K : Subgroup G)
    (h : D.Hypothesis)
    [(D.V₁.subgroupOf D.UH).Normal]
    [IsElementaryAbelian 2 (Action.ModuleGroup D)]
    [(component D K).Normal]
    (s : Selected D K)
    (earlier42 : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (earlier45 : Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.FullB45.{u,u}
      KnownSimple.IsKnownSimple)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hv2 : v ^ 2 = 1)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hsection : IsIrreducible (chiefRepresentation D K h U N))
    (hL : IsSQTK KnownSimple.IsKnownSimple (component D K))
    (hquot : IsPGroup 2 (actor D K ⧸ component D K))
    (hkernel_central :
      ((chiefRepresentation D K h U N).comp (component D K).subtype).ker ≤
        center (component D K))
    (hkernel_two : IsPGroup 2 (chiefRepresentation D K h U N).ker)
    (hclifford : CliffordComponentInput
      (chiefRepresentation D K h U N) (component D K) v) :
    FullCatalogueAction (imageRepresentation (chiefRepresentation D K h U N)) := by
  let : IsQuasisimple (starImage D.H K) := s.quasisimple
  let : IsQuasisimple (component D K) :=
    IsQuasisimple.of_mulEquiv
      (subgroupOfEquivOfLe (show starImage D.H K ≤ actor D K from le_sup_left)).symm
  have hcomponent_irreducible := component_irreducible_of_clifford
    (chiefRepresentation D K h U N) hsection (component D K) v hclifford
  apply classified_section D K h s earlier42 earlier45 hcard heven v hv hv2 hr U N hn
  exact b4_hypotheses_of_component (chiefRepresentation D K h U N)
    (component D K) hsection hL hquot hkernel_central hkernel_two hn
    hcomponent_irreducible

/-- The cubic-centre constituent can be chosen faithful on the original
component.  This preserves the original `L`, as required for the triple-
`A₆` exclusion; passing only to a central quotient would lose that input. -/
theorem exists_faithful_original_constituent_of_cubic_center
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E) [IsQuasisimple L]
    (hρ : Function.Injective ρ)
    (hcenter : Nat.card (center L) = 3) :
    ∃ I, ∃ hI : IsIrrPlus ρ L I,
      Function.Injective (centralQuotientRepresentation ρ L I hI.choose) := by
  exact exists_faithful_isIrrPlus_of_cubic_center ρ L
    (hρ.comp L.subtype_injective) hcenter

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
