module

public import CFSG.Quasithin.ChapterB.Section01.Restriction
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.Representation.BinaryOffender.TwoCoreFixedSpace
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# Two-core and irreducible-section reduction for B.1.11

The equality `[L,A] = L` makes L normal in the generated overgroup `L ⊔ A`,
not necessarily in the original ambient group. A normal quasisimple subgroup
centralizes the two-core: the component dichotomy would otherwise put the
nontrivial perfect group inside a soluble two-group. Centralizers of its image
then lift across any action kernel centralizing L by perfectness.

These are independent parts of the reduction in Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.1.10–11, printed pp. 72–73.
The fixed-space kernel equality follows from the P × Q lemma, applied to the
kernel intersected with L. Minimal dimension gives an Irr⁺ section without an
existence assumption. All quotient maps use their actual action kernels.

`irreducibleReduction_local` gives the reduction in K = L ⊔ A.
`irreducibleReduction_generated` is its form after this change of ambient group.
`irreducibleReduction_lift` transports a chosen invariant section back through
the action image. The imported ambient-section lemmas then transport from K to
G. The later FF and section-centralizer premises remain explicit; choosing the
section's overgroup and discharging those premises belongs to B.1.11's parent
assembly.
-/

public section
namespace CFSG.Quasithin.ChapterB
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The commutator hypothesis supplies precisely the needed relative normality. -/
theorem irreducibleReduction_normal (L A : Subgroup G) (hLA : ⁅L, A⁆ = L) :
    (L.subgroupOf (L ⊔ A)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer le_sup_left).2
  apply sup_le L.le_normalizer
  simpa only [hLA] using normalizer_commutator_ge_right L A

/-- A normal quasisimple subgroup centralizes the two-core. -/
theorem irreducibleReduction_core_centralizes [Finite G] (L : Subgroup G)
    [L.Normal] [IsQuasisimple L] : pCore 2 G ≤ centralizer (L : Set G) := by
  have hL : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  rcases hL.normal_dichotomy (pCore 2 G) with hle | hc
  · have hp : IsPGroup 2 L := pCore_isPGroup.of_injective (inclusion hle)
      (inclusion_injective hle)
    let : Group.IsNilpotent L := hp.isNilpotent
    let : Nontrivial L := by
      let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
      exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center L))
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])

/-- In the original ambient group the core and centralizer are both relative to K. -/
theorem irreducibleReduction_local_core_centralizes [Finite G]
    (L A : Subgroup G) [IsQuasisimple L] (hLA : ⁅L, A⁆ = L) :
    pCore 2 ↥(L ⊔ A) ≤
      centralizer (L.subgroupOf (L ⊔ A) : Set ↥(L ⊔ A)) := by
  let := irreducibleReduction_normal L A hLA
  let : IsQuasisimple (L.subgroupOf (L ⊔ A)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left)).symm
  exact irreducibleReduction_core_centralizes _

end CFSG.Quasithin.ChapterB


namespace CFSG.Quasithin.ChapterB
open Subgroup Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D]

omit [Finite G] in
theorem irreducibleReduction_image_core_eq_bot (f : G →* D)
    (hf : Function.Surjective f) (hker : f.ker = pCore 2 G) : pCore 2 D = ⊥ := by
  have hp : IsPGroup 2 ((pCore 2 D).comap f) :=
    pCore_isPGroup.comap_of_ker_isPGroup f (hker.symm ▸ pCore_isPGroup)
  have hle : (pCore 2 D).comap f ≤ pCore 2 G := le_sSup ⟨inferInstance, hp⟩
  apply le_antisymm _ bot_le
  intro d hd
  obtain ⟨g, rfl⟩ := hf d
  have hk : g ∈ f.ker := by rw [hker]; exact hle hd
  exact hk

theorem irreducibleReduction_image_quasisimple (L : Subgroup G) [IsQuasisimple L]
    (f : G →* D) (hker : f.ker = pCore 2 G) : IsQuasisimple (L.map f) := by
  have hn : ¬ L ≤ f.ker := by
    intro hle
    rw [hker] at hle
    have hp : IsPGroup 2 L := pCore_isPGroup.of_injective (inclusion hle)
      (inclusion_injective hle)
    let : Group.IsNilpotent L := hp.isNilpotent
    let : Nontrivial L := by
      let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
      exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center L))
    exact Group.IsPerfect.not_isSolvable L inferInstance
  let : Nontrivial (L.map f) := (nontrivial_iff_ne_bot _).2
    (fun h => hn ((map_eq_bot_iff L).mp h))
  exact IsQuasisimple.of_surjective (f.subgroupMap L) (f.subgroupMap_surjective L)

theorem irreducibleReduction_offender_image_ne_bot (L A : Subgroup G)
    [L.Normal] [IsQuasisimple L] (hLA : ⁅L, A⁆ = L)
    (f : G →* D) (hker : f.ker = pCore 2 G) : A.map f ≠ ⊥ := by
  intro ha
  have hA : A ≤ centralizer (L : Set G) :=
    ((map_eq_bot_iff A).mp ha).trans (hker.symm ▸ irreducibleReduction_core_centralizes L)
  have hc : ⁅L, A⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hA
  have hLbot : L = ⊥ := hLA.symm.trans hc
  let : Nontrivial L := by
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center L))
  exact (nontrivial_iff_ne_bot L).1 inferInstance hLbot
end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.ChapterB
open Subgroup Theory.GroupTheory Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Conditional assembly after the fixed-space kernel theorem: the actual
image has trivial two-core, quasisimple L-image, and a nontrivial best offender.
The kernel hypothesis is discharged by the B.1.10 fixed-space argument in
`irreducibleReduction_generated` below. -/
theorem irreducibleReduction_fixedSpace_image (L A : Subgroup G)
    [L.Normal] [IsQuasisimple L] (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A)
    (hker : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G) :
    let U := fixedSpace ρ (pCore 2 G)
    pCore 2 (subspaceActionImage ρ U) = ⊥ ∧
      IsQuasisimple (restrictedSubgroup ρ U L) ∧
      restrictedSubgroup ρ U A ≠ ⊥ ∧
      IsBestOffender (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) := by
  let U := fixedSpace ρ (pCore 2 G)
  have hU := fixedSpace_stable_of_normal ρ (pCore 2 G)
  let f := invariantActionHom ρ U hU
  have hf : f.ker = pCore 2 G := (invariantActionHom_ker ρ U hU).trans hker
  have hAn := irreducibleReduction_offender_image_ne_bot L A hLA f hf
  have hmove : ¬ U ≤ fixedSpace ρ A := by
    intro hfix
    apply hAn
    apply (map_eq_bot_iff A).2
    rw [invariantActionHom_ker]
    intro a ha
    exact ⟨mem_top a, fun v hv => hfix hv ⟨a, ha⟩⟩
  refine ⟨irreducibleReduction_image_core_eq_bot f
    (invariantActionHom_surjective ρ U hU) hf, ?_, ?_, ?_⟩
  · rw [← invariantActionHom_map ρ U hU]
    exact irreducibleReduction_image_quasisimple L f hf
  · rwa [← invariantActionHom_map ρ U hU]
  · exact hA.restricted ρ U (le_trans le_top hU) hmove

end CFSG.Quasithin.ChapterB


open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The two-core reduction for the generated overgroup: all kernel, Fitting,
offender and Irr⁺ existence premises are discharged. -/
theorem irreducibleReduction_generated (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hLA : ⁅L,A⁆ = L) (hgen : L ⊔ A = ⊤) (hA : IsBestOffender ρ A) :
    let U := fixedSpace ρ (pCore 2 G)
    subspaceKernel ρ U ⊤ = pCore 2 G ∧
    pCore 2 G ≤ centralizer (L : Set G) ∧
    pCore 2 (subspaceActionImage ρ U) = ⊥ ∧
    IsQuasisimple (restrictedSubgroup ρ U L) ∧
    generalizedFitting (subspaceActionImage ρ U) = restrictedSubgroup ρ U L ∧
    restrictedSubgroup ρ U A ≠ ⊥ ∧
    IsBestOffender (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) ∧
    ∃ I, IsIrrPlus (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U L) I := by
  let U := fixedSpace ρ (pCore 2 G)
  let : IsElementaryAbelian 2 A := hA.1.2
  have hp := IsElementaryAbelian.isPGroup 2 A
  have hc := irreducibleReduction_core_centralizes L
  have hk := fixedSpace_kernel_eq_twoCore_of_centralizes ρ hfaith L
    (quotient_isPGroup_of_sup_eq_top A L hp (sup_comm L A ▸ hgen)) hc
  obtain ⟨hcore, hquasi, hne, hbest⟩ := irreducibleReduction_fixedSpace_image ρ L A hLA hA hk
  let hU := fixedSpace_stable_of_normal ρ (pCore 2 G)
  let f := invariantActionHom ρ U hU
  have hf := invariantActionHom_surjective ρ U hU
  have hmap := invariantActionHom_map ρ U hU
  have hgen' : restrictedSubgroup ρ U L ⊔ restrictedSubgroup ρ U A = ⊤ := by
    rw [← hmap L, ← hmap A, ← Subgroup.map_sup, hgen, map_top_of_surjective f hf]
  let : (restrictedSubgroup ρ U L).Normal := by
    rw [← hmap L]
    exact Subgroup.Normal.map inferInstance f hf
  let : IsQuasisimple (restrictedSubgroup ρ U L) := hquasi
  have hfit := generalizedFitting_eq_of_quasisimple_two_quotient
    (restrictedSubgroup ρ U L)
    (quotient_isPGroup_of_sup_eq_top (restrictedSubgroup ρ U A) _
      (by rw [← hmap A]; exact hp.map f) (by simpa only [sup_comm] using hgen')) hcore
  have hLn : restrictedSubgroup ρ U L ≠ ⊥ := by
    let : IsSimpleGroup ((restrictedSubgroup ρ U L) ⧸ center (restrictedSubgroup ρ U L)) := IsQuasisimple.simple
    let : Nontrivial (restrictedSubgroup ρ U L) := Function.Surjective.nontrivial
      (QuotientGroup.mk'_surjective (center (restrictedSubgroup ρ U L)))
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  exact ⟨hk, hc, hcore, hquasi, hfit, hne, hbest,
    exists_isIrrPlus_of_faithful (subspaceImageRepresentation ρ U)
      (subspaceImageRepresentation_injective ρ U) _ hLn⟩
end CFSG.Quasithin.ChapterB


namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The kernel on L is its intrinsic two-core, as asserted in B.1.11. -/
theorem irreducibleReduction_component_kernel (L : Subgroup G) [L.Normal]
    (hker : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G) :
    subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) L = (pCore 2 L).map L.subtype := by
  have hlocal : (pCore 2 G).subgroupOf L ≤ pCore 2 L :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  have hglobal : (pCore 2 L).map L.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map L.subtype⟩
  apply le_antisymm
  · intro x hx
    have hq : x ∈ pCore 2 G := hker ▸ (show x ∈ subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ from ⟨mem_top _, hx.2⟩)
    exact ⟨⟨x, hx.1⟩, hlocal hq, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    have hzq := hglobal (mem_map_of_mem L.subtype hz)
    have hzfix : (z : G) ∈ subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ := hker.symm ▸ hzq
    exact ⟨z.property, hzfix.2⟩

/-- Explicit quotient equivalence for the identified two-core action kernel. -/
noncomputable def irreducibleReduction_quotientEquiv (W : Submodule (ZMod 2) V)
    (hW : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W)
    (hk : subspaceKernel ρ W ⊤ = pCore 2 G) :
    G ⧸ pCore 2 G ≃* subspaceActionImage ρ W :=
  (QuotientGroup.quotientMulEquivOfEq ((invariantActionHom_ker ρ W hW).trans hk).symm).trans
    (invariantActionQuotientEquiv ρ W hW)

end CFSG.Quasithin.ChapterB


namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The source setup in an arbitrary ambient G, using only normality inside L ⊔ A. -/
theorem irreducibleReduction_local (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L] (hLA : ⁅L,A⁆ = L)
    (hA : IsBestOffender ρ A) :
    let K := L ⊔ A
    let τ := ρ.comp K.subtype
    let L₀ := L.subgroupOf K
    let A₀ := A.subgroupOf K
    let U := fixedSpace τ (pCore 2 K)
    subspaceKernel τ U ⊤ = pCore 2 K ∧
    pCore 2 K ≤ centralizer (L₀ : Set K) ∧
    pCore 2 (subspaceActionImage τ U) = ⊥ ∧
    IsQuasisimple (restrictedSubgroup τ U L₀) ∧
    generalizedFitting (subspaceActionImage τ U) = restrictedSubgroup τ U L₀ ∧
    restrictedSubgroup τ U A₀ ≠ ⊥ ∧
    IsBestOffender (subspaceImageRepresentation τ U) (restrictedSubgroup τ U A₀) ∧
    ∃ I, IsIrrPlus (subspaceImageRepresentation τ U) (restrictedSubgroup τ U L₀) I := by
  let K := L ⊔ A
  let L₀ := L.subgroupOf K
  let A₀ := A.subgroupOf K
  let : L₀.Normal := irreducibleReduction_normal L A hLA
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ K from le_sup_left)).symm
  have hcomm : ⁅L₀, A₀⁆ = L₀ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator]
    change ⁅(L.subgroupOf K).map K.subtype, (A.subgroupOf K).map K.subtype⁆ =
      (L.subgroupOf K).map K.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ K from le_sup_right), hLA]
  have hgen : L₀ ⊔ A₀ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup]
    change (L.subgroupOf K).map K.subtype ⊔ (A.subgroupOf K).map K.subtype =
      (⊤ : Subgroup K).map K.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ K from le_sup_right)]
    exact K.range_subtype.symm.trans K.subtype.range_eq_map
  exact irreducibleReduction_generated (ρ.comp K.subtype)
    (hfaith.comp K.subtype_injective) L₀ A₀ hcomm hgen
    (hA.subgroupOf ρ (show A ≤ K from le_sup_right))

end CFSG.Quasithin.ChapterB


namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Lift a chosen invariant Irr⁺ section through the actual fixed-space action.
The FF and section-centralizer implications take exactly the later premises;
the kernel-centralization premise is discharged here by the two-core reduction. -/
theorem irreducibleReduction_lift (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hLA : ⁅L,A⁆ = L) (hgen : L ⊔ A = ⊤) (hA : IsBestOffender ρ A)
    (D₀ : Subgroup (subspaceActionImage ρ (fixedSpace ρ (pCore 2 G))))
    (I : Submodule (ZMod 2) (fixedSpace ρ (pCore 2 G)))
    (hL : restrictedSubgroup ρ (fixedSpace ρ (pCore 2 G)) L ≤ D₀)
    (hI : IsIrrPlus (subspaceImageRepresentation ρ (fixedSpace ρ (pCore 2 G)))
      (restrictedSubgroup ρ (fixedSpace ρ (pCore 2 G)) L) I)
    (hDI : D₀ ≤ subspaceStabilizer (subspaceImageRepresentation ρ (fixedSpace ρ (pCore 2 G))) I) :
    let U := fixedSpace ρ (pCore 2 G)
    let σ := subspaceImageRepresentation ρ U
    let f := invariantActionHom ρ U (fixedSpace_stable_of_normal ρ (pCore 2 G))
    let J := I.map U.subtype
    let H := D₀.comap f
    ∃ hDN : D₀ ≤ normalizer (L.map f : Set (subspaceActionImage ρ U)),
      ∃ hHJ : H ≤ subspaceStabilizer ρ J,
        L ≤ H ∧ IsIrrPlus ρ L J ∧
        Nonempty (centralQuotient σ (L.map f) I ≃ₗ[ZMod 2] centralQuotient ρ L J) ∧
        Nonempty (actionImage (centralSectionRepresentation σ (L.map f) D₀ I hDI hDN) ≃*
          actionImage (centralSectionRepresentation ρ L H J hHJ le_normalizer_of_normal)) ∧
        (IsFFModule (imageRepresentation (centralSectionRepresentation σ (L.map f) D₀ I hDI hDN)) →
          IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H J hHJ le_normalizer_of_normal))) ∧
        ((centralSectionRepresentation σ (L.map f) D₀ I hDI hDN).ker.map D₀.subtype ≤
          D₀ ⊓ centralizer (L.map f : Set (subspaceActionImage ρ U)) →
          (centralSectionRepresentation ρ L H J hHJ le_normalizer_of_normal).ker.map H.subtype ≤
            H ⊓ centralizer (L : Set G)) := by
  let U := fixedSpace ρ (pCore 2 G)
  let σ := subspaceImageRepresentation ρ U
  let f := invariantActionHom ρ U (fixedSpace_stable_of_normal ρ (pCore 2 G))
  have hf : Function.Surjective f := invariantActionHom_surjective ρ U _
  have hact : ∀ g w, ρ g (U.subtype w) = U.subtype (σ (f g) w) := fun _ _ => rfl
  let : (L.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hDN : D₀ ≤ normalizer (L.map f : Set (subspaceActionImage ρ U)) := le_normalizer_of_normal
  let hHJ := preimage_stabilizes_embedding ρ σ f U.subtype hact D₀ I hDI
  have hmap : L.map f = restrictedSubgroup ρ U L := invariantActionHom_map ρ U _ L
  refine ⟨hDN, hHJ, le_preimage_of_map_le f L D₀ (hmap.symm ▸ hL), ?_,
    ⟨embeddedCentralQuotientEquiv ρ σ f U.subtype U.subtype_injective hact L I⟩,
    ⟨embeddedSectionImageEquiv ρ σ f U.subtype U.subtype_injective hact hf L D₀ I hDI hDN le_normalizer_of_normal⟩,
    ?_, ?_⟩
  · exact IsIrrPlus.map_embedding ρ σ f U.subtype U.subtype_injective hact L I (hmap.symm ▸ hI)
  · intro hFF
    exact image_isFFModule_of_equivariant _ _ (preimageSubgroupHom f D₀)
      (preimageSubgroupHom_surjective f hf D₀)
      (embeddedCentralQuotientEquiv ρ σ f U.subtype U.subtype_injective hact L I)
      (fun h v => (embeddedSection_intertwines ρ σ f U.subtype U.subtype_injective hact L D₀ I
        hDI hDN le_normalizer_of_normal h v).symm) hFF
  · intro hcent
    have hred := irreducibleReduction_generated ρ hfaith L A hLA hgen hA
    have hk : f.ker ≤ centralizer (L : Set G) := by
      rw [invariantActionHom_ker, hred.1]
      exact hred.2.1
    exact section_centralizer_lifts ρ σ f U.subtype U.subtype_injective hact L D₀ I
      hDI hDN le_normalizer_of_normal hk hcent

end CFSG.Quasithin.ChapterB
