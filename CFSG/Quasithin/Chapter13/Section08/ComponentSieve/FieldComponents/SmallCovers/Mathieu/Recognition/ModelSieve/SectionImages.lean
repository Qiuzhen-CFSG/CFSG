module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve.Comparisons
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.Quotient
public import Theory.Mathieu.M22.Properties.Simplicity

/-!
# Subgroups and section actions in the M₂₂ FF reduction

A centerless normal quasisimple subgroup with trivial centralizer is the
whole generalized Fitting subgroup: every other component centralizes it,
and its Fitting subgroup is solvable. Applying this to overgroups of an
actual M₂₂ generalized Fitting subgroup retains possible outer supplements.

The native M₂₂ facts also make the two-core trivial and turn any best
offender into the commutator input of B.1.11. Given that theorem's invariant
Irr⁺ section and kernel-centralizer conclusion, the action on the literal
I/C_I(L) is faithful and satisfies the genuine B.4 hypotheses. Offenders on
its faithful action image transport back through an actual equivalence.
The existence of that section is deliberately not assumed to follow merely
from irreducible-section existence without invariance and the FF property.

Source: Aschbacher–Smith, B.1.11, printed pp.72–73, and B.4.2, p.86,
as used in 13.8.21(2), p.956 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu
open CFSG.Quasithin.ChapterB.QuasisimpleSections
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve.SectionImages

private theorem fitting_eq_of_normal_quasisimple {D : Type*} [Group D] [Finite D]
    (L : Subgroup D) [L.Normal] [IsQuasisimple L]
    (hc : centralizer (L : Set D) = ⊥) : generalizedFitting D = L := by
  have hL : IsComponent D L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  apply le_antisymm
  · apply sup_le
    · rcases hL.normal_dichotomy (fittingSubgroup D) with h | h
      · have hs : Group.IsSolvable L :=
          Group.isSolvable_of_isSolvable_injective (inclusion_injective h)
        exact (Group.IsPerfect.not_isSolvable L hs).elim
      · have hf := commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h)
        rw [hc] at hf
        exact hf.trans bot_le
    · apply sSup_le
      intro M hM
      rcases hM.normal_dichotomy L with h | h
      · exact h
      · exact ((commutator_eq_bot_iff_le_centralizer.mp h).trans hc.le).trans bot_le
  · exact component_le_generalizedFitting D L hL

/-- Transport the native trivial center through the supplied M₂₂ marking. -/
theorem center_eq_bot {L : Type*} [Group L] (e : L ≃* M22) : center L = ⊥ := by
  apply bot_unique
  intro x hx
  have hz : e x ∈ center M22 := (centerCongr e ⟨x, hx⟩).property
  rw [m22_center_eq_bot, mem_bot] at hz
  exact e.injective (hz.trans e.map_one.symm)

/-- The native simplicity and trivial center give quasisimplicity of the marked group. -/
theorem quasisimple {L : Type*} [Group L] (e : L ≃* M22) : IsQuasisimple L := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : IsSimpleGroup L := e.isSimpleGroup
  have hn : ¬ IsMulCommutative L := by
    intro h
    let := h
    exact top_ne_bot ((Subgroup.center_eq_top (G := L)).symm.trans (center_eq_bot e))
  let : Group.IsPerfect L := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator L)
      inferInstance).resolve_left (fun h => hn ((commutator_eq_bot_iff L).mp h))⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (center_eq_bot e)).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

/-- The entire generalized Fitting subgroup is self-centralizing, and its M₂₂ center is trivial. -/
theorem centralizer_fitting_eq_bot {D : Type*} [Group D] [Finite D]
    (e : generalizedFitting D ≃* M22) :
    centralizer (generalizedFitting D : Set D) = ⊥ := by
  apply bot_unique
  intro x hx
  have hxL : x ∈ generalizedFitting D := centralizer_generalizedFitting_le hx
  have hz : (⟨x, hxL⟩ : generalizedFitting D) ∈ center (generalizedFitting D) := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hx l l.property)
  rw [center_eq_bot e, mem_bot] at hz
  exact congrArg Subtype.val hz

/-- Every overgroup retains the whole original M₂₂ as its generalized Fitting subgroup.
No assumption that the overgroup equals M₂₂, or has no outer supplement, is used. -/
theorem overgroup_fitting {D : Type*} [Group D] [Finite D]
    (e : generalizedFitting D ≃* M22) (H : Subgroup D)
    (hLH : generalizedFitting D ≤ H) :
    generalizedFitting H = (generalizedFitting D).subgroupOf H := by
  let L := (generalizedFitting D).subgroupOf H
  let : IsQuasisimple L := quasisimple ((subgroupOfEquivOfLe hLH).trans e)
  apply fitting_eq_of_normal_quasisimple L
  apply bot_unique
  intro x hx
  have hc : (x : D) ∈ centralizer (generalizedFitting D : Set D) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val
      (mem_centralizer_iff.mp hx (⟨l, hLH hl⟩ : H) hl)
  rw [centralizer_fitting_eq_bot e, mem_bot] at hc
  exact Subtype.ext hc

/-- A normal two-subgroup centralizes the component and must be trivial. -/
theorem twoCore_eq_bot {D : Type*} [Group D] [Finite D]
    (e : generalizedFitting D ≃* M22) : pCore 2 D = ⊥ := by
  let L := generalizedFitting D
  let : IsQuasisimple L := quasisimple e
  have hL : IsComponent D L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  rcases hL.normal_dichotomy (pCore 2 D) with h | h
  · let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
    have hs : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective h)
    exact (Group.IsPerfect.not_isSolvable L hs).elim
  · have hc := commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h)
    exact bot_unique (hc.trans (centralizer_fitting_eq_bot e).le)

universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V)

/-- An arbitrary FF module supplies the best offender and commutator
hypothesis required by B.1.11. Constructing its invariant section is the remaining step. -/
theorem bestOffender_commutator (e : generalizedFitting D ≃* M22)
    (hff : IsFFModule ρ) :
    ∃ A : Subgroup D, IsBestOffender ρ A ∧
      ⁅generalizedFitting D, A⁆ = generalizedFitting D := by
  obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  let : IsElementaryAbelian 2 A := hA.1.2
  exact ⟨A, hA, commutator_fitting_eq (twoCore_eq_bot e) (quasisimple e)
    hA.1.1 (IsElementaryAbelian.isPGroup 2 A)⟩

omit [Finite V] in
/-- The kernel-centralizer conclusion of B.1.11 makes the literal central-section action faithful. -/
theorem section_faithful (e : generalizedFitting D ≃* M22)
    (H : Subgroup D) (I : Submodule (ZMod 2) V)
    (hHI : H ≤ subspaceStabilizer ρ I)
    (hker : (centralSectionRepresentation ρ (generalizedFitting D) H I hHI
      le_normalizer_of_normal).ker.map H.subtype ≤
        centralizer (generalizedFitting D : Set D)) :
    Function.Injective (centralSectionRepresentation ρ (generalizedFitting D) H I hHI
      le_normalizer_of_normal) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hc := hker (mem_map_of_mem H.subtype hx)
  rw [centralizer_fitting_eq_bot e, mem_bot] at hc
  exact Subtype.ext hc

local instance quotient_finite (L : Subgroup D) (I : Submodule (ZMod 2) V) :
    Finite (centralQuotient ρ L I) :=
  Finite.of_surjective ((fixedSpace ρ L).comap I.subtype).mkQ
    (Submodule.mkQ_surjective _)

/-- A B.1.11 section satisfies all the actual B.4 hypotheses on its stabilizing
overgroup. Irreducibility is transported on the literal quotient, through the
subgroup inclusion and the proved generalized-Fitting equality. -/
theorem section_hypotheses {𝒦 : GroupClass.{u}} (hD : IsSQTK 𝒦 D)
    (e : generalizedFitting D ≃* M22) (H : Subgroup D)
    (hLH : generalizedFitting D ≤ H) (I : Submodule (ZMod 2) V)
    (hI : IsIrrPlus ρ (generalizedFitting D) I)
    (hHI : H ≤ subspaceStabilizer ρ I)
    (hker : (centralSectionRepresentation ρ (generalizedFitting D) H I hHI
      le_normalizer_of_normal).ker.map H.subtype ≤
        centralizer (generalizedFitting D : Set D)) :
    B4Hypotheses 𝒦 (centralSectionRepresentation ρ (generalizedFitting D) H I hHI
      le_normalizer_of_normal) := by
  let σ := centralSectionRepresentation ρ (generalizedFitting D) H I hHI
    le_normalizer_of_normal
  let f : (generalizedFitting D).subgroupOf H ≃* generalizedFitting D :=
    subgroupOfEquivOfLe hLH
  have hfit := overgroup_fitting e H hLH
  refine ⟨hD.subgroup H, section_faithful ρ e H I hHI hker,
    quasisimple ((MulEquiv.subgroupCongr hfit).trans (f.trans e)), ?_⟩
  change IsIrreducible (σ.comp (generalizedFitting H).subtype)
  rw [hfit]
  have he : σ.comp ((generalizedFitting D).subgroupOf H).subtype =
      (centralQuotientRepresentation ρ (generalizedFitting D) I hI.choose).comp
        f.toMonoidHom := by
    ext g v
    rfl
  rw [he]
  exact (irreducible_comp_surjective_iff f.toMonoidHom f.surjective _).mpr hI.choose_spec.2

/-- Pull an FF offender back through the actual faithful action-image equivalence. -/
theorem ff_of_faithful_image {E : Type*} [Group E]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (hf : Function.Injective σ)
    (hff : IsFFModule (imageRepresentation σ)) : IsFFModule σ := by
  let f : E ≃* actionImage σ := MulEquiv.ofBijective (actionHom σ)
    ⟨fun x y h => hf (congrArg (imageRepresentation σ) h),
      σ.asGroupHom.rangeRestrict_surjective⟩
  apply hff.map_equivariant (imageRepresentation σ) σ f.symm.toMonoidHom f.symm.injective
    (LinearEquiv.refl _ _)
  intro g v
  exact (congrArg (fun a => imageRepresentation σ a v) (f.apply_symm_apply g)).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.ModelSieve.SectionImages

