module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover.Ambient
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The central moved cover on the original characteristic replacement

Restriction to the minimum characteristic overgroup preserves the entire
initial moved subgroup and its full movement by the component. That subgroup
remains inside the central omega of the new two-core. Its natural central
quotient gives a faithful action of the new two-core quotient on the binary
four-space; its central attachment has not been split off.

These are input facts for MS93 (3.8) and Section 5, not a large-distance
exclusion. Source: MS93 (3.2)(vi), (3.8), and Section 7, printed pp.863,
877--879, and 932--933.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC ChapterB.QuasisimpleSource
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M
local notation "X₀" => centralOmega L R

/-- The component of the replacement, on its literal subgroup carrier. -/
abbrev replacementComponent (d : Replacement L R) : Subgroup d.overgroup :=
  (K).subgroupOf d.overgroup

include h in
theorem replacementComponent_normal (d : Replacement L R) :
    (replacementComponent d).Normal := by
  let := h.relative_normal
  infer_instance

include h in
/-- Full movement survives both literal subgroup inclusions. -/
theorem replacementMoved_idempotent (d : Replacement L R) :
    ⁅replacementMoved d, replacementComponent d⁆ = replacementMoved d := by
  apply map_injective d.overgroup.subtype_injective
  rw [map_commutator, replacementMoved_map h d,
    map_subgroupOf_eq_of_le (show K ≤ d.overgroup from le_sup_left)]
  exact initial_moved_idempotent h

include h in
/-- No splitting is needed to place the entire moved cover in the new central omega. -/
theorem replacementMoved_le_omegaCenter (d : Replacement L R) :
    replacementMoved d ≤ omegaCenterIn (pCore 2 d.overgroup) := by
  intro x hx
  have hx₀ : (x : M) ∈ X₀ := commutator_le_left X₀ K hx
  obtain ⟨hxQ, hxC, hx2⟩ := (mem_omegaCenterIn_iff Q (x : M)).mp hx₀
  apply (mem_omegaCenterIn_iff _ x).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [replacement_core h d]
    exact hxQ
  · intro y hy
    apply Subtype.ext
    apply hxC y
    change ((d.overgroup.subtype y : M) ∈ pCore 2 M)
    have hy' : y ∈ (pCore 2 M).comap d.overgroup.subtype := by
      rw [← replacement_core h d]
      exact hy
    exact hy'
  · exact Subtype.ext hx2

/-- Coordinates refer to the original moved/fixed quotient, not a complement. -/
def naturalCoordinates (hn : InitialNatural h e hz) :
    ActionEquiv ((initialSection h e hz).action.comp (componentImage L R).subtype)
      (alternatingNatural 6) :=
  Classical.choice hn

/-- The entire original quotient acts on the same four-dimensional quotient. -/
def quotientAction (hn : InitialNatural h e hz) :
    Representation (ZMod 2) (M ⧸ Q) (BinaryPermutation.natural (Fin 6)) :=
  (initialSection h e hz).ambientAction (naturalCoordinates h e hz hn)

/-- Faithfulness uses the actual self-centralizing simple component image. -/
theorem quotientAction_faithful (hn : InitialNatural h e hz) :
    Function.Injective (quotientAction h e hz hn) := by
  let := relative_quotient_simple (R := R) e hz
  obtain ⟨_, hC, _, _, hc⟩ := MSCentralOrbit.component_image_structure K
    (R.subgroupOf (L ⊔ R)) h.component h.relative_radical.isPGroup h.relative_product
  let : (componentImage L R).Normal := hC
  apply (initialSection h e hz).ambientAction_faithful
    (naturalCoordinates h e hz hn) ?_ hc
  exact (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)).comp
    (alternatingGroup (Fin 6)).subtype_injective

/-- Restrict the original quotient action through the literal replacement inclusion. -/
def replacementAction (hn : InitialNatural h e hz) (d : Replacement L R) :
    Representation (ZMod 2) d.overgroup (BinaryPermutation.natural (Fin 6)) :=
  (quotientAction h e hz hn).comp ((QuotientGroup.mk' Q).comp d.overgroup.subtype)

/-- The faithful action kernel is the actual replacement two-core. -/
theorem replacementAction_kernel (hn : InitialNatural h e hz) (d : Replacement L R) :
    (replacementAction h e hz hn d).ker = pCore 2 d.overgroup := by
  rw [replacement_core h d]
  ext g
  change quotientAction h e hz hn (QuotientGroup.mk' Q (g : M)) = 1 ↔ (g : M) ∈ Q
  rw [← (quotientAction h e hz hn).map_one,
    (quotientAction_faithful h e hz hn).eq_iff]
  exact QuotientGroup.eq_one_iff _

/-- The component map uses the same natural-section marking as the ambient action. -/
def componentMap (hn : InitialNatural h e hz) (d : Replacement L R) :
    replacementComponent d →* alternatingGroup (Fin 6) :=
  (naturalCoordinates h e hz hn).groupEquiv.toMonoidHom.comp
    ((QuotientGroup.mk' Q).subgroupMap K |>.comp
      (subgroupOfEquivOfLe (show K ≤ d.overgroup from le_sup_left)).toMonoidHom)

theorem componentMap_surjective (hn : InitialNatural h e hz) (d : Replacement L R) :
    Function.Surjective (componentMap h e hz hn d) :=
  (naturalCoordinates h e hz hn).groupEquiv.surjective.comp
    (((QuotientGroup.mk' Q).subgroupMap_surjective K).comp
      (subgroupOfEquivOfLe (show K ≤ d.overgroup from le_sup_left)).surjective)

theorem replacementAction_component (hn : InitialNatural h e hz) (d : Replacement L R)
    (k : replacementComponent d) (v : BinaryPermutation.natural (Fin 6)) :
    replacementAction h e hz hn d k v =
      alternatingNatural 6 (componentMap h e hz hn d k) v :=
  (initialSection h e hz).ambientAction_component (naturalCoordinates h e hz hn)
    ((QuotientGroup.mk' Q).subgroupMap K
      ((subgroupOfEquivOfLe (show K ≤ d.overgroup from le_sup_left)) k)) v

include h in
theorem replacementMoved_normal (d : Replacement L R) :
    (replacementMoved d).Normal := by
  let := h.relative_normal
  infer_instance

/-- The original moved-space embedding restricted to the replacement. -/
def coverEmbedding (d : Replacement L R) :
    Multiplicative (initialSection h e hz).space.toSubmodule →* d.overgroup where
  toFun v := ⟨v.toAdd.val.toMul.val, initialMoved_le_replacement h d (by
    have hv := v.toAdd.property
    change v.toAdd.val ∈ subspaceCommutator (initialAction h e hz) ⊤
      (componentImage L R) at hv
    dsimp only [initialAction, componentImage] at hv
    rw [← NormalElementaryQuotient.commutatorSpace_eq X₀ (QuotientGroup.mk' Q)
      (QuotientGroup.mk'_surjective Q)
      ((QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h e hz).symm) K] at hv
    exact hv)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coverEmbedding_injective (d : Replacement L R) :
    Function.Injective (coverEmbedding h e hz d) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun x : d.overgroup => (x : M)) hab

theorem coverEmbedding_range (d : Replacement L R) :
    (coverEmbedding h e hz d).range = replacementMoved d := by
  let := h.relative_normal
  have hh := ElementaryMovedCover.embedding_range X₀ K (QuotientGroup.mk' Q)
    (QuotientGroup.mk'_surjective Q)
    ((QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h e hz).symm)
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change v.toAdd.val.toMul.val ∈ initialMoved L R
    dsimp only [initialMoved]
    rw [← hh]
    exact ⟨v, rfl⟩
  · intro hx
    change (x : M) ∈ initialMoved L R at hx
    dsimp only [initialMoved] at hx
    rw [← hh] at hx
    obtain ⟨v, hv⟩ := hx
    exact ⟨v, Subtype.ext hv⟩

/-- Coordinates on the entire moved subgroup, including the fixed kernel. -/
def coverEquiv (d : Replacement L R) :
    replacementMoved d ≃* Multiplicative (initialSection h e hz).space.toSubmodule :=
  ((MonoidHom.ofInjective (coverEmbedding_injective h e hz d)).trans
    (MulEquiv.subgroupCongr (coverEmbedding_range h e hz d))).symm

theorem coverEquiv_val (d : Replacement L R) (v : replacementMoved d) :
    ((coverEquiv h e hz d v).toAdd.val.toMul : M) = v.val.val := by
  have hh := (coverEquiv h e hz d).symm_apply_apply v
  exact congrArg (fun x : replacementMoved d => (x.val : M)) hh

/-- The literal surjection from the moved subgroup onto its natural central quotient. -/
def coverProjection (hn : InitialNatural h e hz) (d : Replacement L R) :
    replacementMoved d →* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  (((initialSection h e hz).coverProjection (naturalCoordinates h e hz hn)).toLinearMap.toAddMonoidHom.toMultiplicative).comp
    (coverEquiv h e hz d).toMonoidHom

theorem coverProjection_surjective (hn : InitialNatural h e hz) (d : Replacement L R) :
    Function.Surjective (coverProjection h e hz hn d) := by
  intro w
  obtain ⟨v, hv⟩ := (initialSection h e hz).central.toSubmodule.mkQ_surjective
    ((naturalCoordinates h e hz hn).linearEquiv.symm w.toAdd)
  obtain ⟨u, hu⟩ := (coverEquiv h e hz d).surjective (Multiplicative.ofAdd v)
  refine ⟨u, ?_⟩
  change Multiplicative.ofAdd ((naturalCoordinates h e hz hn).linearEquiv
    ((initialSection h e hz).central.toSubmodule.mkQ (coverEquiv h e hz d u).toAdd)) = w
  apply Multiplicative.toAdd.injective
  change (naturalCoordinates h e hz hn).linearEquiv
    ((initialSection h e hz).central.toSubmodule.mkQ (coverEquiv h e hz d u).toAdd) = w.toAdd
  apply (naturalCoordinates h e hz hn).linearEquiv.symm.injective
  simp only [LinearEquiv.symm_apply_apply]
  exact (congrArg (fun z : Multiplicative (initialSection h e hz).space.toSubmodule =>
    (initialSection h e hz).central.toSubmodule.mkQ z.toAdd) hu).trans hv

/-- The projection kernel is precisely the component-fixed subgroup of the actual cover. -/
theorem coverProjection_kernel (hn : InitialNatural h e hz) (d : Replacement L R) :
    (coverProjection h e hz hn d).ker =
      (centralizer (replacementComponent d : Set d.overgroup)).comap
        (replacementMoved d).subtype := by
  let := h.relative_normal
  ext v
  change ((initialSection h e hz).coverProjection (naturalCoordinates h e hz hn))
    (coverEquiv h e hz d v).toAdd = 0 ↔ _
  have hc := ElementaryMovedCover.cover_kernel_iff X₀ K (QuotientGroup.mk' Q)
    (QuotientGroup.mk'_surjective Q)
    ((QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h e hz).symm)
    (naturalCoordinates h e hz hn) (coverEquiv h e hz d v).toAdd
  change ((initialSection h e hz).coverProjection (naturalCoordinates h e hz hn))
    (coverEquiv h e hz d v).toAdd = 0 ↔
    ((coverEquiv h e hz d v).toAdd.val.toMul : M) ∈ centralizer (K : Set M) at hc
  rw [hc]
  change ((coverEquiv h e hz d v).toAdd.val.toMul : M) ∈ centralizer (K : Set M) ↔ _
  rw [coverEquiv_val]
  constructor
  · intro hv k hk
    exact Subtype.ext (hv k.val hk)
  · intro hv k hk
    exact congrArg d.overgroup.subtype
      (hv ⟨k, (show K ≤ d.overgroup from le_sup_left) hk⟩ hk)

/-- Equivariance keeps the original ambient conjugation on the whole cover. -/
theorem coverProjection_conjugate (hn : InitialNatural h e hz) (d : Replacement L R)
    (g : d.overgroup) (v w : replacementMoved d)
    (hw : (w : d.overgroup) = g * (v : d.overgroup) * g⁻¹) :
    (coverProjection h e hz hn d w).toAdd =
      replacementAction h e hz hn d g (coverProjection h e hz hn d v).toAdd := by
  have he : (coverEquiv h e hz d w).toAdd =
      (initialSection h e hz).space.toRepresentation (QuotientGroup.mk' Q (g : M))
        (coverEquiv h e hz d v).toAdd := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coverEquiv_val]
    change (w.val : M) =
      ((initialAction h e hz (QuotientGroup.mk' Q (g : M))
        (coverEquiv h e hz d v).toAdd.val).toMul : M)
    dsimp only [initialAction]
    rw [NormalElementaryQuotient.representation_apply, coverEquiv_val]
    exact congrArg d.overgroup.subtype hw
  change (initialSection h e hz).coverProjection (naturalCoordinates h e hz hn)
    (coverEquiv h e hz d w).toAdd = _
  rw [he, MovedSection.coverProjection_ambient]
  rfl

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

