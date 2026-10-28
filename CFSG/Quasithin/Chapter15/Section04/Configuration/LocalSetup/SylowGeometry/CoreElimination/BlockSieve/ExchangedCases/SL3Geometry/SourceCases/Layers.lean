module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Section
public import Mathlib.GroupTheory.Complement

/-!
# Literal module sections for the SL₃ source cases

A layer is an actual quotient A/B with its conjugation action, identified
with a specified linear representation. The extraction below restricts that
quotient map to the component. Its kernel is central when B centralizes the
component. No splitting of an ambient module is assumed.

Source: Aschbacher–Smith, C.1.34, printed pp.136–137; 15.4.20, p.1164.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

variable {D : Type*} [Group D]

/-- Conjugation by an element of a subgroup normalizing A. -/
def layerConjugate (L A : Subgroup D) (hn : L ≤ normalizer (A : Set D))
    (l : L) (a : A) : A :=
  ⟨l * (a : D) * (l : D)⁻¹, (mem_normalizer_iff.mp (hn l.property) a).mp a.property⟩

/-- An actual quotient, with the exact conjugation action of the component.
The transported vector-space structure is specified by the multiplicative
isomorphism with the additive group of V. -/
structure LayerModel {F V T : Type*} [Field F] [Group T]
    [AddCommGroup V] [Module F V] (L A B : Subgroup D)
    (e : (L ⧸ pCore 2 L) ≃* T) (ρ : Representation F T V) where
  lower_le : B ≤ A
  normalized : L ≤ normalizer (A : Set D)
  lower_normal : (B.subgroupOf A).Normal
  quotientIso : letI := lower_normal; (A ⧸ B.subgroupOf A) ≃* Multiplicative V
  intertwining : letI := lower_normal; ∀ (l : L) (a : A),
    Multiplicative.toAdd (quotientIso (QuotientGroup.mk' _ (layerConjugate L A normalized l a))) =
      ρ (e (QuotientGroup.mk' _ l))
        (Multiplicative.toAdd (quotientIso (QuotientGroup.mk' _ a)))

/-- The commutator in the source theorem is formed in the ambient group. -/
abbrev sourceQ (L : Subgroup D) : Subgroup D := ⁅pCore 2 D, L⁆

/-- The center of that actual subgroup, mapped into the ambient group. -/
def sourceCenter (L : Subgroup D) : Subgroup D :=
  (center (sourceQ L)).map (sourceQ L).subtype

/-- Its fixed subgroup under conjugation by the component. -/
def sourceFixed (L : Subgroup D) : Subgroup D := sourceQ L ⊓ centralizer (L : Set D)

/-- The intrinsic center maps into the source center, using the proved
comparison of the two core commutators. -/
theorem intrinsic_center_le [Finite D] (L : Subgroup D) (hL : L.IsCComponent) :
    ((center (blockU L)).map (blockU L).subtype).map L.subtype ≤ sourceCenter L := by
  rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
  have hQ : (blockU L).map L.subtype = sourceQ L := component_core_commutator_eq L hL
  have hzQ : ((z : blockU L) : D) ∈ sourceQ L := by
    rw [← hQ]
    exact mem_map_of_mem L.subtype z.property
  refine ⟨⟨z, hzQ⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro q
  have hq : (q : D) ∈ (blockU L).map L.subtype := hQ.symm ▸ q.property
  obtain ⟨u, hu, he⟩ := hq
  apply Subtype.ext
  have hh := congrArg (fun y : blockU L => ((y : L) : D))
    (mem_center_iff.mp hz ⟨u, hu⟩)
  change (u : D) * (z : D) = (z : D) * (u : D) at hh
  change (u : D) = (q : D) at he
  change (q : D) * (z : D) = (z : D) * (q : D)
  rwa [he] at hh

/-- Restrict an actual binary natural quotient to the component. -/
noncomputable def LayerModel.coreCenterSection [Finite D]
    {L A B : Subgroup D} {a : ℕ} {e : (L ⧸ pCore 2 L) ≃* Natural.Actor}
    (m : LayerModel L A B e (Natural.copies a)) (hL : L.IsCComponent)
    (hcenter : sourceCenter L ≤ A) (hfixed : B ≤ centralizer (L : Set D)) :
    CoreCenterSection L a := by
  letI := m.lower_normal
  let J := A.subgroupOf L
  have hn : J.Normal := normal_subgroupOf_of_le_normalizer m.normalized
  let f : J →* A :=
    { toFun x := ⟨x.val, x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  refine {
    quotientIso := e
    layer := J
    normal := hn
    center_le := ?_
    map := m.quotientIso.toMonoidHom.comp ((QuotientGroup.mk' _).comp f)
    intertwining := ?_
    kernel_central := ?_ }
  · intro x hx
    exact hcenter (intrinsic_center_le L hL (mem_map_of_mem L.subtype hx))
  · intro l b
    exact m.intertwining l (f b)
  · intro b hb
    have hb' : QuotientGroup.mk' (B.subgroupOf A) (f b) = 1 :=
      m.quotientIso.injective (hb.trans m.quotientIso.map_one.symm)
    have hmem : (b.val : D) ∈ B := (QuotientGroup.eq_one_iff (N := B.subgroupOf A) (f b)).mp hb'
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp (hfixed hmem) l l.property)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
