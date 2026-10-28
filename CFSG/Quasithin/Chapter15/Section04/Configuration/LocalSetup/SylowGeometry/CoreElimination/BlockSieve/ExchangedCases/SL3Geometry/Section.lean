module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Natural
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.Actions
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Mathlib.GroupTheory.Nilpotent

/-!
# Natural sections of the center of the core commutator

For a subnormal two-perfect subgroup L, [O₂(H),L] is the image of the
intrinsic Q = [O₂(L),L]. A normal elementary H-module with kernel O₂(H)
centralizes Q, so its intersection with Q lies in Z(Q). A natural-module
map on Z(Q), with central kernel, therefore restricts to an actual central
section of this H-module. The inclusion, quotient embedding, linear map,
intertwining, central kernel and trivial upper quotient are constructed here.

The cubic calculation in `Natural` excludes such a section when the seed
centralizer is a Sylow two-subgroup. The source corollary uses precisely the
internal module already constructed from `BlockSieve.Input` and preserves
the selected component. `CoreCenterSection` is an auxiliary witness to be
constructed from each source case, not a replacement for C.1.34.

In cases (1)–(2), Q itself is the relevant center; in case (3), Z(Q) is
natural; in case (4), the natural projection of Z(Q) has central kernel.
Constructing these maps from the complete source alternatives remains the
source application's obligation, including the local/intrinsic comparison.
The other dual layers and radical inequalities need not be used by this
fixed-space calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(1)–(4),
printed pp.136–137, and the proof of 15.4.20, p.1164.
-/

@[expose] public section

open Subgroup Representation CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry

variable {H : Type*} [Group H] [Finite H]

/-- Literal conjugation in an intrinsically normal subgroup. -/
def sectionConjugate {L : Type*} [Group L] (B : Subgroup L) (hn : B.Normal)
    (l : L) (b : B) : B := ⟨l * (b : L) * l⁻¹, hn.conj_mem b b.property l⟩

/-- Auxiliary module witness on the center of the intrinsic core commutator.
It is not a C.1.34 alternative: those source cases must construct this witness. -/
structure CoreCenterSection (L : Type*) [Group L] (a : ℕ) where
  quotientIso : (L ⧸ pCore 2 L) ≃* Natural.Actor
  layer : Subgroup L
  normal : layer.Normal
  center_le : (center (blockU L)).map (blockU L).subtype ≤ layer
  map : layer →* Multiplicative (Fin a → Natural.Space)
  intertwining : ∀ (l : L) (b : layer),
    Multiplicative.toAdd (map (sectionConjugate layer normal l b)) =
      Natural.copies a (quotientIso (QuotientGroup.mk' _ l)) (Multiplicative.toAdd (map b))
  kernel_central : ∀ b : layer, map b = 1 → (b : L) ∈ center L

variable (L : Subgroup H) (hL : L.IsSubnormal) {a : ℕ} (m : CoreCenterSection L a)

/-- The model actor embeds through the actual subnormal component quotient. -/
noncomputable def sectionEmbedding : Natural.Actor →* (H ⧸ pCore 2 H) :=
  (subnormalCoreMap L hL).comp m.quotientIso.symm.toMonoidHom

theorem sectionEmbedding_injective : Function.Injective (sectionEmbedding L hL m) :=
  (subnormalCoreMap_injective L hL).comp m.quotientIso.symm.injective

@[simp] theorem sectionEmbedding_mk (l : L) :
    sectionEmbedding L hL m (m.quotientIso (QuotientGroup.mk' _ l)) =
      QuotientGroup.mk' (pCore 2 H) (l : H) := by
  simp [sectionEmbedding, subnormalCoreMap]

variable (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
variable (hc : centralizer (V : Set H) = pCore 2 H)

include hL in
/-- Subnormality and two-perfectness identify the local commutator with
the intrinsic block commutator, even when that subgroup is not abelian. -/
theorem core_commutator_eq (hp : IsPPerfect 2 L) :
    (blockU L).map L.subtype = ⁅pCore 2 H, L⁆ := by
  apply le_antisymm
  · rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    apply commutator_mono _ le_rfl
    exact (map_mono (pCore_subnormal_eq_comap 2 hL).le).trans (map_comap_le _ _)
  · apply commutator_le_core_commutator_of_isSubnormal L (pCore 2 H) hL hp pCore_isPGroup
    rw [normalizer_eq_top]
    exact le_top

/-- Intersect the model's intrinsic layer with the ambient module. -/
noncomputable def sectionIntersection : Subrepresentation ((coreAction V hc).comp (sectionEmbedding L hL m)) where
  toSubmodule := AddSubgroup.toZModSubmodule 2 ((m.layer.map L.subtype).comap V.subtype).toAddSubgroup
  apply_mem_toSubmodule g v hv := by
    obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _) g
    change ((coreAction V hc (sectionEmbedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) v).toMul : H) ∈
      m.layer.map L.subtype
    rw [sectionEmbedding_mk, coreAction_apply]
    obtain ⟨b, hb, he⟩ := hv
    exact ⟨l * b * l⁻¹, m.normal.conj_mem b hb l, by
      change (b : H) = (v.toMul : H) at he
      change (l : H) * (b : H) * (l : H)⁻¹ = _
      rw [he]⟩

/-- The intersection inclusion retains the underlying element of H. -/
noncomputable def sectionLift (w : (sectionIntersection L hL m V hc).toSubmodule) : m.layer :=
  ⟨⟨w.val.toMul, map_subtype_le _ w.property⟩, by
    obtain ⟨b, hb, he⟩ := w.property
    exact (Subtype.ext he : b = (⟨w.val.toMul, map_subtype_le _ w.property⟩ : L)) ▸ hb⟩

/-- Restrict the supplied multiplicative map and obtain a binary linear map. -/
noncomputable def naturalSectionMap : (sectionIntersection L hL m V hc).toSubmodule →ₗ[ZMod 2]
    (Fin a → Natural.Space) :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun w := Multiplicative.toAdd (m.map (sectionLift L hL m V hc w))
    map_zero' := by
      have he : sectionLift L hL m V hc 0 = 1 := rfl
      simp only [he, map_one]
      rfl
    map_add' x y := by
      have he : sectionLift L hL m V hc (x + y) =
          sectionLift L hL m V hc x * sectionLift L hL m V hc y := rfl
      simp only [he, map_mul]
      rfl }

theorem sectionLift_action (l : L) (w : (sectionIntersection L hL m V hc).toSubmodule) :
    sectionLift L hL m V hc ((sectionIntersection L hL m V hc).toRepresentation
      (m.quotientIso (QuotientGroup.mk' _ l)) w) =
      sectionConjugate m.layer m.normal l (sectionLift L hL m V hc w) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((coreAction V hc (sectionEmbedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) w.val).toMul : H) = _
  rw [sectionEmbedding_mk, coreAction_apply]
  rfl

theorem naturalSectionMap_equivariant (g : Natural.Actor)
    (w : (sectionIntersection L hL m V hc).toSubmodule) :
    naturalSectionMap L hL m V hc ((sectionIntersection L hL m V hc).toRepresentation g w) =
      Natural.copies a g (naturalSectionMap L hL m V hc w) := by
  obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _) g
  change Multiplicative.toAdd (m.map (sectionLift L hL m V hc
    ((sectionIntersection L hL m V hc).toRepresentation _ w))) = _
  dsimp only [Function.comp_apply]
  rw [sectionLift_action, m.intertwining]
  rfl

theorem naturalSectionMap_kernel_fixed (g : Natural.Actor)
    (w : (sectionIntersection L hL m V hc).toSubmodule)
    (hw : naturalSectionMap L hL m V hc w = 0) :
    (sectionIntersection L hL m V hc).toRepresentation g w = w := by
  have hq : m.map (sectionLift L hL m V hc w) = 1 := hw
  have hz := m.kernel_central _ hq
  obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _) g
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((coreAction V hc (sectionEmbedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) w.val).toMul : H) = _
  rw [sectionEmbedding_mk, coreAction_apply]
  have he := congrArg (fun x : L => (x : H)) (mem_center_iff.mp hz l)
  change (l : H) * (w.val.toMul : H) = (w.val.toMul : H) * (l : H) at he
  rw [he, mul_inv_cancel_right]

omit [V.Normal] [IsElementaryAbelian 2 V] in
include hL hc in
/-- The intersection with the core commutator lies in its center: the
ambient module centralizes the ambient core, which contains O₂(L). -/
theorem core_intersection_le_center :
    V ⊓ (blockU L).map L.subtype ≤ ((center (blockU L)).map (blockU L).subtype).map L.subtype := by
  rintro v ⟨hv, u, hu, rfl⟩
  refine ⟨u, ⟨⟨u, hu⟩, ?_, rfl⟩, rfl⟩
  apply mem_center_iff.mpr
  intro b
  apply Subtype.ext
  apply Subtype.ext
  have hb : (b.val : H) ∈ pCore 2 H := by
    have hh := (pCore_subnormal_eq_comap 2 hL).le (blockU_le_core b.property)
    exact hh
  rw [← hc] at hb
  exact (mem_centralizer_iff.mp hb u hv).symm

/-- Every displacement lies in the constructed intersection; the upper
quotient is trivial without any splitting assumption. -/
theorem naturalSection_quotient_trivial (hp : IsPPerfect 2 L)
    (g : Natural.Actor) (v : Additive V) :
    coreAction V hc (sectionEmbedding L hL m g) v - v ∈ sectionIntersection L hL m V hc := by
  obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _) g
  let w := coreAction V hc (sectionEmbedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) v - v
  have hwQ : (w.toMul : H) ∈ (blockU L).map L.subtype := by
    dsimp only [w]
    simp only [toMul_sub, div_eq_mul_inv]
    change ((coreAction V hc (sectionEmbedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) v).toMul : H) *
      (v.toMul : H)⁻¹ ∈ (blockU L).map L.subtype
    rw [sectionEmbedding_mk, coreAction_apply]
    have hn : L ≤ normalizer (V : Set H) := by rw [normalizer_eq_top]; exact le_top
    apply commutator_le_core_commutator_of_isSubnormal L V hL hp
      (IsElementaryAbelian.isPGroup 2 V) hn
    rw [commutator_comm V L]
    exact commutator_mem_commutator l.property v.toMul.property
  exact (map_mono m.center_le) (core_intersection_le_center L hL V hc ⟨w.toMul.property, hwQ⟩)

include hL m hc in
/-- A natural center section contradicts the Sylow seed centralizer. -/
theorem not_coreCenterSection (Z : Subgroup H) (hZV : Z ≤ V)
    (P : Sylow 2 H) (hCZ : centralizer (Z : Set H) = (P : Subgroup H))
    (hp : IsPPerfect 2 L) : False := by
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  obtain ⟨g, hg, _, hfix⟩ := Natural.centralSection_enlargement (coreAction V hc)
    (sectionEmbedding L hL m) (sectionEmbedding_injective L hL m) a
    (sectionIntersection L hL m V hc) (naturalSectionMap L hL m V hc)
    (naturalSectionMap_equivariant L hL m V hc)
    (naturalSectionMap_kernel_fixed L hL m V hc)
    (naturalSection_quotient_trivial L hL m V hc hp) S
  exact no_fixedSpace_enlargement V Z hc hZV P hCZ g hg hfix

private theorem perfect_twoPerfect {B : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] : IsPPerfect 2 B := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (B ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (B ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro b _
  exact (QuotientGroup.eq_one_iff b).mp (Subsingleton.elim _ _)

/-- C-components are perfect, so their intrinsic and external commutators agree. -/
theorem component_core_commutator_eq (L : Subgroup H) (hL : L.IsCComponent) :
    (blockU L).map L.subtype = ⁅pCore 2 H, L⁆ := by
  let := hL.perfect
  exact core_commutator_eq L hL.subnormal perfect_twoPerfect

variable {G : Type*} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

/-- The source's faithful internal module excludes the constructed section
for the same selected component, with no assertion about the local omega module. -/
theorem not_source_coreCenterSection (h : Input d i j H U K)
    (s : Selected H U K K₁ r) {a : ℕ}
    (m : CoreCenterSection (K₁.subgroupOf H) a) : False := by
  let V := TwoFactors.FFBranch.moduleClosure (d.Z.subgroupOf H)
  let := h.module_properties.1
  let := s.component.2.perfect
  exact not_coreCenterSection (K₁.subgroupOf H) s.relative_subnormal m V
    h.module_properties.2.2.2 (d.Z.subgroupOf H) (fun _ hz => le_normalClosure hz)
    h.placed.sylow h.seed_inputs.2.2.1 perfect_twoPerfect

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
