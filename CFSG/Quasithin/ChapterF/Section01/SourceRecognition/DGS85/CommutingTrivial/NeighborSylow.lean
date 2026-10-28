module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualGeneration
public import Theory.SpecificGroups.SL2.SylowInvariantSubgroup

/-!
# The neighboring core supplies the Sylow on the linear residual section

The full edge normalizes the neighboring core. Its image in a binary SL₂
local quotient is therefore normalized by the full Sylow normalizer. Core
escape makes the image nonzero, and the diagonal action forces it to be the
whole Sylow. Neighboring-core fixed generation consequently becomes genuine
Sylow-fixed generation for the same residual-section vectors and action.

The actual local quotient and its action on the section remain explicit;
this result does not recognize that quotient or construct the descent.
Source: DGS, *Groups and Graphs* (1985), 9.3, p.142, using 6.5(a), p.121,
and the fixed-space-generation correction to 5.12.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The original neighboring core maps onto the Sylow attached to this edge. -/
theorem linear_neighbor_core_sylow_image (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    let H := graphLocalGroup (family P) v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∃ T : Sylow 2 SL(2,F), ((Q (family P) w).subgroupOf H).map q = T ∧
      ∀ l : H, q l ∈ normalizer (T : Set SL(2,F)) ↔ (l : G) • w = w := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let A := (Q (family P) w).subgroupOf H
  let I := A.map q
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hQH := neighbor_core_le_localGroup h hB hS hvw
  obtain ⟨T, hT⟩ := local_quotient_neighbor_stabilizer h hB hS hvw e
  let N := normalizer (T : Set SL(2,F))
  have hIN : I ≤ N := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hT a).mpr (Q_le_stabilizer (family P) w ha)
  have hn : N ≤ normalizer (I : Set SL(2,F)) := by
    intro x hx
    obtain ⟨a, rfl⟩ := hq x
    have ha : a ∈ normalizer (A : Set H) := by
      rw [← subgroupOf_normalizer_eq hQH]
      exact stabilizer_normalizes_Q (family P) w ((hT a).mp hx)
    exact le_normalizer_map q (mem_map_of_mem q ha)
  have hneI : I ≠ ⊥ := by
    intro hbot
    apply hne
    intro x hx
    have h1 : q ⟨x, hQH hx⟩ = 1 := by
      have hm := mem_map_of_mem q (show (⟨x, hQH hx⟩ : H) ∈ A from hx)
      exact (show q ⟨x, hQH hx⟩ ∈ (⊥ : Subgroup SL(2,F)) from hbot ▸ hm)
    have hk : (⟨x, hQH hx⟩ : H) ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (h1.trans e.map_one.symm)
    exact (graphLocalGroup_core h v) ▸ mem_map_of_mem H.subtype hk
  have hp : IsPGroup 2 I := ((isPGroup_pCoreIn 2 (stabilizer (family P) w)).comap_subtype (K := H)).map q
  let : (I.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  have hIT : I ≤ T := by
    have hpN : IsPGroup 2 (I.subgroupOf N) := hp.comap_subtype
    have hh := hpN.le_sylow_of_normal (T.subtype (T : Subgroup SL(2,F)).le_normalizer)
    intro x hx
    exact hh (show (⟨x,hIN hx⟩ : N) ∈ I.subgroupOf N from hx)
  exact ⟨T, Matrix.SpecialLinearGroup.sylow_eq_of_normalized T I hIT hneI hn, hT⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Corrected Sylow-fixed generation on the unchanged residual section,
once its actual linear local quotient action is supplied. -/
theorem linear_residual_section_sylow_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    (hz : Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) v) (V (family P) v 1)
      (V (family P) v 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) v)).map
        (graphLocalGroup (family P) v).subtype : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))))) :
    let H := graphLocalGroup (family P) v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∃ T : Sylow 2 SL(2,F), ((Q (family P) w).subgroupOf H).map q = T ∧
      GeneratedByFixedSpace σ T ∧
      ∀ l : H, q l ∈ normalizer (T : Set SL(2,F)) ↔ (l : G) • w = w := by
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hg := residual_section_core_fixed_generation h hB hS hvw hz (σ.comp q) c
  have hg' := generatedByFixedSpace_of_equivariant_surjection (σ.comp q) σ q
    (LinearMap.id : W →ₗ[ZMod 2] W) Function.surjective_id (fun _ _ => rfl) _ hg
  obtain ⟨T, hT, hTf⟩ := linear_neighbor_core_sylow_image h hB hS hvw hne e
  exact ⟨T, hT, hT ▸ hg', hTf⟩

/-- The precise earlier 6.5(a) obstruction excludes a zero neighboring-core image. -/
theorem core_escape_of_intersection_obstruction
    (F₀ : Bool → Subgroup G) {v w : Vertex F₀}
    (hob : ¬ stabilizer F₀ w ≤ normalizer ((Q F₀ v ⊓ Q F₀ w : Subgroup G) : Set G)) :
    ¬ Q F₀ w ≤ Q F₀ v := by
  intro hle
  apply hob
  rw [inf_eq_right.mpr hle]
  exact stabilizer_normalizes_Q F₀ w
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
