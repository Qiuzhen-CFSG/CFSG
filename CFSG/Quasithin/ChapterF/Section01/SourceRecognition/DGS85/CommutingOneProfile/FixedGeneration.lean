module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphSeeds
public import Theory.Representation.RankOne.QuadraticRecognition.Generation
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Corrected fixed-space generation for the actual source centers

Sylow conjugacy identifies Zδ with the orbit span of any one Sylow
omega-center. That seed lies in C_Zδ(T), giving the generation condition
required by the correction to DGS (5.12). If a normal local subgroup L
contains T, Frattini's argument removes the Sylow normalizer supplement,
so L already generates the same span. Its embedded two-core is Qδ.

The last theorem applies these facts to the literal quotient L/O₂(L) and
the actual conjugation action on Zδ. It gives the sum of the moved space
and the Sylow fixed space, and fixed-space generation on every quotient
module. The chosen model marking and action remain explicit. This does
not construct or recognize the different module Qα/Zα needed in (11.8).

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
notation for Zδ, p.81; (5.8)(a), p.109; corrected (5.12), pp.113--114;
applications in (11.3), pp.169--171, and (11.8), p.176.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- One actual Sylow omega-center generates the complete source center span. -/
theorem source_center_seed_span (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) (T : Sylow 2 (stabilizer (family P) v)) :
    conjugateSpanBy (omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype)) (stabilizer (family P) v) =
      Z (family P) v := by
  let := finite_endpoints h
  let M := stabilizer (family P) v
  let T₀ := (T : Subgroup M).map M.subtype
  apply le_antisymm
  · exact conjugateSpanBy_le
      (le_iSup (fun R : Sylow 2 M => omegaCenterIn ((R : Subgroup M).map M.subtype)) T)
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ v)).mp (Z_normal _ v))
  · apply iSup_le
    intro R
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq M T R
    have ht : ((g • T : Sylow 2 M) : Subgroup M).map M.subtype =
        T₀.map (MulAut.conj (g : G)).toMonoidHom := by
      change ((T : Subgroup M).map (MulAut.conj g).toMonoidHom).map M.subtype =
        ((T : Subgroup M).map M.subtype).map (MulAut.conj (g : G)).toMonoidHom
      rw [map_map,map_map]
      rfl
    rw [ht,←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj (g : G)).injective]
    rintro x ⟨z,hz,rfl⟩
    exact subset_closure ⟨g,g.property,z,hz,rfl⟩

/-- The original center satisfies the corrected Sylow fixed-generation condition. -/
theorem source_center_fixed_generation (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) (T : Sylow 2 (stabilizer (family P) v)) :
    conjugateSpanBy (Z (family P) v ⊓
      centralizer ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype : Set G)) (stabilizer (family P) v) =
      Z (family P) v := by
  let := finite_endpoints h
  have hseed : omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map
      (stabilizer (family P) v).subtype) ≤ Z (family P) v ⊓
      centralizer ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype : Set G) :=
    le_inf (le_iSup (fun R : Sylow 2 (stabilizer (family P) v) =>
      omegaCenterIn ((R : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype)) T)
      (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  apply le_antisymm
  · exact conjugateSpanBy_le inf_le_left
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ v)).mp (Z_normal _ v))
  · conv_lhs => rw [←source_center_seed_span h v T]
    exact conjugateSpanBy_mono hseed le_rfl

/-- A normal local subgroup containing the Sylow already generates the same fixed-point span. -/
theorem source_center_fixed_generation_normal (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) (T : Sylow 2 (stabilizer (family P) v))
    (L : Subgroup (stabilizer (family P) v)) [L.Normal] (hTL : (T : Subgroup _) ≤ L) :
    conjugateSpanBy (Z (family P) v ⊓
      centralizer ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype : Set G))
      (L.map (stabilizer (family P) v).subtype) = Z (family P) v := by
  let := finite_endpoints h
  let M := stabilizer (family P) v
  let Ω := omegaCenterIn (T : Subgroup M)
  have hspan := conjugateSpanBy_sup_of_normalizes_seed Ω L
    (normalizer (T : Set M)) (normalizer_le_normalizer_omegaCenterIn _)
    (by rw [normalizer_eq_top]; exact le_top)
  rw [sup_comm,T.normalizer_sup_eq_top' hTL] at hspan
  have hm := congrArg (fun A : Subgroup M => A.map M.subtype) hspan
  rw [map_conjugateSpanBy,map_conjugateSpanBy,←MonoidHom.range_eq_map,range_subtype] at hm
  dsimp only [Ω] at hm
  rw [NilesRankOneKernel.omegaCenterIn_map_injective _ M.subtype_injective] at hm
  have hseed : omegaCenterIn ((T : Subgroup M).map M.subtype) ≤
      Z (family P) v ⊓ centralizer ((T : Subgroup M).map M.subtype : Set G) :=
    le_inf (le_iSup (fun R : Sylow 2 M => omegaCenterIn ((R : Subgroup M).map M.subtype)) T)
      (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  apply le_antisymm
  · exact conjugateSpanBy_le inf_le_left ((map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ v)).mp (Z_normal _ v)))
  · conv_lhs => rw [←source_center_seed_span h v T,hm]
    exact conjugateSpanBy_mono hseed le_rfl

/-- The two-core of the normal local actor maps to the original vertex core. -/
theorem source_normal_local_core (v : Vertex (family P))
    (T : Sylow 2 (stabilizer (family P) v))
    (L : Subgroup (stabilizer (family P) v)) [L.Normal] (hTL : (T : Subgroup _) ≤ L) :
    (pCore 2 L).map ((stabilizer (family P) v).subtype.comp L.subtype) = Q (family P) v := by
  rw [←map_map]
  change (L.pCoreIn 2).map (stabilizer (family P) v).subtype = _
  rw [←pCore_eq_map_of_normal_of_le 2 L ((pCore_isPGroup.le_sylow_of_normal T).trans hTL)]
  rfl

open Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition

private theorem representation_generated_of_ambient_span
    {H D : Type*} [Group H] [Group D] (V : Subgroup G) [IsElementaryAbelian 2 V]
    (j : H →* G) (T : Subgroup H) (q : H →* D)
    (ρ : Representation (ZMod 2) D (Additive V))
    (hspan : conjugateSpanBy (V ⊓ centralizer (T.map j : Set G)) j.range = V)
    (hact : ∀ (g : H) (w : Additive V),
      ((ρ (q g) w).toMul : G) = j g * w.toMul * (j g)⁻¹) :
    GeneratedByFixedSpace ρ (T.map q) := by
  let A := T.map q
  let W := ⨆ d : D, (fixedSpace ρ A).map (ρ d)
  let C : Subgroup G := W.toAddSubgroup.toSubgroup.map V.subtype
  have hfixed (z : G) (hz : z ∈ V) (hc : z ∈ centralizer (T.map j : Set G)) :
      Additive.ofMul (⟨z,hz⟩ : V) ∈ fixedSpace ρ A := by
    intro a
    obtain ⟨t,ht,he⟩ := a.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ a.val (Additive.ofMul (⟨z,hz⟩ : V))).toMul : G) = z
    rw [←he,hact]
    change j t * z * (j t)⁻¹ = z
    rw [hc (j t) (mem_map_of_mem _ ht),mul_inv_cancel_right]
  have hVC : V ≤ C := by
    rw [←hspan]
    apply (closure_le _).mpr
    rintro x ⟨_,⟨g,rfl⟩,z,hz,rfl⟩
    have hw : ρ (q g) (Additive.ofMul (⟨z,hz.1⟩ : V)) ∈ W :=
      (le_iSup (fun d : D => (fixedSpace ρ A).map (ρ d)) (q g))
        ⟨_,hfixed z hz.1 hz.2,rfl⟩
    exact ⟨(ρ (q g) (Additive.ofMul (⟨z,hz.1⟩ : V))).toMul,hw,hact g _⟩
  apply top_unique
  intro w _
  obtain ⟨z,hz,he⟩ := hVC w.toMul.property
  have he' : Additive.ofMul z = w := Additive.toMul.injective (Subtype.ext he)
  exact he' ▸ hz

/-- Transport the source generation proof to the given literal conjugation coordinates. -/
theorem source_center_representation_generated
    {D : Type*} [Group D] (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) (T : Sylow 2 (stabilizer (family P) v))
    (q : stabilizer (family P) v →* D) :
    letI := source_center_elementary h v
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) v))),
      (∀ (g : stabilizer (family P) v) (w : Additive (Z (family P) v)),
        ((ρ (q g) w).toMul : G) = (g : G) * w.toMul * (g : G)⁻¹) →
      GeneratedByFixedSpace ρ ((T : Subgroup (stabilizer (family P) v)).map q) := by
  let := source_center_elementary h v
  intro ρ hact
  apply representation_generated_of_ambient_span (Z (family P) v)
    (stabilizer (family P) v).subtype T q ρ _ hact
  simpa only [range_subtype] using source_center_fixed_generation h v T

/-- The same generation result holds for the normal local actor and its actual Sylow image. -/
theorem source_center_representation_generated_normal
    {D : Type*} [Group D] (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) (T : Sylow 2 (stabilizer (family P) v))
    (L : Subgroup (stabilizer (family P) v)) [L.Normal] (hTL : (T : Subgroup _) ≤ L)
    (q : L →* D) :
    letI := source_center_elementary h v
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) v))),
      (∀ (g : L) (w : Additive (Z (family P) v)),
        ((ρ (q g) w).toMul : G) = (g.val : G) * w.toMul * (g.val : G)⁻¹) →
      GeneratedByFixedSpace ρ (((T : Subgroup (stabilizer (family P) v)).subgroupOf L).map q) := by
  let := source_center_elementary h v
  intro ρ hact
  let j := (stabilizer (family P) v).subtype.comp L.subtype
  apply representation_generated_of_ambient_span (Z (family P) v) j
    ((T : Subgroup (stabilizer (family P) v)).subgroupOf L) q ρ _ hact
  have ht : ((T : Subgroup (stabilizer (family P) v)).subgroupOf L).map j =
      (T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype := by
    rw [←map_map,map_subgroupOf_eq_of_le hTL]
  rw [ht,MonoidHom.range_comp,range_subtype]
  exact source_center_fixed_generation_normal h v T L hTL

/-- The original quotient marking gives (5.8)(a) and fixed-generation on every quotient module, with the core map retained. -/
theorem source_marked_center_module_consequences
    {D : Type*} [Group D] (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) (T : Sylow 2 (stabilizer (family P) v))
    (L : Subgroup (stabilizer (family P) v)) [L.Normal] (hTL : (T : Subgroup _) ≤ L)
    (e : (L ⧸ pCore 2 L) ≃* D) :
    letI := source_center_elementary h v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) v))),
      (∀ (g : L) (w : Additive (Z (family P) v)),
        ((ρ (q g) w).toMul : G) = (g.val : G) * w.toMul * (g.val : G)⁻¹) →
      (pCore 2 L).map ((stabilizer (family P) v).subtype.comp L.subtype) = Q (family P) v ∧
      Coinvariants.ker ρ ⊔
        fixedSpace ρ (((T : Subgroup (stabilizer (family P) v)).subgroupOf L).map q) = ⊤ ∧
      ∀ C : Subrepresentation ρ, GeneratedByFixedSpace C.quotientRepresentation
        (((T : Subgroup (stabilizer (family P) v)).subgroupOf L).map q) := by
  let := source_center_elementary h v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  dsimp only
  intro ρ hact
  have hg := source_center_representation_generated_normal h v T L hTL q ρ hact
  exact ⟨source_normal_local_core v T L hTL,
    moved_sup_fixed_eq_top ρ _ hg,fun C => generatedByFixedSpace_quotient ρ C _ hg⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
