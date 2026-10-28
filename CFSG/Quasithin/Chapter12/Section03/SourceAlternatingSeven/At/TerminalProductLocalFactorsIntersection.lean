module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsIntersection
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsFirst

/-!
# TerminalProductLocalFactorsIntersection at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductLocalFactorsIntersection`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem component_intersection_image_ne_top_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) :
    ((normalizer (L : Set G)).subgroupOf P.K).map (P.componentProjection C) ≠ ⊤ := by
  intro he
  have hk : (P.componentProjection C).ker ≤ (normalizer (L : Set G)).subgroupOf P.K := by
    rw [P.componentProjection_ker C]
    intro x hx
    exact S.hypothesis.source_sylow_normalizes_at structural
      (P.component_core_le_sylow (mem_map_of_mem P.K.subtype hx))
  have h := congrArg (comap (P.componentProjection C)) he
  rw [comap_map_eq_self hk,comap_top] at h
  apply P.residual_escape_at structural
  intro x hx
  exact show (⟨x,hx⟩ : P.K) ∈ (normalizer (L : Set G)).subgroupOf P.K from
    h.symm ▸ mem_top _

theorem component_intersection_centralizes_Z_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) :
    P.K ⊓ normalizer (L : Set G) ≤ centralizer (P.Z : Set G) := by
  obtain ⟨R,hR⟩ := P.exists_component_sylow
  apply C.natural.centralizes_seed_of_five_sylow_overgroup
    (P.componentProjection C) (P.componentProjection_surjective C)
    R (P.K ⊓ normalizer (L : Set G)) P.Z inf_le_left
  · rw [hR,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans (S.hypothesis.source_sylow_normalizes_at structural))
  · have he : (P.K ⊓ normalizer (L : Set G)).subgroupOf P.K =
        (normalizer (L : Set G)).subgroupOf P.K := by ext x; simp
    rw [he]
    exact P.component_intersection_image_ne_top_at structural C
  · rw [hR,subgroupOf_map_subtype]
    exact (show P.Z ≤ centralizer (T : Set G) from
      fun _ hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1).trans
        (centralizer_le inf_le_left)
  · exact le_rfl

theorem component_intersection_eq_centralizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) :
    P.K ⊓ normalizer (L : Set G) = P.K ⊓ centralizer (P.Z : Set G) :=
  le_antisymm (le_inf inf_le_left (P.component_intersection_centralizes_Z_at structural C))
    (inf_le_inf_left _ (omega_center_centralizer_le_at S D structural))

theorem component_intersection_residual_le_L1_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) :
    (primeToResidual 3 (P.K ⊓ normalizer (L : Set G) : Subgroup G)).map
      (P.K ⊓ normalizer (L : Set G)).subtype ≤ P.L1 := by
  rw [P.L1_eq_ambient_residual_of_component_at C structural]
  exact embedded_primeToResidual_mono 3 (P.component_intersection_centralizes_Z_at structural C)

theorem component_intersection_image_eq_borel_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) (R : Sylow 2 P.K)
    (hR : (R : Subgroup P.K) = (T : Subgroup G).subgroupOf P.K) :
    ((normalizer (L : Set G)).subgroupOf P.K).map (P.componentProjection C) =
      normalizer (R.mapSurjective (P.componentProjection_surjective C) :
        Set (alternatingGroup (Fin 5))) := by
  let q := P.componentProjection C
  let R' := R.mapSurjective (P.componentProjection_surjective C)
  let B := normalizer (R' : Set (alternatingGroup (Fin 5)))
  have hTM := S.hypothesis.source_sylow_normalizes_at structural
  have hRX : (R : Subgroup P.K) ≤ (normalizer (L : Set G)).subgroupOf P.K := by
    rw [hR]
    intro x hx
    exact hTM hx
  have hXB : ((normalizer (L : Set G)).subgroupOf P.K).map q ≤ B :=
    Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
      R' _ (map_mono hRX) (P.component_intersection_image_ne_top_at structural C)
  apply le_antisymm hXB
  let X := (B.comap q).map P.K.subtype
  have hXK : X ≤ P.K := map_subtype_le _
  have hsub : X.subgroupOf P.K = B.comap q :=
    comap_map_eq_self_of_injective P.K.subtype_injective _
  have himage : (X.subgroupOf P.K).map q = B := by
    rw [hsub,map_comap_eq_self (by
      rw [MonoidHom.range_eq_top.mpr (P.componentProjection_surjective C)]; exact le_top)]
  have hXC : X ≤ centralizer (P.Z : Set G) := by
    apply C.natural.centralizes_seed_of_five_sylow_overgroup q
      (P.componentProjection_surjective C) R X P.Z hXK
    · apply map_mono
      intro r hr
      exact R'.toSubgroup.le_normalizer (mem_map_of_mem q hr)
    · rw [himage]
      exact (Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_normalizer_isCoatom R').1
    · rw [hR,subgroupOf_map_subtype]
      exact (show P.Z ≤ centralizer (T : Set G) from
        fun _ hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1).trans
          (centralizer_le inf_le_left)
    · exact le_rfl
  have hXM := hXC.trans (omega_center_centralizer_le_at S D structural)
  rw [←himage]
  exact map_mono (fun x hx => hXM hx)

theorem component_intersection_normalized_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) :
    P.pointNormalizer ≤ normalizer (P.K ⊓ normalizer (L : Set G) : Subgroup G) :=
  (le_inf (inf_le_right.trans C.normalizes)
    ((P.pointNormalizer_le_original_at structural).trans (normalizer (L : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

