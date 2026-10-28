module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsFirst
public import Theory.Representation.BinaryAlternatingFiveSylowSeed
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The actual component intersection in the terminal A₇ argument

The normal A₅ component meets the original Sylow subgroup in an intrinsic
Sylow subgroup. Its two-core lies there, so the escaping intersection with
N_G(L) has proper image in the supplied A₅ quotient. Sylow-fixed seed
splitting shows that this whole intersection fixes Z. Applying the same
argument to the full Borel preimage identifies its image with the original
Sylow normalizer. All quotient maps and ambient embeddings are retained.

The prime-to-three residual consequently lies in the literal L₁. The reverse
containment is proved in TerminalProductLocalFactorsIntersectionResidual.
The second factor identification remains with qt-d-1231-terminal-product; ComponentAnalysis is discharged by the terminal
assembly owner qt-d-1231-terminal.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.811.
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

def componentProjection (C : P.ComponentAnalysis) : P.K →* alternatingGroup (Fin 5) :=
  C.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.K))

theorem componentProjection_surjective (C : P.ComponentAnalysis) :
    Function.Surjective (P.componentProjection C) :=
  C.quotient.surjective.comp (QuotientGroup.mk'_surjective _)

theorem componentProjection_ker (C : P.ComponentAnalysis) :
    (P.componentProjection C).ker = pCore 2 P.K := by
  ext x
  change C.quotient (QuotientGroup.mk' (pCore 2 P.K) x) = 1 ↔ x ∈ pCore 2 P.K
  rw [map_eq_one_iff C.quotient C.quotient.injective]
  exact QuotientGroup.eq_one_iff x

theorem exists_component_sylow :
    ∃ R : Sylow 2 P.K, (R : Subgroup P.K) = (T : Subgroup G).subgroupOf P.K := by
  let W := P.K ⊔ (T : Subgroup G)
  have hKW : P.K ≤ W := le_sup_left
  let : (P.K.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le P.K.le_normalizer P.sylow_normalizes_residual)
  obtain ⟨R,hR⟩ := (T.subtype (show (T : Subgroup G) ≤ W from le_sup_right)).exists_subgroupOf_eq_of_normal
    (P.K.subgroupOf W)
  let e := subgroupOfEquivOfLe hKW
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (R : Subgroup _).map e.toMonoidHom = _
  rw [hR]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x,hKW x.property⟩,x.property⟩,hx,rfl⟩

theorem component_core_le_sylow : P.K.pCoreIn 2 ≤ (T : Subgroup G) := by
  obtain ⟨R,hR⟩ := P.exists_component_sylow
  have h := pCoreIn_le_sylow P.K R
  rw [hR,subgroupOf_map_subtype] at h
  exact h.trans inf_le_left

theorem component_intersection_image_ne_top
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) :
    ((normalizer (L : Set G)).subgroupOf P.K).map (P.componentProjection C) ≠ ⊤ := by
  intro he
  have hk : (P.componentProjection C).ker ≤ (normalizer (L : Set G)).subgroupOf P.K := by
    rw [P.componentProjection_ker C]
    intro x hx
    exact S.hypothesis.source_sylow_normalizes structural
      (P.component_core_le_sylow (mem_map_of_mem P.K.subtype hx))
  have h := congrArg (comap (P.componentProjection C)) he
  rw [comap_map_eq_self hk,comap_top] at h
  apply P.residual_escape structural
  intro x hx
  exact show (⟨x,hx⟩ : P.K) ∈ (normalizer (L : Set G)).subgroupOf P.K from
    h.symm ▸ mem_top _

theorem component_intersection_centralizes_Z
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) :
    P.K ⊓ normalizer (L : Set G) ≤ centralizer (P.Z : Set G) := by
  obtain ⟨R,hR⟩ := P.exists_component_sylow
  apply C.natural.centralizes_seed_of_five_sylow_overgroup
    (P.componentProjection C) (P.componentProjection_surjective C)
    R (P.K ⊓ normalizer (L : Set G)) P.Z inf_le_left
  · rw [hR,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans (S.hypothesis.source_sylow_normalizes structural))
  · have he : (P.K ⊓ normalizer (L : Set G)).subgroupOf P.K =
        (normalizer (L : Set G)).subgroupOf P.K := by ext x; simp
    rw [he]
    exact P.component_intersection_image_ne_top structural C
  · rw [hR,subgroupOf_map_subtype]
    exact (show P.Z ≤ centralizer (T : Set G) from
      fun _ hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1).trans
        (centralizer_le inf_le_left)
  · exact le_rfl

theorem component_intersection_eq_centralizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) :
    P.K ⊓ normalizer (L : Set G) = P.K ⊓ centralizer (P.Z : Set G) :=
  le_antisymm (le_inf inf_le_left (P.component_intersection_centralizes_Z structural C))
    (inf_le_inf_left _ (omega_center_centralizer_le S D structural))

theorem component_intersection_residual_le_L1
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) :
    (primeToResidual 3 (P.K ⊓ normalizer (L : Set G) : Subgroup G)).map
      (P.K ⊓ normalizer (L : Set G)).subtype ≤ P.L1 := by
  rw [P.L1_eq_ambient_residual_of_component C structural]
  exact embedded_primeToResidual_mono 3 (P.component_intersection_centralizes_Z structural C)

theorem component_intersection_image_eq_borel
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) (R : Sylow 2 P.K)
    (hR : (R : Subgroup P.K) = (T : Subgroup G).subgroupOf P.K) :
    ((normalizer (L : Set G)).subgroupOf P.K).map (P.componentProjection C) =
      normalizer (R.mapSurjective (P.componentProjection_surjective C) :
        Set (alternatingGroup (Fin 5))) := by
  let q := P.componentProjection C
  let R' := R.mapSurjective (P.componentProjection_surjective C)
  let B := normalizer (R' : Set (alternatingGroup (Fin 5)))
  have hTM := S.hypothesis.source_sylow_normalizes structural
  have hRX : (R : Subgroup P.K) ≤ (normalizer (L : Set G)).subgroupOf P.K := by
    rw [hR]
    intro x hx
    exact hTM hx
  have hXB : ((normalizer (L : Set G)).subgroupOf P.K).map q ≤ B :=
    Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
      R' _ (map_mono hRX) (P.component_intersection_image_ne_top structural C)
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
  have hXM := hXC.trans (omega_center_centralizer_le S D structural)
  rw [←himage]
  exact map_mono (fun x hx => hXM hx)

theorem component_intersection_normalized
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) :
    P.pointNormalizer ≤ normalizer (P.K ⊓ normalizer (L : Set G) : Subgroup G) :=
  (le_inf (inf_le_right.trans C.normalizes)
    ((P.pointNormalizer_le_original structural).trans (normalizer (L : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf


end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
