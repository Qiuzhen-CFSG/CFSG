module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.SylowAction
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Inner witnesses on the original E.6.7 block

Restrict the source Sylow subgroup to the intermediate group, apply the
proved elementary central Sylow action theorem there, and map its witnesses
back through the literal inclusion. The chosen Sylow subgroup of the block
is exactly its intersection with the original Q.

Source: Aschbacher–Smith E.6.7, printed p.246.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- The source inner-action assertion with all intermediate subgroup maps
discharged and the original ambient V retained. -/
theorem source_block_action {𝒦 : GroupClass} {T : Sylow 2 G} {M V W H L : Subgroup G}
    (h : HypothesisE61 𝒦 T M V) (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G)) (hc : HasCharacteristicTwo H)
    (hLH : L ≤ H) (hL : ChapterC.IsBlock (L.subgroupOf H)) :
    ∃ S : Sylow 2 L,
      (S : Subgroup L) = (sylowCentralizer (T : Subgroup G) V).subgroupOf L ∧
      V ≤ normalizer (L : Set G) ∧
      ∀ v ∈ V, ∃ z ∈ (omegaOneCenterAmbient (S : Subgroup L)).map L.subtype,
        ∀ l ∈ L, z*l*z⁻¹ = v*l*v⁻¹ := by
  let Q := sylowCentralizer (T : Subgroup G) V
  let : IsElementaryAbelian 2 V := h.elementary
  have hVH : V ≤ H := h.le_sylowCentralizer.trans hQH
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨P, hP⟩ := h.sylow_obstructionIntermediate hW hQH hHC
  change (P : Subgroup H).map H.subtype = Q at hP
  have hPH : (P : Subgroup H) = Q.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le hQH]
  have hVC : V ≤ centralizer (Q : Set G) :=
    le_centralizer_iff.mp (inf_le_right : Q ≤ centralizer (V : Set G))
  have hVP : V.subgroupOf H ≤ (P : Subgroup H) ⊓ centralizer (P : Set H) := by
    intro v hv
    refine ⟨?_, mem_centralizer_iff.mpr ?_⟩
    · rw [hPH]
      exact h.le_sylowCentralizer hv
    · intro p hp
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hVC hv) p (hP ▸ mem_map_of_mem H.subtype hp)
  obtain ⟨hVN, hinner⟩ := central_elementary_sylow_block_action
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hc) P (L.subgroupOf H) hL
    (V.subgroupOf H) hVP
  obtain ⟨S₀, hS₀⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) hL.subnormal
  let e := subgroupOfEquivOfLe hLH
  let S := S₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS : (S : Subgroup L) = Q.subgroupOf L := by
    change (S₀ : Subgroup (L.subgroupOf H)).map e.toMonoidHom = _
    rw [hS₀, hPH]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x, hLH x.property⟩, x.property⟩, hx, rfl⟩
  have hLi : (L.subgroupOf H).map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hZi : (omegaOneCenterAmbient (L.subgroupOf H ⊓ (P : Subgroup H))).map H.subtype =
      (omegaOneCenterAmbient (S : Subgroup L)).map L.subtype := by
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      Subgroup.map_inf _ _ H.subtype H.subtype_injective, hLi, hP,
      ← omegaOneCenterAmbient_map_injective L.subtype L.subtype_injective,
      hS, subgroupOf_map_subtype, inf_comm]
  refine ⟨S, hS, ?_, ?_⟩
  · intro v hv
    have hvH : (⟨v, hVH hv⟩ : H) ∈ V.subgroupOf H := hv
    have hh := le_normalizer_map H.subtype (mem_map_of_mem H.subtype (hVN hvH))
    rw [hLi] at hh
    exact hh
  · intro v hv
    obtain ⟨z, hz, he⟩ := hinner ⟨v, hVH hv⟩ hv
    refine ⟨z, hZi ▸ mem_map_of_mem H.subtype hz, ?_⟩
    intro l hl
    exact congrArg H.subtype (he ⟨l, hLH hl⟩ hl)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
