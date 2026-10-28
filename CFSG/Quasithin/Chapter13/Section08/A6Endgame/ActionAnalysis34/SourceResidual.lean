module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.MarkedCores
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients

/-!
# Residual and core markings for the actual source quotient

The source subgroup L₁ is the embedded two-residual of H∩M. Residuals
commute with the literal quotient H → H/O₂(H), and the two-group kernel
also preserves parabolic two-cores. Transport through the same actor
equivalence as the natural and syntheme actions identifies O₂(L₁*) with
D₀. For the alternating restriction we use its subtype injection into S₆,
not the outer-related duad action.

The case-two placement in 13.8.8 is Vα ≤ O₂(L₁T), with L₁T=H∩M.
Thus its image lies in D (respectively the intrinsic D₀) directly. These
identities supply the core and radical premises used by `lemma_13_8_34`.
The canonical residual-core calculation is reused from `MarkedCores`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.7.3(9), 13.8.8(2) and 13.8.34, printed pp.936,949,968.
-/

public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.SixLetterRadicalDisplacement.PermutationQuotients
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.SourceResidual
open ComponentSieve.SixAndG2.NaturalSix
variable {G : Type*} [Group G] [Finite G]

/-- The embedded two-residual commutes with the literal star quotient.
The containment keeps `subgroupOf` from introducing an extra intersection. -/
theorem star_residual (H J : Subgroup G) (hJ : J ≤ H) :
    Source.starImage H ((pResidual 2 J).map J.subtype) =
      (pResidual 2 (Source.starImage H J)).map (Source.starImage H J).subtype := by
  have he : ((pResidual 2 J).map J.subtype).subgroupOf H =
      (pResidual 2 (J.subgroupOf H)).map (J.subgroupOf H).subtype := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hJ),
      map_embedded_pResidual, map_subgroupOf_eq_of_le hJ]
  change (((pResidual 2 J).map J.subtype).subgroupOf H).map _ = _
  rw [he, map_embedded_pResidual]
  rfl

/-- Source O²(H∩M) has relative two-core D₀ under the same symmetric
actor equivalence that marks the source plane parabolic. -/
theorem symmetric_core (H M L₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 ↥(H ⊓ M)).map (H ⊓ M).subtype)
    (e : Source.Hstar H ≃* S)
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = H2) :
    ((Source.starImage H L₁).pCoreIn 2).map e.toMonoidHom = D0 := by
  have he : (Source.starImage H L₁).map e.toMonoidHom = Marked.residual := by
    rw [hres, star_residual H _ inf_le_left, map_embedded_pResidual, hmark]
    rfl
  rw [map_pCoreIn_of_injective 2 _ _ e.injective, he,
    ActionAnalysis33.ChiefModels.residual_core_eq_D0]

/-- The alternating source residual has the intrinsic even radical as
its relative two-core. Its ambient image is computed through the subtype
injection, without applying an outer automorphism. -/
theorem alternating_core (H M L₁ : Subgroup G)
    (hres : L₁ = (pResidual 2 ↥(H ⊓ M)).map (H ⊓ M).subtype)
    (e : Source.Hstar H ≃* alternatingGroup (Fin 6))
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = a6SynthemeStabilizer) :
    ((Source.starImage H L₁).pCoreIn 2).map e.toMonoidHom = alternatingRadical := by
  have hp : a6SynthemeStabilizer.map (alternatingGroup (Fin 6)).subtype = L2 := by
    rw [a6SynthemeStabilizer, map_comap_eq, range_subtype, inf_comm]
    rfl
  have hr : ((Source.starImage H L₁).map e.toMonoidHom).map
      (alternatingGroup (Fin 6)).subtype = Marked.residual := by
    rw [hres, star_residual H _ inf_le_left, map_embedded_pResidual, hmark,
      map_embedded_pResidual, hp, Marked.residual_L2]
  have hc : (((Source.starImage H L₁).pCoreIn 2).map e.toMonoidHom).map
      (alternatingGroup (Fin 6)).subtype = D0 := by
    rw [map_pCoreIn_of_injective 2 _ _ e.injective,
      map_pCoreIn_of_injective 2 _ _ Subtype.val_injective, hr,
      ActionAnalysis33.ChiefModels.residual_core_eq_D0]
  ext x
  rw [mem_alternatingRadical]
  constructor
  · intro hx
    rw [← hc]
    exact mem_map_of_mem _ hx
  · intro hx
    rw [← hc] at hx
    obtain ⟨y, hy, he⟩ := hx
    have he' : y = x := Subtype.ext he
    rwa [he'] at hy
end CFSG.Quasithin.Chapter13.Section08.A6Endgame.SourceResidual

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.SourceResidual
open ComponentSieve.SixAndG2.NaturalSix
variable {G : Type*} [Group G] [Finite G]

/-- The star map preserves the local two-core: its actual kernel is a
two-group. No normality of J in the ambient group is needed. -/
theorem star_core (H J : Subgroup G) (hJ : J ≤ H) :
    Source.starImage H (J.pCoreIn 2) = (Source.starImage H J).pCoreIn 2 := by
  have he : (J.pCoreIn 2).subgroupOf H = (J.subgroupOf H).pCoreIn 2 := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 J).trans hJ),
      map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hJ]
  change ((J.pCoreIn 2).subgroupOf H).map _ = _
  rw [he]
  exact map_pCoreIn_of_ker_isPGroup (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) (J.subgroupOf H)

/-- The source parabolic two-core maps to D in the symmetric marking. -/
theorem symmetric_parabolic_core (H M : Subgroup G) (e : Source.Hstar H ≃* S)
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = H2) :
    (Source.starImage H ((H ⊓ M).pCoreIn 2)).map e.toMonoidHom = D := by
  rw [star_core H _ inf_le_left, map_pCoreIn_of_injective 2 _ _ e.injective,
    hmark, H2_core_eq_D]

private theorem alternating_plane_core : L2.pCoreIn 2 = D0 := by
  have hn : H2 ≤ normalizer (L2 : Set S) := by
    apply le_trans (le_inf H2.le_normalizer (show H2 ≤ normalizer (alternatingGroup (Fin 6) : Set S) by
      rw [normalizer_eq_top]; exact le_top))
    exact inf_normalizer_le_normalizer_inf
  apply le_antisymm
  · have hd := pCoreIn_mono_of_normalizes (p := 2) (show L2 ≤ H2 from inf_le_left) hn
    rw [H2_core_eq_D] at hd
    exact le_inf hd ((pCoreIn_le 2 L2).trans inf_le_right)
  · exact le_pCoreIn_of_normalizes (D_isPGroup.to_le inf_le_left) D0_le_L2
      ((show L2 ≤ H2 from inf_le_left).trans H2_normalizes_D0)

/-- The source parabolic two-core maps to the intrinsic even radical
in the alternating marking. -/
theorem alternating_parabolic_core (H M : Subgroup G)
    (e : Source.Hstar H ≃* alternatingGroup (Fin 6))
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = a6SynthemeStabilizer) :
    (Source.starImage H ((H ⊓ M).pCoreIn 2)).map e.toMonoidHom = alternatingRadical := by
  have hp : a6SynthemeStabilizer.map (alternatingGroup (Fin 6)).subtype = L2 := by
    rw [a6SynthemeStabilizer, map_comap_eq, range_subtype, inf_comm]
    rfl
  have hc : ((Source.starImage H ((H ⊓ M).pCoreIn 2)).map e.toMonoidHom).map
      (alternatingGroup (Fin 6)).subtype = D0 := by
    rw [star_core H _ inf_le_left, map_pCoreIn_of_injective 2 _ _ e.injective,
      hmark, map_pCoreIn_of_injective 2 _ _ Subtype.val_injective,
      hp, alternating_plane_core]
  ext x
  rw [mem_alternatingRadical]
  constructor
  · intro hx
    rw [← hc]
    exact mem_map_of_mem _ hx
  · intro hx
    rw [← hc] at hx
    obtain ⟨y, hy, he⟩ := hx
    have he' : y = x := Subtype.ext he
    rwa [he'] at hy
end CFSG.Quasithin.Chapter13.Section08.A6Endgame.SourceResidual
