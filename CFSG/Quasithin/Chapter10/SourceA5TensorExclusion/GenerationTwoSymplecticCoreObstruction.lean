module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticMarkedPlane
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSCoreComparison
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The whole intrinsic core contains the original tensor span

The marked plane quotient and the original natural quotient force the full
module into the whole intrinsic commutator core, before block recognition.
The old residual normalizes this core; removing the Sylow supplement shows
that the original H-conjugate span also lies in it. If the core had order at
most 256, it would equal the full module, contrary to its original normalizer
and the outside residual. Thus a surviving symplectic row is non-Frattini.
The actual MS hypotheses construct positive even critical geometry, and its
distance-two critical indices are four without a further non-Frattini input.

This does not identify the whole core as a natural module or bound its order.
The distance and secondary-orbit reconstruction remain with
qt-d-tensor-sp4-plane. Source: Aschbacher--Smith 9.3.10 and the concluding
paragraph of 9.3, pp.734--735; MS93 (3.6), pp.870--871.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit
open ClassicalOrthogonal.FourPlusMatrix Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

/-- The original full module lies in the whole intrinsic core without block recognition. -/
theorem fullModule_le_blockU
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    D.fullModule ≤ (((ChapterC.blockU (pResidual 2 c.M)).map
      (pResidual 2 c.M).subtype).map c.M.subtype) := by
  obtain ⟨q,hq,hk,hm⟩ := c.exists_marked_plane_quotient eK
  obtain ⟨p,hp,hpk,he⟩ := m.exists_fullModule_natural_quotient
  let := fullModule_component_normal (D := D)
  apply source_fullModule_le_of_plane_radical L _ m.fullModule_le_component q hq hk p hp
  · rw [hpk]
    exact comap_mono (comap_mono c.tensorPlane_le_blockU)
  · exact m.original_plane_radical_image q hq
  · intro l v
    rw [hm l]
    exact he l v

/-- The literal H-span, retaining the original seed, lies in this same whole core. -/
theorem original_span_le_blockU
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    ChapterD.conjugateSpan c.H D.fullModule ≤
      (((ChapterC.blockU (pResidual 2 c.M)).map
        (pResidual 2 c.M).subtype).map c.M.subtype) := by
  let J := (pResidual 2 c.H).map c.H.subtype
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) := by
    have hn := (pResidual 2 c.H).le_normalizer_map c.H.subtype
    rw [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hn
    exact c.hstar.1.1.2.trans hn
  have hTV : (T : Subgroup G) ≤ normalizer (D.fullModule : Set G) :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  have hJK : J ≤ (pResidual 2 c.M).map c.M.subtype := by
    intro j hj
    have hjM : j ∈ c.M := (c.generated ▸ le_sup_of_le_left le_sup_right) hj
    exact mem_map_of_mem c.M.subtype
      (c.component_product.2.2.1 (show (⟨j,hjM⟩ : c.M) ∈ J.subgroupOf c.M from hj))
  rw [ChapterD.conjugateSpan, ← conjugateSpanBy_eq_iSup_conj,
    ← source_hstar_residual_sup_sylow c.hstar,
    conjugateSpanBy_sup_of_normalizes_seed _ J _ hTV hTJ]
  exact conjugateSpanBy_le (c.fullModule_le_blockU eK)
    (hJK.trans c.residual_normalizes_blockU)

/-- An outside normalizer forces the ambient whole core to be larger than the tensor module. -/
theorem blockU_ambient_card_gt
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    256 < Nat.card (((ChapterC.blockU (pResidual 2 c.M)).map
      (pResidual 2 c.M).subtype).map c.M.subtype) := by
  apply lt_of_not_ge
  intro hcard
  have heq := Subgroup.eq_of_le_of_card_ge (c.fullModule_le_blockU eK)
    (show Nat.card (((ChapterC.blockU (pResidual 2 c.M)).map
      (pResidual 2 c.M).subtype).map c.M.subtype) ≤ Nat.card D.fullModule by
        rwa [m.card_fullModule])
  have hn := c.residual_normalizes_blockU
  rw [← heq, source_fullModule_normalizer D] at hn
  exact c.residual_outside hn

/-- The perfect residual has no additional central kernel; its entire two-core is too large. -/
theorem residual_twoCore_card_gt
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    256 < Nat.card (pCore 2 (pResidual 2 c.M)) := by
  have h := c.blockU_ambient_card_gt eK
  rw [card_map_of_injective c.M.subtype_injective,
    card_map_of_injective (pResidual 2 c.M).subtype_injective,
    ← c.residual_twoCore_eq_blockU eK] at h
  exact h

/-- The complete Frattini-small source branch is impossible in the original tensor setup. -/
theorem commutatorCore_not_le_frattini_central
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    ¬ ⁅pCore 2 c.M,pResidual 2 c.M⁆ ≤
      (frattini (pCore 2 c.M)).map (pCore 2 c.M).subtype ⊔
        omegaCenterIn (pCore 2 c.M) := by
  intro hsmall
  have hcard := c.blockU_ambient_card
    (c.sp4_block_of_quotient_frattini_small eK hsmall)
  exact (Nat.lt_irrefl 256) (hcard ▸ c.blockU_ambient_card_gt eK)

/-- The whole intrinsic core escapes the actual Frattini-central layer of the overgroup. -/
theorem blockU_not_le_frattini_central
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    ¬ (ChapterC.blockU (pResidual 2 c.M)).map (pResidual 2 c.M).subtype ≤
      (frattini (pCore 2 c.M)).map (pCore 2 c.M).subtype ⊔
        omegaCenterIn (pCore 2 c.M) := by
  have h := c.commutatorCore_not_le_frattini_central eK
  rw [commutatorCore_eq_intrinsic (pResidual 2 c.M) (isPPerfect_pResidual 2)] at h
  exact h

/-- Construct the actual holomorph geometry from the original MS hypotheses. -/
theorem exists_positive_even_geometry
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∃ g : Geometry R, 0 < g.b R ∧ Even (g.b R) := by
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1
    ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
    c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  apply ChapterC.MSCentralOrbit.exists_positive_even_geometry _ hodd.isPGroup
    _ hms hodd.twoCore_le hself hfaith
  intro hr
  exact c.core_ne_bot (le_bot_iff.mp (hr ▸ hodd.twoCore_le))

/-- Apply the proved non-Frattini condition to every original distance-two critical path. -/
theorem nonfrattini_critical_indices
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {z : Vertex R}, CriticalPath R geometry (alpha R) z →
        (Q R z).relIndex (Z R (alpha R)) = 4 ∧
          (Q R (alpha R)).relIndex (Z R z) = 4 := by
  exact source_tensor_sp4_nonfrattini_critical_indices D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1
    ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
    c.component_product.2.2.2 (c.blockU_not_le_frattini_central eK)

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
