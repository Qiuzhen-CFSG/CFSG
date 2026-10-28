module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.Preparation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Place the selected component in the actual offender actor

Inside the original plus actor, W_K is a normal elementary abelian subgroup.
The source containment W_K ≤ T_v lets maximum elementary subgroups of T_v
supply best offenders. Their images generate J(T_v)⁺, so the transported Y_z
commutator relation puts K⁺ in the best-offender subgroup. Restricting the
subnormal chain and transporting quasisimplicity retains K⁺ as a component
of this precise actor and excludes the trivial B.5.6 alternative.

The auxiliary internal subgroup is identified with the original W_K by a
binary linear equivalence commuting with conjugation. Thus all offender
claims concern the published representation, with its original kernel.
The containment W_K ≤ T_v follows in the source setup from W_K ≤ U_v ≤ O₂(G_v)
and the chosen Sylow subgroup. It remains explicit here for source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.5,
printed p.76, and the paragraph preceding 13.6.14, p.929.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
open ComponentSelection ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

private abbrev internalModule := (WK K L T z v).subgroupOf (plusActor K L T v)

omit [IsElementaryAbelian 2 (WK K L T z v)] in
include hL hz in
private theorem internalModule_normal : (internalModule K L T z v).Normal :=
  normal_subgroupOf_of_le_normalizer (plusActor_normalizes_WK K L T z v hL hz)

private instance internalModule_elementary : IsElementaryAbelian 2 (internalModule K L T z v) where
  toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative (H := WK K L T z v)
    (K := plusActor K L T v)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := WK K L T z v) _ x.property

variable (hW : WK K L T z v ≤ Tv T v)
include hW

omit [IsElementaryAbelian 2 (WK K L T z v)] in
private theorem internalModule_kernel :
    (plusMk K L T z v hL hz).ker =
      centralizer (internalModule K L T z v : Set (plusActor K L T v)) := by
  rw [plusMk_ker]
  ext x
  constructor
  · intro hx
    apply mem_centralizer_iff.mpr
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp hx y hy)
  · intro hx
    apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx
      ⟨y, (hW.trans le_sup_right) hy⟩ hy)

private def internalRepresentation :=
  let := internalModule_normal K L T z v hL hz
  NormalElementaryQuotient.representation (internalModule K L T z v)
    (plusMk K L T z v hL hz) (QuotientGroup.mk'_surjective _)
      (internalModule_kernel K L T z v hL hz hW)

private def internalCoordinates : Additive (internalModule K L T z v) ≃ₗ[ZMod 2]
    Additive (WK K L T z v) :=
  LinearEquiv.ofBijective
    ((subgroupOfEquivOfLe (show WK K L T z v ≤ plusActor K L T v from
      hW.trans le_sup_right)).toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe (hW.trans le_sup_right)).bijective

private theorem internalCoordinates_intertwines (a : Gplus K L T z v hL hz)
    (w : Additive (internalModule K L T z v)) :
    internalCoordinates K L T z v hW (internalRepresentation K L T z v hL hz hW a w) =
      representation K L T z v hL hz a (internalCoordinates K L T z v hW w) := by
  let := internalModule_normal K L T z v hL hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (plusConjugation K L T z v hL hz).ker a
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun a : plusActor K L T v => (a : G)) (NormalElementaryQuotient.representation_apply
    (internalModule K L T z v) (plusMk K L T z v hL hz) (QuotientGroup.mk'_surjective _)
      (internalModule_kernel K L T z v hL hz hW) x w)

private theorem internal_weight (A : Subgroup (Gplus K L T z v hL hz)) :
    weight (internalRepresentation K L T z v hL hz hW) A =
      weight (representation K L T z v hL hz) A := by
  have hf := fixedSpace_map_equivariant
    (internalRepresentation K L T z v hL hz hW) (representation K L T z v hL hz)
    (MonoidHom.id _) (internalCoordinates K L T z v hW)
    (internalCoordinates_intertwines K L T z v hL hz hW) A
  rw [Subgroup.map_id] at hf
  unfold weight
  rw [← hf, LinearEquiv.finrank_map_eq]

/-- Maximum elementary images are best offenders on the published W_K action. -/
theorem maximum_image_best [Finite G] (A : Subgroup (plusActor K L T v))
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups ((Tv T v).subgroupOf (plusActor K L T v)))
    (hne : A.map (plusMk K L T z v hL hz) ≠ ⊥) :
    IsBestOffender (representation K L T z v hL hz) (A.map (plusMk K L T z v hL hz)) := by
  let := internalModule_normal K L T z v hL hz
  have hbest := Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
    (internalModule K L T z v) (plusMk K L T z v hL hz) (QuotientGroup.mk'_surjective _)
      (internalModule_kernel K L T z v hL hz hW)
      ((Tv T v).subgroupOf (plusActor K L T v)) A (comap_mono hW) hA hne
  refine ⟨hbest.1, ?_⟩
  intro B hB
  rw [← internal_weight K L T z v hL hz hW,
    ← internal_weight K L T z v hL hz hW]
  exact hbest.2 B hB

/-- The full Thompson image is contained; no ambient offender-generation
assertion is inferred from the existence of one offender. -/
theorem thompson_le_offenderActor [Finite G] :
    plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤
      offenderActor K L T z v hL hz := by
  have he : (Stellmacher.elementaryAbelianMaxJ (Tv T v)).subgroupOf (plusActor K L T v) =
      Stellmacher.elementaryAbelianMaxJ ((Tv T v).subgroupOf (plusActor K L T v)) := by
    apply map_injective (plusActor K L T v).subtype_injective
    rw [map_subgroupOf_eq_of_le
      ((show Stellmacher.elementaryAbelianMaxJ (Tv T v) ≤ Tv T v from
        sSup_le fun _ h => h.1).trans (show Tv T v ≤ plusActor K L T v from le_sup_right)),
      ← Stellmacher.elementaryAbelianMaxJ_map_injective _ Subtype.val_injective,
      map_subgroupOf_eq_of_le (show Tv T v ≤ plusActor K L T v from le_sup_right)]
  change ((Stellmacher.elementaryAbelianMaxJ (Tv T v)).subgroupOf _).map _ ≤ _
  rw [he]
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hzA : A.map (plusMk K L T z v hL hz) = ⊥
  · rw [hzA]; exact bot_le
  exact (maximum_image_best K L T z v hL hz hW A hA hzA).le_offenderSubgroup _

/-- Source Y_z and W_K ≤ T_v put the actual component in the classified actor. -/
theorem component_contained [Finite G] (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    plusImage K L T z v hL hz K ≤ offenderActor K L T z v hL hz :=
  component_le_offenderActor K L T z v hL hz hK hn
    (thompson_le_offenderActor K L T z v hL hz hW)


/-- The component is retained as a literal subgroup of the classified actor. -/
def componentInOffender : Subgroup (offenderActor K L T z v hL hz) :=
  (plusImage K L T z v hL hz K).subgroupOf (offenderActor K L T z v hL hz)

/-- Forgetting the nested subtype gives the original K⁺, not an abstract copy. -/
def componentEquiv [Finite G] (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    componentInOffender K L T z v hL hz ≃* plusImage K L T z v hL hz K :=
  subgroupOfEquivOfLe (component_contained K L T z v hL hz hW hK hn)

/-- The R₂ condition supplies quasisimplicity inside the appropriate actor. -/
theorem component_isComponent [Finite G] (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    Theory.GroupTheory.IsComponent (offenderActor K L T z v hL hz)
      (componentInOffender K L T z v hL hz) := by
  have hC : Theory.GroupTheory.IsComponent (Gplus K L T z v hL hz)
      (plusImage K L T z v hL hz K) :=
    ⟨plusImage_K_subnormal K L T z v hL hz hK,
      plusImage_K_quasisimple K L T z v hL hz hK hR⟩
  exact hC.subgroupOf (component_contained K L T z v hL hz hW hK hn)

/-- Membership in Y_z rules out the trivial B.5 alternative through the actual
component containment, rather than through an assumed ambient FF-generation. -/
theorem classify_nontrivial_offenderActor [Finite G] {𝒦 : GroupClass.{u}}
    (classification : AdequateClassificationInput.{u,u} 𝒦)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hSQ : IsSQTK 𝒦 (plusActor K L T v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    NontrivialAdequateAlternative (offenderRepresentation K L T z v hL hz) := by
  have hne : offenderActor K L T z v hL hz ≠ ⊥ := by
    intro hb
    have hc := component_contained K L T z v hL hz hW hK hn
    rw [hb] at hc
    exact plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK (bot_unique hc)
  let : Nontrivial (offenderActor K L T z v hL hz) :=
    (nontrivial_iff_ne_bot _).mpr hne
  exact (classify_offenderActor K L T z v hL hz classification hSQ hR).of_nontrivial _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
