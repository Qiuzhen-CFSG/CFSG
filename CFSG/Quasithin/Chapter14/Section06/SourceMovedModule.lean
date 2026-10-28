module
public import CFSG.Quasithin.Chapter14.Section06.SourcePrimitiveOddResidual
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalF918
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
/-!
# The actual moved-module reduction for the abelian plane branch

The source point has index two in the seed plane. Their T-normalization
makes the seed image in U/Z fixed by the mapped Sylow subgroup. Its actual
orbit spans U/Z, so the residual commutator space and the globally fixed
space span U/Z. This also identifies the whole-group commutator space with
the residual commutator space and proves faithfulness on that space.

This supplies the source-specific module premise for the D.2.17 application
in original 14.6.12; an arbitrary faithful module need not have this fixed
supplement. The representation and both quotients remain literal.

Source: Aschbacher--Smith, 14.6.12(2), printed p.1031, using the B.2.14
Sylow-fixed generation argument.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab



theorem source_rankTwo_seed_fixed
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)) :
    seedSpace a (localModule T M) ≤ fixedSpace a.representation (actorImage H T) := by
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
  apply (RepresentationReduction.seedSpace_le_actorImage_iff a
    (le_conjugateSpanBy _ _) hH.1.2).mpr
  have hi : (centralInvolutions T).relIndex (localModule T M) = 2 := by
    have hc := ((centralInvolutions T).subgroupOf (localModule T M)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe h.point_lt.le).toEquiv] at hc
    change Nat.card (centralInvolutions T) *
      (centralInvolutions T).relIndex (localModule T M) = Nat.card (localModule T M) at hc
    rw [h.point_card,hcard] at hc
    omega
  exact commutator_le_of_normalized_index_two _ _ _ h.point_lt.le hi
    (le_sup_right.trans h.local_normalizes) h.normalizes_point

theorem source_rankTwo_span_decomposition
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)) :
    subspaceCommutator a.representation ⊤ (pResidual 2 (H ⧸ pCore 2 H)) ⊔
      fixedSpace a.representation ⊤ = ⊤ := by
  have hh := source_span_decomposition a T hH.1.2
    (source_rankTwo_seed_fixed hG T hempty hM hu hmany hcard e hab H hH a)
  have hr : actorImage H (GenerationOne.residual H) = pResidual 2 (H ⧸ pCore 2 H) := by
    unfold actorImage GenerationOne.residual subgroupOf
    rw [comap_map_eq_self_of_injective H.subtype_injective,map_pResidual_quotient]
  rwa [hr] at hh

theorem source_rankTwo_whole_moved_eq_residual
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)) :
    subspaceCommutator a.representation ⊤ ⊤ =
      subspaceCommutator a.representation ⊤ (pResidual 2 (H ⧸ pCore 2 H)) := by
  let W := subspaceCommutator a.representation ⊤ (pResidual 2 (H ⧸ pCore 2 H))
  have hd := source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab H hH a
  have hn : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ subspaceStabilizer a.representation W :=
    subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer a.representation ⊤ (by intros; trivial)) le_normalizer_of_normal
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    obtain ⟨w,hw,c,hc,rfl⟩ := Submodule.mem_sup.mp (hd.ge (Submodule.mem_top (x := v)))
    have hgc : a.representation g c = c := hc ⟨g,mem_top _⟩
    rw [map_add,hgc,add_sub_add_right_eq_sub]
    exact W.sub_mem ((hn (mem_top _) w).2 hw) hw
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,hv,rfl⟩
    exact Submodule.subset_span ⟨g,mem_top _,v,hv,rfl⟩

theorem source_rankTwo_residual_moved_faithful
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (g : H ⧸ pCore 2 H)
    (hfix : ∀ v ∈ subspaceCommutator a.representation ⊤ (pResidual 2 (H ⧸ pCore 2 H)),
      a.representation g v = v) : g = 1 := by
  have hd := source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab H hH a
  apply a.faithful
  apply LinearMap.ext
  intro v
  obtain ⟨w,hw,c,hc,rfl⟩ := Submodule.mem_sup.mp (hd.ge (Submodule.mem_top (x := v)))
  have hgc : a.representation g c = c := hc ⟨g,mem_top _⟩
  simp only [map_one, Module.End.one_apply, map_add, hfix w hw, hgc]

end CFSG.Quasithin.Chapter14.Section06
