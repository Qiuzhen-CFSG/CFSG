module
public import Theory.SpecificGroups.BinaryLinear.CubicSylowGeneration
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.CubicSylowLift

/-!
# The invariant middle minimal parabolic of a binary four-cover

Inner automorphisms preserve every node of a fixed Sylow flag. Graph
 automorphisms reverse the three nodes, fixing the middle node. Its index
three and the full flag's self-normalization identify its core quotient
with S₃. The invariant lift retains the original T-normalization and
index in the ambient group above the two-core quotient.

Source: Aschbacher--Smith 15.2.21(3), printed p.1114, refs/quasithin.pdf.
The literal Kc application is SmallActionsSource.MiddleParabolic.
-/

public section
open Subgroup
namespace BinaryLinear.FourMiddleLift
open OuterCyclic InvariantNodeActions
private instance : Finite (LinearGroup 4) := Finite.of_injective
  (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective

private theorem normalizer_sylow_eq (S : Sylow 2 (LinearGroup 4)) :
    normalizer ((S : Subgroup (LinearGroup 4)) : Set (LinearGroup 4)) = S := by
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer (m := 3) S
  apply le_antisymm _ (S : Subgroup (LinearGroup 4)).le_normalizer
  intro g hg
  have he := mem_normalizer_iff_map_conj_eq.mp hg
  change (S : Subgroup (LinearGroup 4)).map (MulAut.conj g).toMonoidHom = S at he
  rw [hb,cutStabilizer_map_conj] at he
  rw [hb,mem_cutStabilizer]
  intro i _ v
  have hspace : cutSpace b i = cutSpace (b.map g) i :=
    (cutSpace_eq_of_fullFlag_le b (b.map g) Set.univ he.symm.le i (Set.mem_univ i)).symm
  rw [cutSpace_map] at hspace
  constructor
  · intro hv
    rw [hspace] at hv
    obtain ⟨w,hw,he⟩ := hv
    exact g.injective he ▸ hw
  · intro hv
    rw [hspace]
    exact ⟨v,hv,rfl⟩

/-- The middle minimal parabolic is invariant under the full Sylow stabilizer
in Aut(GL₄(2)), and its literal two-core quotient is S₃. -/
theorem exists_invariant_middle (S : Sylow 2 (LinearGroup 4)) :
    ∃ J : Subgroup (LinearGroup 4), (S : Subgroup _) ≤ J ∧
      (S : Subgroup _).relIndex J = 3 ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) ∧
      ∀ α : MulAut (LinearGroup 4), (S : Subgroup _).map α.toMonoidHom = S →
        J.map α.toMonoidHom = J := by
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer (m := 3) S
  let J := minimalParabolic b (1 : Fin 3)
  have hSJ : (S : Subgroup (LinearGroup 4)) ≤ J := by
    rw [hb]
    exact (cutStabilizer_le_iff b Set.univ {1}ᶜ).mpr (Set.subset_univ _)
  have hi : (S : Subgroup (LinearGroup 4)).relIndex J = 3 := by
    rw [hb]
    exact CubicSylowGeneration.minimalParabolic_index b 1
  refine ⟨J,hSJ,hi,?_,?_⟩
  · apply sylow_index_three_core_quotient (S.subtype hSJ) hi
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal (S.subtype hSJ))
    intro he
    have hn : ((S : Subgroup (LinearGroup 4)).subgroupOf J).Normal := by
      rw [← show pCore 2 J = (S : Subgroup (LinearGroup 4)).subgroupOf J from he]
      infer_instance
    have hle : J ≤ (S : Subgroup (LinearGroup 4)) := by
      rw [← normalizer_sylow_eq S]
      exact (normal_subgroupOf_iff_le_normalizer hSJ).mp hn
    have hh := relIndex_eq_one.mpr hle
    rw [hi] at hh
    omega
  · intro α hα
    rw [hb] at hα
    obtain ⟨g,rfl | rfl⟩ := OuterCyclic.inner_graph (Or.inl rfl) α
    · exact inner_fixes_minimalParabolic b g hα 1
    · exact graph_inner_reverses_minimalParabolic b g hα 1
/-- The actual middle-node lift in a T-normalized two-cover of GL₄(2). -/
theorem exists_middle_lift {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* LinearGroup 4) :
    ∃ E : Subgroup G, E ≤ K ∧ (T : Subgroup G) ≤ normalizer (E : Set G) ∧
      (T : Subgroup G).relIndex (E ⊔ (T : Subgroup G)) = 3 ∧
      Nonempty ((E ⧸ pCore 2 E) ≃* Equiv.Perm (Fin 3)) :=
  Subgroup.CubicSylowLift.exists_lift T K hn eK exists_invariant_middle
end BinaryLinear.FourMiddleLift
