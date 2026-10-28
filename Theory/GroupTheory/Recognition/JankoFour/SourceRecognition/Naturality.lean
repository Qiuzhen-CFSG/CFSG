module
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.Intrinsic
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Naturality of the intrinsic type-J₄ hypotheses

An ambient group equivalence restricts to the original involution centralizer,
then to its generalized Fitting subgroup. The induced quotient equivalence
transports the full cubic projection, including its kernel of order three.
The returning conjugator is transported in the ambient group itself.

These maps let the returning-core argument apply the same source hypotheses
at an actual conjugate of the marked involution, without assuming a second
local model. Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.3), printed p.597, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
variable {G G' : Type*} [Group G] [Group G']

noncomputable def centralizerEquiv (f : G ≃* G') (z : G) :
    centralizer z ≃* centralizer (f z) :=
  { f.toEquiv.subtypeEquiv (fun x => by
      simp only [mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
      exact ⟨fun hx => by simpa only [map_mul] using congrArg f hx,
        fun hx => f.injective (by simpa only [map_mul] using hx)⟩) with
    map_mul' := fun x y => Subtype.ext (f.map_mul x y) }

theorem centralizerEquiv_apply (f : G ≃* G') (z : G) (x : centralizer z) :
    (centralizerEquiv f z x : G') = f x := rfl

theorem core_map (f : G ≃* G') (z : G) :
    (core z).map (centralizerEquiv f z).toMonoidHom = core (f z) :=
  map_generalizedFitting_equiv _

noncomputable def coreEquiv (f : G ≃* G') (z : G) : core z ≃* core (f z) :=
  ((centralizerEquiv f z).subgroupMap (core z)).trans (MulEquiv.subgroupCongr (core_map f z))

theorem ambientCore_map (f : G ≃* G') (z : G) :
    (ambientCore z).map f.toMonoidHom = ambientCore (f z) := by
  rw [ambientCore, map_map, ambientCore, ← core_map f z, map_map]
  rfl

noncomputable def coreQuotientEquiv (f : G ≃* G') (z : G) :
    (centralizer z ⧸ core z) ≃* (centralizer (f z) ⧸ core (f z)) :=
  QuotientGroup.congr _ _ (centralizerEquiv f z) (core_map f z)

variable [Finite G] [Finite G']

theorem type_map {z : G} (h : IsTypeJ4 z) (f : G ≃* G') : IsTypeJ4 (f z) := by
  refine ⟨(f.orderOf_eq z).trans h.involution,
    IsExtraspecial.of_mulEquiv (coreEquiv f z) h.extraspecial,
    (Nat.card_congr (coreEquiv f z).toEquiv).symm.trans h.core_card, ?_, ?_⟩
  · obtain ⟨e⟩ := h.cubic_quotient
    let q := coreQuotientEquiv f z
    refine ⟨⟨e.projection.comp q.symm.toMonoidHom,
      e.surjective.comp q.symm.surjective, ?_⟩⟩
    change Nat.card (e.projection.ker.comap q.symm.toMonoidHom) = 3
    exact (congrArg (fun K : Subgroup (centralizer (f z) ⧸ core (f z)) => Nat.card K)
      (map_equiv_eq_comap_symm' q e.projection.ker)).symm.trans
        ((card_map_of_injective q.injective).trans e.kernel_card)
  · apply (fusion_iff_exists_conjugator _).mpr
    obtain ⟨g, hg, hne⟩ := (fusion_iff_exists_conjugator z).mp h.fusion
    refine ⟨f g, ?_, ?_⟩
    · rw [← map_inv, ← map_mul, ← map_mul, ← ambientCore_map f z]
      exact mem_map_of_mem f.toMonoidHom hg
    · simpa only [← map_inv, ← map_mul, f.injective.ne_iff] using hne

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
