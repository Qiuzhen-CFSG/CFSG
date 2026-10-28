module
public import Theory.GroupTheory.ReducedNormal.SubspaceGroupConsequences

/-!
# Irreducibility of a reduced-module seed with zero fixed kernel

An invariant subgroup pulls back through the literal reduced-module inclusion
to an invariant binary subspace. The Irr⁺ quotient dichotomy then says it
is either central or supplements the fixed kernel. When that kernel is zero,
the subgroup is trivial or the whole seed.

Source: Aschbacher–Smith, A.1.40, printed p.31; the fixed-kernel step of
5.1.17, printed p.640 (refs/quasithin.pdf).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G]

/-- A fixed-free Irr⁺ seed has no proper nontrivial invariant subgroup. -/
theorem invariant_subgroup_of_irrPlus (H X : Subgroup G) (hXH : X ≤ H)
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hi : IsIrrPlus (representation H) (X.subgroupOf H) I)
    (hz : subspaceImage H I ⊓ centralizer (X : Set G) = ⊥)
    (A : Subgroup G) (hA : A ≤ subspaceImage H I)
    (hn : X ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = subspaceImage H I := by
  obtain ⟨hs,_,hirr⟩ := hi
  let J : Submodule (ZMod 2) (Additive (ModuleGroup H)) :=
    AddSubgroup.toZModSubmodule 2
      (((A.comap H.subtype).comap (ModuleGroup H).subtype).toAddSubgroup)
  let S : Subrepresentation (invariantSubspace (representation H) (X.subgroupOf H) I hs).toRepresentation :=
    ⟨J.comap I.subtype, fun x v hv => by
      change (x.val : G) * v.val.toMul.val.val * (x.val : G)⁻¹ ∈ A
      exact (mem_normalizer_iff.mp (hn x.property) _).mp hv⟩
  let C := centralSubspace (representation H) (X.subgroupOf H) I hs
  have hC : C = ⊥ := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hz]
    exact ⟨mem_map_of_mem _ (mem_map_of_mem _ v.property),
      (mem_reduced_fixedSpace_iff H X hXH v.val).mp hv⟩
  let : Representation.IsIrreducible C.quotientRepresentation := hirr
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient C S with he | he
  · left
    apply bot_unique
    intro a ha
    obtain ⟨_,⟨v,hv,rfl⟩,rfl⟩ := hA ha
    have hm : (⟨Additive.ofMul v,hv⟩ : I) ∈ S := ha
    have hm' := he hm
    rw [hC] at hm'
    have hv0 : Additive.ofMul v = 0 := congrArg Subtype.val (show (⟨Additive.ofMul v,hv⟩ : I) = 0 from hm')
    exact congrArg (fun w : Additive (ModuleGroup H) => w.toMul.val.val) hv0
  · right
    apply le_antisymm hA
    have hC0 : C.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hC
    rw [hC0, bot_sup_eq] at he
    rintro a ⟨_,⟨v,hv,rfl⟩,rfl⟩
    have hm : (⟨Additive.ofMul v,hv⟩ : I) ∈ S := by
      change (⟨Additive.ofMul v,hv⟩ : I) ∈ S.toSubmodule
      rw [he]
      trivial
    exact hm

end Theory.GroupTheory.ReducedNormal
