module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.FactorMarking
public import Theory.Representation.BinaryPermutation.FivePairMoved
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Natural coordinates on the selected alternating-five support

The two class-sum sections split the same marked symmetric-five quotient.
Their first image is exactly the original commutator with the selected A5
component, because its literal quotient image is the first alternating axis.
The resulting coordinates retain conjugation by every element in the original
paired actor, including the prescribed Thompson and Baumann subgroups.

Source: Aschbacher–Smith B.6.9 and C.1.23–28, pp.115–116,129–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction BinaryPermutation
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
/-- Same-factor coordinates on the literal selected component's moved subgroup. -/
theorem first_five_moved_coordinates
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (L : Subgroup G)
    (hL : L.map q = (alternatingGroup (Fin 5)).map
      (SymmetricFive.Paired.leftFactorMap
        (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)) c.action.groupEquiv)) :
    let W := (⁅U,L⁆ : Subgroup G)
    letI : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U L)
    ∃ f : Additive W ≃ₗ[ZMod 2] core (Fin 5),
      (∀ v : Additive W, c.symmetricCoreMap
        (Additive.ofMul (⟨v.toMul,(commutator_le_left U L) v.toMul.property⟩ : U)) = (f v,0)) ∧
      (∀ (g : G) (hg : q g ∈ offenderSubgroup (NormalElementaryQuotient.representation U q hq hk))
          (v : Additive W) (hgv : g*(v.toMul:G)*g⁻¹ ∈ W),
        f (Additive.ofMul ⟨g*(v.toMul:G)*g⁻¹,hgv⟩) =
          coreRepresentation (Fin 5) (c.action.groupEquiv ⟨q g,hg⟩).1 (f v)) := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  let σ := α.comp j
  have he (g : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) (v : Additive U) :
      c.symmetricCoreMap (σ g v) = FivePair.action g (c.symmetricCoreMap v) := by
    simpa only [σ,j,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply]
      using c.symmetricCoreMap_action (c.action.groupEquiv.symm g) v
  have hz (v : Additive U) (hv : c.symmetricCoreMap v = 0) (g : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) :
      σ g v = v := by
    have hh : v ∈ Representation.invariants (α.comp Y.subtype) := c.symmetricCoreMap_ker ▸ hv
    exact hh (c.action.groupEquiv.symm g)
  obtain ⟨s₁,s₂,h₁,h₂,he₁,he₂,hr₁,hr₂⟩ := FivePair.exists_moved_sections σ c.symmetricCoreMap
    c.symmetricCoreMap_surjective he hz
  have hm : s₁.range = NormalElementaryQuotient.commutatorSpace U L := by
    rw [hr₁,NormalElementaryQuotient.commutatorSpace_eq U q hq hk L,hL]
    have hh := subspaceCommutator_map_embedding σ α j
      (LinearMap.id : Additive U →ₗ[ZMod 2] Additive U) (fun _ _ => rfl)
      ((alternatingGroup (Fin 5)).prod (⊥ : Subgroup (Equiv.Perm (Fin 5)))) ⊤
    have ha : ((alternatingGroup (Fin 5)).prod (⊥ : Subgroup (Equiv.Perm (Fin 5)))).map j =
        (alternatingGroup (Fin 5)).map (SymmetricFive.Paired.leftFactorMap Y c.action.groupEquiv) := by
      ext x
      constructor
      · rintro ⟨g,hg,rfl⟩
        exact ⟨g.1,hg.1,congrArg j (Prod.ext rfl hg.2.symm)⟩
      · rintro ⟨g,hg,rfl⟩
        exact ⟨(g,1),⟨hg,one_mem _⟩,rfl⟩
    simpa only [Submodule.map_id,ha] using hh
  have hs : Function.Injective s₁ := by
    intro x y hxy
    have hh := congrArg c.symmetricCoreMap hxy
    rw [h₁,h₁] at hh
    exact congrArg Prod.fst hh
  let W := (⁅U,L⁆ : Subgroup G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U L)
  let f := (NormalElementaryQuotient.commutatorSpaceEquiv U L).trans
    ((LinearEquiv.ofEq _ _ hm).symm.trans (LinearEquiv.ofInjective s₁ hs).symm)
  have hv (v : Additive W) : s₁ (f v) =
      Additive.ofMul (⟨v.toMul,(commutator_le_left U L) v.toMul.property⟩ : U) := by
    exact congrArg Subtype.val ((LinearEquiv.ofInjective s₁ hs).apply_symm_apply
      ((LinearEquiv.ofEq _ _ hm).symm (NormalElementaryQuotient.commutatorSpaceEquiv U L v)))
  have hc (v : Additive W) : c.symmetricCoreMap
      (Additive.ofMul (⟨v.toMul,(commutator_le_left U L) v.toMul.property⟩ : U)) = (f v,0) := by
    rw [←hv,h₁]
  refine ⟨f,hc,?_⟩
  intro g hg v hgv
  have hh := c.symmetricCoreMap_action ⟨q g,hg⟩
    (Additive.ofMul (⟨v.toMul,(commutator_le_left U L) v.toMul.property⟩ : U))
  have hx : α (q g) (Additive.ofMul (⟨v.toMul,(commutator_le_left U L) v.toMul.property⟩ : U)) =
      Additive.ofMul (⟨g*(v.toMul:G)*g⁻¹,(commutator_le_left U L) hgv⟩ : U) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply U q hq hk g _
  change c.symmetricCoreMap (α (q g) _) = _ at hh
  have hc' := hc (Additive.ofMul (⟨g*(v.toMul:G)*g⁻¹,hgv⟩ : W))
  change c.symmetricCoreMap (Additive.ofMul (⟨g*(v.toMul:G)*g⁻¹,(commutator_le_left U L) hgv⟩ : U)) =
    (f (Additive.ofMul (⟨g*(v.toMul:G)*g⁻¹,hgv⟩ : W)),0) at hc'
  rw [hx,hc',hc] at hh
  exact congrArg Prod.fst hh
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
