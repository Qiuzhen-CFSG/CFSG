module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualImages
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric
public import Theory.Representation.BinaryPermutation.FivePairMoved
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# The original moved modules of the symmetric-five source pair

Apply the two class-sum sections to the same marked offender product and
original centralizer quotient. Their ranges are exactly the original
residual-factor commutator subgroups, and the sections intertwine the full
original product action. The symmetric factor and its alternating residual
have identical moved supports, giving the literal Vi of E.2.3. Both are
four-dimensional natural A5 modules, hence have order sixteen.

Source: Aschbacher–Smith B.6.9 and E.2.3(3), printed pp.115–116 and216–217.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

/-- Natural coordinates on the original two moved subgroups, equivariant
for their actual offender product and preserving the original quotient. -/
theorem paired_symmetric_residual_module_sections
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5))) :
    let α := NormalElementaryQuotient.representation U q hq hker
    let Y := offenderSubgroup α
    ∃ s₁ s₂ : core (Fin 5) →ₗ[ZMod 2] Additive U,
      (∀ v, c.symmetricCoreMap (s₁ v) = (v,0)) ∧
      (∀ v, c.symmetricCoreMap (s₂ v) = (0,v)) ∧
      (∀ g : Y, ∀ v, s₁ (coreRepresentation (Fin 5) (c.action.groupEquiv g).1 v) =
        α (g:H) (s₁ v)) ∧
      (∀ g : Y, ∀ v, s₂ (coreRepresentation (Fin 5) (c.action.groupEquiv g).2 v) =
        α (g:H) (s₂ v)) ∧
      s₁.range = NormalElementaryQuotient.commutatorSpace U (factorResidual q Y d.first) ∧
      s₂.range = NormalElementaryQuotient.commutatorSpace U (factorResidual q Y d.second) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  let σ := α.comp j
  have he (g : S5 × S5) (v : Additive U) :
      c.symmetricCoreMap (σ g v) = FivePair.action g (c.symmetricCoreMap v) := by
    simpa only [σ,j,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using c.symmetricCoreMap_action (c.action.groupEquiv.symm g) v
  have hk (v : Additive U) (hv : c.symmetricCoreMap v = 0) (g : S5 × S5) : σ g v = v := by
    have hfix : v ∈ Representation.invariants (α.comp Y.subtype) := c.symmetricCoreMap_ker ▸ hv
    exact hfix (c.action.groupEquiv.symm g)
  obtain ⟨s₁,s₂,h₁,h₂,he₁,he₂,hr₁,hr₂⟩ := FivePair.exists_moved_sections σ c.symmetricCoreMap
    c.symmetricCoreMap_surjective he hk
  have hm (A : Subgroup (S5 × S5)) :
      subspaceCommutator σ ⊤ A = subspaceCommutator α ⊤ (A.map j) := by
    have hh := subspaceCommutator_map_embedding σ α j (LinearMap.id : Additive U →ₗ[ZMod 2] Additive U)
      (fun _ _ => rfl) A ⊤
    simpa only [Submodule.map_id] using hh
  refine ⟨s₁,s₂,h₁,h₂,?_,?_,?_,?_⟩
  · intro g v
    simpa only [σ,j,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply,Subgroup.subtype_apply] using he₁ (c.action.groupEquiv g) v
  · intro g v
    simpa only [σ,j,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply,Subgroup.subtype_apply] using he₂ (c.action.groupEquiv g) v
  · rw [hr₁,hm,NormalElementaryQuotient.commutatorSpace_eq U q hq hker,
      paired_symmetric_first_residual_image α q hq d c]
  · rw [hr₂,hm,NormalElementaryQuotient.commutatorSpace_eq U q hq hker,
      paired_symmetric_second_residual_image α q hq d c]

omit [Finite G] in
private theorem commutator_eq_of_space_eq
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (X Z : Subgroup G)
    (he : NormalElementaryQuotient.commutatorSpace U X =
      NormalElementaryQuotient.commutatorSpace U Z) :
    (⁅U,X⁆ : Subgroup G) = ⁅U,Z⁆ := by
  apply le_antisymm
  · intro x hx
    have hv : Additive.ofMul (⟨x,(commutator_le_left U X) hx⟩ : U) ∈
        NormalElementaryQuotient.commutatorSpace U X := hx
    rw [he] at hv
    exact hv
  · intro x hx
    have hv : Additive.ofMul (⟨x,(commutator_le_left U Z) hx⟩ : U) ∈
        NormalElementaryQuotient.commutatorSpace U Z := hx
    rw [←he] at hv
    exact hv

/-- The original Hi moved modules equal those of the same literal residual
factors; no central quotient or unrelated isomorphism replaces the modules. -/
theorem paired_symmetric_preimage_moved_eq
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5))) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    (⁅U,factorPreimage q Y d.first⁆ : Subgroup G) = ⁅U,factorResidual q Y d.first⁆ ∧
    (⁅U,factorPreimage q Y d.second⁆ : Subgroup G) = ⁅U,factorResidual q Y d.second⁆ := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  let σ := α.comp j
  have he (g : S5 × S5) (v : Additive U) :
      c.symmetricCoreMap (σ g v) = FivePair.action g (c.symmetricCoreMap v) := by
    simpa only [σ,j,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using c.symmetricCoreMap_action (c.action.groupEquiv.symm g) v
  have hk (v : Additive U) (hv : c.symmetricCoreMap v = 0) (g : S5 × S5) : σ g v = v := by
    have hfix : v ∈ Representation.invariants (α.comp Y.subtype) := c.symmetricCoreMap_ker ▸ hv
    exact hfix (c.action.groupEquiv.symm g)
  have hm (A : Subgroup (S5 × S5)) :
      subspaceCommutator σ ⊤ A = subspaceCommutator α ⊤ (A.map j) := by
    have hh := subspaceCommutator_map_embedding σ α j (LinearMap.id : Additive U →ₗ[ZMod 2] Additive U)
      (fun _ _ => rfl) A ⊤
    simpa only [Submodule.map_id] using hh
  have hp₁ : (factorPreimage q Y d.first).map q = ((⊤ : Subgroup S5).prod ⊥).map j := by
    rw [factorPreimage,map_comap_eq_self_of_surjective hq,←c.first_eq,map_map]
  have hp₂ : (factorPreimage q Y d.second).map q = ((⊥ : Subgroup S5).prod ⊤).map j := by
    rw [factorPreimage,map_comap_eq_self_of_surjective hq,←c.second_eq,map_map]
  have hfull := FivePair.full_residual_moved_eq σ c.symmetricCoreMap
    c.symmetricCoreMap_surjective he hk
  constructor
  · apply commutator_eq_of_space_eq U
    rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hker,
      NormalElementaryQuotient.commutatorSpace_eq U q hq hker,hp₁,
      paired_symmetric_first_residual_image α q hq d c,←hm,←hm]
    exact hfull.1
  · apply commutator_eq_of_space_eq U
    rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hker,
      NormalElementaryQuotient.commutatorSpace_eq U q hq hker,hp₂,
      paired_symmetric_second_residual_image α q hq d c,←hm,←hm]
    exact hfull.2
omit [Finite G] in
private theorem commutator_card_of_natural_section
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (X : Subgroup G)
    (f : core (Fin 5) →ₗ[ZMod 2] Additive U) (hf : Function.Injective f)
    (hr : f.range = NormalElementaryQuotient.commutatorSpace U X) :
    Nat.card (⁅U,X⁆ : Subgroup G) = 16 := by
  let : IsElementaryAbelian 2 (⁅U,X⁆ : Subgroup G) :=
    IsElementaryAbelian.of_le (commutator_le_left U X)
  let e := (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)
  let eW := (NormalElementaryQuotient.commutatorSpaceEquiv U X).trans e.symm
  change Nat.card (Additive (⁅U,X⁆ : Subgroup G)) = 16
  rw [Nat.card_congr eW.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
    BinaryPermutation.finrank_core]
  norm_num

/-- Both original Vi=[U,Hi] have order sixteen, on the same marked source pair. -/
theorem paired_symmetric_preimage_modules_card
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5))) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    Nat.card (⁅U,factorPreimage q Y d.first⁆ : Subgroup G) = 16 ∧
      Nat.card (⁅U,factorPreimage q Y d.second⁆ : Subgroup G) = 16 := by
  obtain ⟨s₁,s₂,h₁,h₂,_,_,hr₁,hr₂⟩ := paired_symmetric_residual_module_sections U q hq hker d c
  have hi₁ : Function.Injective s₁ := by
    intro v w he
    have hh := congrArg c.symmetricCoreMap he
    rw [h₁,h₁] at hh
    exact congrArg Prod.fst hh
  have hi₂ : Function.Injective s₂ := by
    intro v w he
    have hh := congrArg c.symmetricCoreMap he
    rw [h₂,h₂] at hh
    exact congrArg Prod.snd hh
  have hc₁ := commutator_card_of_natural_section U _ s₁ hi₁ hr₁
  have hc₂ := commutator_card_of_natural_section U _ s₂ hi₂ hr₂
  have he := paired_symmetric_preimage_moved_eq U q hq hker d c
  exact ⟨he.1.symm ▸ hc₁,he.2.symm ▸ hc₂⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
