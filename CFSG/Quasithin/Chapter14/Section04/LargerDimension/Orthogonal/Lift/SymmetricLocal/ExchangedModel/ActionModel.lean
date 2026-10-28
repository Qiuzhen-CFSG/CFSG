module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Defs
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.Algebra.Module.ZMod

/-!
# The actual determinant coordinates for source case (3)

The input marks U/Z(U), the local conjugation action, and the preimage of its component
square. This preimage has two-group quotient, and the action kernel
lies in U. Hence the common two-residual has a nonsolvable image in the
literal SL₂(4) × SL₂(4) matrix group whenever the residual is nonsolvable.

The same coordinates identify the ambient commutator image with the range
of the involution displacement and transport invariant subgroups to binary
subspaces. In particular the maps and commutator convention are retained.
No moved-rank, irreducibility or component-exchange assertion is an input.

Source: Aschbacher–Smith, case (3) of 14.4.2 and Lemma 14.4.9,
printed pp.1006–1007 and 1010. The case-(3) producer supplies the marking.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G]

/-- The marked determinant action in source case (3). The component preimage
has a two-group quotient and acts by the literal left-right matrix action. -/
structure CaseThreeAction (H U : Subgroup G) where
  normalizes : H ≤ normalizer (U : Set G)
  coordinates : (U ⧸ center U) ≃* Multiplicative Binary.V
  action : H →* (Binary.V ≃ₗ[ZMod 2] Binary.V)
  equivariant : ∀ h : H, ∀ u : U,
    coordinates (QuotientGroup.mk' (center U)
      (U.normalizerMonoidHom ⟨h, normalizes h.property⟩ u)) =
      Multiplicative.ofAdd (action h (coordinates (QuotientGroup.mk' (center U) u)).toAdd)
  kernel : action.ker ≤ U.subgroupOf H
  components : Subgroup H
  components_normal : components.Normal
  outer_two : letI := components_normal; IsPGroup 2 (H ⧸ components)
  components_image : components.map action = Binary.linearAction.range

namespace CaseThreeAction
variable {H U : Subgroup G} (m : CaseThreeAction H U)

/-- The quotient action before choosing vector coordinates. -/
def quotientAction : H →* MulAut (U ⧸ center U) :=
  (quotientAut (center U)).comp (U.normalizerMonoidHom.comp
    (inclusion m.normalizes))

theorem quotientAction_apply (h : H) (u : U) :
    m.quotientAction h (QuotientGroup.mk' (center U) u) =
    QuotientGroup.mk' (center U) (U.normalizerMonoidHom ⟨h,m.normalizes h.property⟩ u) := by
  exact quotientAut_apply_mk _ _ _

theorem intertwines (h : H) (v : U ⧸ center U) :
    m.coordinates (m.quotientAction h v) =
      Multiplicative.ofAdd (m.action h (m.coordinates v).toAdd) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center U) v
  rw [m.quotientAction_apply]
  exact m.equivariant h u

/-- Every local actor normalizes the two actual matrix factors jointly. -/
theorem action_normalizes (h : H) :
    m.action h ∈ normalizer (Binary.linearAction.range : Set (Binary.V ≃ₗ[ZMod 2] Binary.V)) := by
  rw [← m.components_image]
  let _ := m.components_normal
  exact le_normalizer_map (f := m.action) (mem_map_of_mem m.action
    (m.components.normalizer_eq_top ▸ mem_top h))

/-- The two-residual lies in the component square. -/
theorem residual_le_components (C : Subgroup G) (hCH : C ≤ H) :
    ((pResidual 2 C).map C.subtype).subgroupOf H ≤ m.components := by
  let _ := m.components_normal
  let f := (QuotientGroup.mk' m.components).comp (inclusion hCH)
  have hk : IsPGroup 2 (C ⧸ f.ker) :=
    (m.outer_two.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hp : pResidual 2 C ≤ f.ker := sInf_le ⟨inferInstance, hk⟩
  intro h hh
  obtain ⟨c, hc, he⟩ := hh
  have he' : inclusion hCH c = h := Subtype.ext he
  rw [← he']
  exact (QuotientGroup.eq_one_iff _).mp (hp hc)

/-- The literal residual image in the two special linear factors. -/
def residualMap (C : Subgroup G) (hCH : C ≤ H) :
    (pResidual 2 C) →* Binary.G :=
  (MonoidHom.ofInjective (f := Binary.linearAction) (fun a b hab =>
    Binary.action_injective (congrArg LinearEquiv.toLinearMap hab))).symm.toMonoidHom.comp
      ((m.action.comp ((inclusion hCH).comp (pResidual 2 C).subtype)).codRestrict
        Binary.linearAction.range (by
          intro c
          rw [← m.components_image]
          exact mem_map_of_mem _ (m.residual_le_components C hCH
            (show inclusion hCH c ∈ ((pResidual 2 C).map C.subtype).subgroupOf H from
              ⟨c,c.property,rfl⟩))))

theorem residualMap_spec (C : Subgroup G) (hCH : C ≤ H) (c : pResidual 2 C) :
    Binary.linearAction (m.residualMap C hCH c) = m.action (inclusion hCH c) := by
  exact congrArg Subtype.val ((MonoidHom.ofInjective (f := Binary.linearAction) (fun a b hab =>
    Binary.action_injective (congrArg LinearEquiv.toLinearMap hab))).apply_symm_apply _)

/-- The actual residual map has a two-group kernel, embedded in U. -/
theorem residualMap_kernel_isPGroup [IsExtraspecial 2 U]
    (C : Subgroup G) (hCH : C ≤ H) : IsPGroup 2 (m.residualMap C hCH).ker := by
  let f := m.residualMap C hCH
  let j : f.ker →* U :=
    { toFun := fun c => ⟨((c : pResidual 2 C) : C), m.kernel (by
        change m.action (inclusion hCH (c : pResidual 2 C)) = 1
        rw [← m.residualMap_spec C hCH]
        change Binary.linearAction (f c) = 1
        rw [c.property, map_one])⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (j a : G) = (j b : G)
    exact congrArg Subtype.val hab
  exact (IsExtraspecial.isPGroup 2 U).of_injective j hj

/-- A two-group action kernel cannot kill the nonsolvable residual. -/
theorem residualMap_nonsolvable [Finite G] [IsExtraspecial 2 U]
    (C : Subgroup G) (hCH : C ≤ H) (hn : ¬ Group.IsSolvable (pResidual 2 C)) :
    ¬ Group.IsSolvable (m.residualMap C hCH).range := by
  intro hs
  let _ := hs
  let f := m.residualMap C hCH
  let _ : Group.IsNilpotent f.ker := (m.residualMap_kernel_isPGroup C hCH).isNilpotent
  apply hn
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
    simpa only [MonoidHom.ker_rangeRestrict, range_subtype] using (le_refl f.ker))

/-- The actual central quotient map in determinant coordinates. -/
def projection : U →* Multiplicative Binary.V :=
  m.coordinates.toMonoidHom.comp (QuotientGroup.mk' (center U))

theorem projection_surjective : Function.Surjective m.projection :=
  m.coordinates.surjective.comp (QuotientGroup.mk'_surjective (center U))

theorem projection_equivariant (h : H) (u : U) :
    m.projection (U.normalizerMonoidHom ⟨h,m.normalizes h.property⟩ u) =
      Multiplicative.ofAdd (m.action h (m.projection u).toAdd) := m.equivariant h u

include m in
theorem comm_mem (a : H) (u : U) : ⁅(u:G),(a:G)⁆ ∈ U :=
  (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr (m.normalizes a.property)))
    (commutator_mem_commutator u.property (mem_zpowers a.val))

theorem projection_commutator (a : H) (u : U) :
    m.projection ⟨⁅(u:G),(a:G)⁆, comm_mem m a u⟩ =
      Multiplicative.ofAdd ((m.projection u).toAdd - m.action a (m.projection u).toAdd) := by
  have he : (⟨⁅(u:G),(a:G)⁆, comm_mem m a u⟩ : U) =
      u * U.normalizerMonoidHom ⟨a,m.normalizes a.property⟩ u⁻¹ := by
    apply Subtype.ext
    change ⁅(u:G),(a:G)⁆ = (u:G) * ((a:G) * (u:G)⁻¹ * (a:G)⁻¹)
    simp only [commutatorElement_def, mul_assoc]
  rw [he, map_mul, m.projection_equivariant, map_inv]
  apply Multiplicative.toAdd.injective
  change (m.projection u).toAdd + m.action a (-(m.projection u).toAdd) = _
  rw [map_neg, sub_eq_add_neg]
  rfl

/-- Subgroup coordinates and binary subspace coordinates have identical
membership, since every additive subgroup of a binary space is a subspace. -/
def subspace (F : Subgroup (U ⧸ center U)) : Submodule (ZMod 2) Binary.V :=
  AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm (F.map m.coordinates.toMonoidHom))

theorem subspace_injective : Function.Injective m.subspace := by
  intro A B he
  apply (map_injective (f := m.coordinates.toMonoidHom) m.coordinates.injective)
  exact AddSubgroup.toSubgroup.symm.injective ((AddSubgroup.toZModSubmodule 2).injective he)

@[simp] theorem subspace_bot : m.subspace ⊥ = ⊥ := by
  simp [subspace]

theorem subspace_mono {A B : Subgroup (U ⧸ center U)} (h : A ≤ B) :
    m.subspace A ≤ m.subspace B :=
  (AddSubgroup.toZModSubmodule 2).monotone (AddSubgroup.toSubgroup.symm.monotone (map_mono h))

/-- The literal image of the ambient commutator is exactly the range of the
matrix displacement; the sign in the commutator convention is accounted for. -/
theorem subspace_moved [Finite G] (a : H) (ha : orderOf (a:G) = 2) :
    m.subspace (((⁅U,zpowers (a:G)⁆).subgroupOf U).map (QuotientGroup.mk' (center U))) =
      LinearMap.range ((m.action a).toLinearMap - LinearMap.id) := by
  classical
  let W := LinearMap.range ((m.action a).toLinearMap - LinearMap.id)
  let L := AddSubgroup.toSubgroup W.toAddSubgroup
  have hmap : ((⁅U,zpowers (a:G)⁆).subgroupOf U).map m.projection = L := by
    apply le_antisymm
    · have hb : ⁅U,zpowers (a:G)⁆ ≤ (L.comap m.projection).map U.subtype := by
        apply commutator_le.mpr
        intro u hu b hb
        have hbcases : b = 1 ∨ b = (a:G) := by
          rw [mem_zpowers_iff_mem_range_orderOf, ha] at hb
          obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hb
          have hn : n = 0 ∨ n = 1 := by have := Finset.mem_range.mp hn; omega
          rcases hn with rfl | rfl
          · exact Or.inl (by simpa only [pow_zero] using he.symm)
          · exact Or.inr (by simpa only [pow_one] using he.symm)
        rcases hbcases with rfl | rfl
        · simp
        · refine ⟨⟨⁅u,(a:G)⁆, comm_mem m a ⟨u,hu⟩⟩, ?_, rfl⟩
          change (m.projection ⟨⁅u,(a:G)⁆, comm_mem m a ⟨u,hu⟩⟩).toAdd ∈ W
          rw [m.projection_commutator a ⟨u,hu⟩]
          refine ⟨-(m.projection ⟨u,hu⟩).toAdd, ?_⟩
          change m.action a (-(m.projection ⟨u,hu⟩).toAdd) -
            (-(m.projection ⟨u,hu⟩).toAdd) = _
          simp only [map_neg, toAdd_ofAdd, neg_sub_neg]
      rintro v ⟨u,hu,rfl⟩
      obtain ⟨w,hw,he⟩ := hb hu
      have he' : w = u := Subtype.ext he
      exact he' ▸ hw
    · intro v hv
      obtain ⟨w,hw⟩ := (show v.toAdd ∈ W from hv)
      obtain ⟨u,hu⟩ := m.projection_surjective (Multiplicative.ofAdd (-w))
      refine ⟨⟨⁅(u:G),(a:G)⁆, comm_mem m a u⟩,
        commutator_mem_commutator u.property (mem_zpowers a.val), ?_⟩
      rw [m.projection_commutator, hu]
      apply Multiplicative.toAdd.injective
      change -w - m.action a (-w) = v.toAdd
      rw [map_neg, sub_neg_eq_add, neg_add_eq_sub]
      exact hw
  apply (AddSubgroup.toZModSubmodule 2).symm.injective
  apply AddSubgroup.toSubgroup.injective
  change ((((⁅U,zpowers (a:G)⁆).subgroupOf U).map (QuotientGroup.mk' (center U))).map
    m.coordinates.toMonoidHom) = L
  rw [map_map]
  exact hmap

/-- Cardinality is retained by these literal quotient coordinates. -/
theorem subspace_card (F : Subgroup (U ⧸ center U)) : Nat.card (m.subspace F) = Nat.card F := by
  exact (Nat.card_congr (show m.subspace F ≃ F.map m.coordinates.toMonoidHom from
    { toFun := fun v => ⟨Multiplicative.ofAdd v.val,v.property⟩
      invFun := fun v => ⟨v.val.toAdd,v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })).trans
    (Nat.card_congr (F.equivMapOfInjective m.coordinates.toMonoidHom
      m.coordinates.injective).toEquiv).symm

/-- Invariance transfers through the marked action on representatives. -/
theorem subspace_invariant (F : Subgroup (U ⧸ center U)) (h : H)
    (hF : ∀ v ∈ F, m.quotientAction h v ∈ F) :
    ∀ v ∈ m.subspace F, m.action h v ∈ m.subspace F := by
  intro v hv
  obtain ⟨w,hw,he⟩ := (show Multiplicative.ofAdd v ∈ F.map m.coordinates.toMonoidHom from hv)
  refine (show Multiplicative.ofAdd (m.action h v) ∈ F.map m.coordinates.toMonoidHom from ?_)
  refine ⟨m.quotientAction h w,hF w hw,?_⟩
  change m.coordinates (m.quotientAction h w) = _
  rw [m.intertwines]
  exact congrArg (fun y : Multiplicative Binary.V => Multiplicative.ofAdd (m.action h y.toAdd)) he


end CaseThreeAction

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
