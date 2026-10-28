module
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor
public import Theory.Representation.BinaryHyperplane.SmallFactors
public import Theory.Representation.BinaryHyperplane.NaturalThree

/-!
# Recognition of the other factor on the same chief-section tensor

The second simple factor acts faithfully on the existing tensor constituent.
Its rank-two fixed-hyperplane actor excludes A₅ and identifies a surviving
SL₃(2) factor with the natural binary three-space. Both coordinate maps refer
to the same constituent and the same common chief section. The actor's image
is contained in the actual second-factor image. In the same coordinates,
the rank-two actor is the entire common-axis group: the two-core of the
stabilizer of its fixed plane.

Source: Aschbacher--Smith 13.1.9, printed p.871. Controlled Thompson selection
and the final ambient generation argument are not asserted here.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥}
theorem Data.NaturalTensor.second_faithful [IsSimpleGroup K]
    (d : c.NaturalTensor hc) :
    Function.Injective (d.tensor.constituent.toRepresentation.comp
      (inclusion (show K ≤ K ⊔ A from le_sup_left))) := by
  let σ := d.tensor.constituent.toRepresentation
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (σ.comp (inclusion (show K ≤ K ⊔ A from le_sup_left))).normal_ker.eq_bot_or_eq_top with hz | ht
  · exact hz
  · exfalso
    apply c.second_moves
    intro k hk
    let kK : K := ⟨k.val,hk⟩
    have hmem : inclusion (show K ≤ K ⊔ A from le_sup_left) kK ∈ σ.ker :=
      show kK ∈ (σ.comp (inclusion (show K ≤ K ⊔ A from le_sup_left))).ker from ht.symm ▸ mem_top _
    rw [d.tensor.constituent_kernel] at hmem
    apply LinearMap.ext
    intro v
    have hh := LinearMap.congr_fun hmem v
    change c.productRepresentation hc (inclusion (show K ≤ K ⊔ A from le_sup_left) kK,1) v = v at hh
    rw [c.productRepresentation_left] at hh
    exact hh

variable [FiniteDimensional (ZMod 2) V]
/-- The rank-two hyperplane actor rules out an alternating-five second factor. -/
theorem Data.NaturalTensor.not_alternating_five [K.Normal] [IsSimpleGroup K]
    (d : c.NaturalTensor hc) (he : IsElementaryAbelian 2 A)
    (hf : A ⊓ centralizer (K : Set Q) = ⊥) (hr : 1 < rank A)
    (e : K ≃* alternatingGroup (Fin 5)) : False := by
  let F := actorGroup S K A
  let U := c.upper.toSubmodule ⧸ (sectionLower (ρ.comp F.subtype) c.lower c.upper).toSubmodule
  let : AddCommGroup U := inferInstance
  let : Module (ZMod 2) U := inferInstance
  let : FiniteDimensional (ZMod 2) U := inferInstance
  let : AddCommGroup d.tensor.constituent.toSubmodule := inferInstance
  let : Module (ZMod 2) d.tensor.constituent.toSubmodule := inferInstance
  let : FiniteDimensional (ZMod 2) d.tensor.constituent.toSubmodule := inferInstance
  have hb := AlternatingFiveHyperplane.actor_card_le_two_in_join K A
    d.tensor.constituent.toRepresentation he d.second_faithful hf e d.tensor.displacement.le
  have hl := Nat.log_mono_right (b := 2) hb
  change rank A ≤ 1 at hl
  omega
end Representation.CommonChief


open Subgroup Representation Representation.BinaryOffender
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥}

structure Data.NaturalTensor.OtherNatural (d : c.NaturalTensor hc) where
  second : K ≃* SL(3,ZMod 2)
  coordinates : d.tensor.constituent.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)
  second_action : ∀ k v,
    coordinates (d.tensor.constituent.toRepresentation
      (inclusion (show K ≤ K ⊔ A from le_sup_left) k) v) =
        (second k).val.mulVec (coordinates v)

variable [FiniteDimensional (ZMod 2) V]
theorem Data.NaturalTensor.exists_otherNatural [K.Normal] [IsSimpleGroup K]
    (d : c.NaturalTensor hc) (he : IsElementaryAbelian 2 A)
    (hf : A ⊓ centralizer (K : Set Q) = ⊥) (hr : 1 < rank A)
    (e : K ≃* Matrix.PSL3Two.SL) : Nonempty d.OtherNatural := by
  let F := actorGroup S K A
  let U := c.upper.toSubmodule ⧸ (sectionLower (ρ.comp F.subtype) c.lower c.upper).toSubmodule
  let : AddCommGroup U := inferInstance
  let : Module (ZMod 2) U := inferInstance
  let : FiniteDimensional (ZMod 2) U := inferInstance
  let : AddCommGroup d.tensor.constituent.toSubmodule := inferInstance
  let : Module (ZMod 2) d.tensor.constituent.toSubmodule := inferInstance
  let : FiniteDimensional (ZMod 2) d.tensor.constituent.toSubmodule := inferInstance
  let := d.tensor.irreducible
  have hr' : 2 < Nat.card A := by
    by_contra! hle
    have hl := Nat.log_mono_right (b := 2) hle
    change rank A ≤ 1 at hl
    omega
  obtain ⟨e',f,hf'⟩ := BinaryHyperplane.linear_three_natural_in_join K A
    d.tensor.constituent.toRepresentation he d.second_faithful hf hr' e d.tensor.displacement.le
  exact ⟨⟨e',f,hf'⟩⟩
end Representation.CommonChief
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥} {d : c.NaturalTensor hc}

theorem Data.NaturalTensor.OtherNatural.realizes
    (n : d.OtherNatural) (a : ↥(K ⊔ A)) :
    ∃ k : K, d.tensor.constituent.toRepresentation a =
      d.tensor.constituent.toRepresentation (inclusion (show K ≤ K ⊔ A from le_sup_left) k) := by
  let σ := d.tensor.constituent.toRepresentation
  let f := n.coordinates
  let b : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    (f.symm.trans (LinearEquiv.ofBijective (σ a) (σ.apply_bijective a))).trans f
  let s := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm b
  refine ⟨n.second.symm s,?_⟩
  apply LinearMap.ext
  intro v
  apply f.injective
  change f (σ a v) = f (σ (inclusion (show K ≤ K ⊔ A from le_sup_left) (n.second.symm s)) v)
  rw [n.second_action,n.second.apply_symm_apply]
  have hb := BinaryLinear.OuterCyclic.slEquivLinear_apply 3 s (f v)
  rw [show BinaryLinear.OuterCyclic.slEquivLinear 3 s = b from
    (BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply b] at hb
  simpa only [b,LinearEquiv.trans_apply,LinearEquiv.ofBijective_apply,f.symm_apply_apply] using hb

private theorem actionSubgroup_le_of_realizes
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) H W) (B C : Subgroup H)
    (h : ∀ a : H, ∃ k ∈ C, σ a = σ k) : actionSubgroup σ B ≤ actionSubgroup σ C := by
  rintro _ ⟨a,_,rfl⟩
  obtain ⟨k,hk,he⟩ := h a
  refine ⟨k,hk,?_⟩
  apply imageRepresentation_injective σ
  exact he.symm

/-- The quotient image of the actor lies in the image of the same second factor. -/
theorem Data.NaturalTensor.OtherNatural.actor_image_le (n : d.OtherNatural) :
    actionSubgroup d.tensor.constituent.toRepresentation (A.subgroupOf (K ⊔ A)) ≤
      actionSubgroup d.tensor.constituent.toRepresentation (K.subgroupOf (K ⊔ A)) := by
  apply actionSubgroup_le_of_realizes
  intro a
  obtain ⟨k,hk⟩ := n.realizes a
  exact ⟨inclusion (show K ≤ K ⊔ A from le_sup_left) k,k.property,hk⟩

private theorem same_kernel_same_value
    {H M N : Type*} [Group H] [Monoid M] [Monoid N]
    (f : H →* M) (g : H →* N) (h : f.ker = g.ker)
    {a b : H} (he : f a = f b) : g a = g b := by
  rw [MonoidHom.eq_iff] at he ⊢
  rwa [←h]

theorem Data.NaturalTensor.OtherNatural.realizes_section
    (n : d.OtherNatural) (a : ↥(K ⊔ A)) :
    ∃ k : K,
      sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper
        (inclusion (show K ⊔ A ≤ actorGroup S K A from le_sup_right) a) =
      sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper
        (inclusion (show K ≤ actorGroup S K A from le_sup_left.trans le_sup_right) k) := by
  obtain ⟨k,hk⟩ := n.realizes a
  refine ⟨k,?_⟩
  let kE := inclusion (show K ≤ K ⊔ A from le_sup_left) k
  have he := same_kernel_same_value d.tensor.constituent.toRepresentation
    (ProductIsotypic.left (c.productRepresentation hc)) d.tensor.constituent_kernel hk
  apply LinearMap.ext
  intro v
  have hh := LinearMap.congr_fun he v
  change c.productRepresentation hc (a,1) v = c.productRepresentation hc (kE,1) v at hh
  have hkE : inclusion (show K ⊔ A ≤ actorGroup S K A from le_sup_right) kE =
      inclusion (show K ≤ actorGroup S K A from le_sup_left.trans le_sup_right) k :=
    Subtype.ext rfl
  simpa only [c.productRepresentation_left,hkE] using hh


/-- The actor and second-factor images under the original section quotient map. -/
@[expose] def Data.ActorImageContained (c : Data ρ S K A support) : Prop :=
  actionSubgroup (sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper)
    (A.subgroupOf (actorGroup S K A)) ≤
  actionSubgroup (sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper)
    (K.subgroupOf (actorGroup S K A))

/-- Containment in the second factor under the literal chief-section quotient action. -/
theorem Data.NaturalTensor.OtherNatural.section_actor_image_le (n : d.OtherNatural) :
    actionSubgroup (sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper)
      (A.subgroupOf (actorGroup S K A)) ≤
    actionSubgroup (sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper)
      (K.subgroupOf (actorGroup S K A)) := by
  let σ := sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper
  change actionSubgroup σ _ ≤ actionSubgroup σ _
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨k,hk⟩ := n.realizes_section ⟨a.val,mem_sup_right ha⟩
  refine ⟨inclusion (show K ≤ actorGroup S K A from le_sup_left.trans le_sup_right) k,k.property,?_⟩
  apply imageRepresentation_injective σ
  exact hk.symm

end Representation.CommonChief

open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥} {d : c.NaturalTensor hc}

noncomputable def Data.NaturalTensor.OtherNatural.matrixAction (n : d.OtherNatural) :
    ↥(K ⊔ A) →* SL(3,ZMod 2) :=
  BinaryThreeCoordinates.matrixAction d.tensor.constituent.toRepresentation n.coordinates

noncomputable def Data.NaturalTensor.OtherNatural.matrixActor (n : d.OtherNatural) :
    Subgroup SL(3,ZMod 2) := (A.subgroupOf (K ⊔ A)).map n.matrixAction

/-- The matrix actor uses the original actor inclusion and coordinate action. -/
theorem Data.NaturalTensor.OtherNatural.matrixActor_eq (n : d.OtherNatural) :
    n.matrixActor = (A.subgroupOf (K ⊔ A)).map n.matrixAction := by rfl

/-- Sharp displacement identifies the same matrix actor's fixed plane. -/
theorem Data.NaturalTensor.OtherNatural.matrixActor_fixed_plane
    [FiniteDimensional (ZMod 2) V] (n : d.OtherNatural) :
    Module.finrank (ZMod 2) (fixedSpace BinaryLinearThree.W n.matrixActor) = 2 := by
  exact BinaryThreeCoordinates.matrixAction_fixed_plane d.tensor.constituent.toRepresentation
    n.coordinates (A.subgroupOf (K ⊔ A)) d.tensor.displacement

theorem Data.NaturalTensor.OtherNatural.matrixAction_second (n : d.OtherNatural) (k : K) :
    n.matrixAction (inclusion (show K ≤ K ⊔ A from le_sup_left) k) = n.second k := by
  apply (BinaryLinear.OuterCyclic.slEquivLinear 3).injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := n.coordinates.surjective v
  rw [BinaryLinear.OuterCyclic.slEquivLinear_apply,BinaryLinear.OuterCyclic.slEquivLinear_apply]
  exact (BinaryThreeCoordinates.matrixAction_apply
    d.tensor.constituent.toRepresentation n.coordinates _ w).symm.trans (n.second_action k w)

theorem Data.NaturalTensor.OtherNatural.matrixActor_eq_core [Finite Q]
    [FiniteDimensional (ZMod 2) V] [K.Normal] [IsSimpleGroup K]
    (n : d.OtherNatural) (he : IsElementaryAbelian 2 A)
    (hf : A ⊓ centralizer (K : Set Q) = ⊥) (hr : rank A = 2) :
    n.matrixActor = (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
      (fixedSpace BinaryLinearThree.W n.matrixActor)).pCoreIn 2 := by
  let F := actorGroup S K A
  let U := c.upper.toSubmodule ⧸ (sectionLower (ρ.comp F.subtype) c.lower c.upper).toSubmodule
  let : AddCommGroup U := inferInstance
  let : Module (ZMod 2) U := inferInstance
  let : FiniteDimensional (ZMod 2) U := inferInstance
  let : AddCommGroup d.tensor.constituent.toSubmodule := inferInstance
  let : Module (ZMod 2) d.tensor.constituent.toSubmodule := inferInstance
  let : FiniteDimensional (ZMod 2) d.tensor.constituent.toSubmodule := inferInstance
  have hn : A ≠ ⊥ := by
    intro hz
    simp [hz,rank] at hr
  have hcA := IsElementaryTwo.card_eq_two_pow_rank (show IsElementaryTwo A from ⟨hn,he⟩)
  rw [hr] at hcA
  have hcard : Nat.card (A.subgroupOf (K ⊔ A)) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ K ⊔ A from le_sup_right)).toEquiv]
    exact hcA
  exact BinaryThreeCoordinates.matrixAction_actor_eq_core d.tensor.constituent.toRepresentation
    n.coordinates (A.subgroupOf (K ⊔ A)) (d.actor_faithful hf) hcard d.tensor.displacement
end Representation.CommonChief
