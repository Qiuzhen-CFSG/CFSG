module
public import Theory.Representation.ProductIsotypic.SharpBinary
public import Theory.Representation.NormalElementaryQuotient.CommonChief

/-!
# Literal tensor coordinates on a common chief section

The commuting factors give a surjective product map onto the original
section's actor group. Pulling back along this map preserves irreducibility
and the first factor's faithful action. Sharp displacement three then
constructs an absolutely irreducible constituent with displacement one,
a three-dimensional multiplicity space, and an external tensor equivalence.
The faithful perfect factor acts as the full SL₃(2) on the multiplicity space.

All group and representation maps retain their original inclusions. This
identifies the canonical factor in Aschbacher--Smith 13.1.9, printed p.871.
Identification of the other constituent and the final generation argument
are separate source obligations.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]

/-- Multiplication of the original commuting factors, with the second factor first. -/
noncomputable def commutingProduct (S E : Subgroup Q) (hc : ⁅S,E⁆ = ⊥) :
    (E × S) →* ↥(S ⊔ E) := by
  let iE := inclusion (show E ≤ S ⊔ E from le_sup_right)
  let iS := inclusion (show S ≤ S ⊔ E from le_sup_left)
  have hcomm : ∀ e s, Commute (iE e) (iS s) := by
    intro e s
    apply Subtype.ext
    exact commutator_eq_bot_iff_le_centralizer.mp hc s.property e e.property
  exact iE.noncommCoprod iS hcomm

theorem commutingProduct_left (S E : Subgroup Q) (hc : ⁅S,E⁆ = ⊥) (e : E) :
    commutingProduct S E hc (e,1) = inclusion le_sup_right e := by
  apply Subtype.ext
  exact mul_one _

theorem commutingProduct_right (S E : Subgroup Q) (hc : ⁅S,E⁆ = ⊥) (s : S) :
    commutingProduct S E hc (1,s) = inclusion le_sup_left s := by
  apply Subtype.ext
  exact one_mul _

theorem commutingProduct_surjective (S E : Subgroup Q) (hc : ⁅S,E⁆ = ⊥) :
    Function.Surjective (commutingProduct S E hc) := by
  apply MonoidHom.range_eq_top.mp
  have hr : (commutingProduct S E hc).range =
      (inclusion (show E ≤ S ⊔ E from le_sup_right)).range ⊔
        (inclusion (show S ≤ S ⊔ E from le_sup_left)).range :=
    MonoidHom.noncommCoprod_range
      (inclusion (show E ≤ S ⊔ E from le_sup_right))
      (inclusion (show S ≤ S ⊔ E from le_sup_left))
      (fun (e : E) (s : S) => Subtype.ext
        (commutator_eq_bot_iff_le_centralizer.mp hc s.property e e.property))
  rw [hr]
  apply Subgroup.map_injective (S ⊔ E).subtype_injective
  rw [Subgroup.map_sup,←MonoidHom.range_comp,←MonoidHom.range_comp]
  change E.subtype.range ⊔ S.subtype.range = _
  rw [range_subtype,range_subtype,←MonoidHom.range_eq_map,range_subtype,sup_comm]

variable {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V}

/-- Pull back the literal chief-section action to its two commuting factors. -/
noncomputable def Data.productRepresentation (d : Data ρ S K A support)
    (hc : ⁅S,K ⊔ A⁆ = ⊥) :=
  (sectionRepresentation (ρ.comp (actorGroup S K A).subtype) d.lower d.upper).comp
    (commutingProduct S (K ⊔ A) hc)

theorem Data.productRepresentation_left (d : Data ρ S K A support)
    (hc : ⁅S,K ⊔ A⁆ = ⊥) (g : ↥(K ⊔ A)) (v) :
    d.productRepresentation hc (g,1) v =
      sectionRepresentation (ρ.comp (actorGroup S K A).subtype) d.lower d.upper
        (inclusion (show K ⊔ A ≤ actorGroup S K A from le_sup_right) g) v := by
  change sectionRepresentation _ _ _ (commutingProduct S (K ⊔ A) hc (g,1)) v = _
  rw [commutingProduct_left]
  rfl

theorem Data.productRepresentation_right (d : Data ρ S K A support)
    (hc : ⁅S,K ⊔ A⁆ = ⊥) (g : S) (v) :
    d.productRepresentation hc (1,g) v =
      sectionRepresentation (ρ.comp (actorGroup S K A).subtype) d.lower d.upper
        (inclusion (show S ≤ actorGroup S K A from le_sup_left) g) v := by
  change sectionRepresentation _ _ _ (commutingProduct S (K ⊔ A) hc (1,g)) v = _
  rw [commutingProduct_right]
  rfl

open scoped MatrixGroups
/-- Tensor coordinates identifying the original canonical factor by its natural action. -/
structure Data.NaturalTensor (d : Data ρ S K A support) (hc : ⁅S,K ⊔ A⁆ = ⊥) where
  tensor : ProductIsotypic.SharpTensor (d.productRepresentation hc) (A.subgroupOf (K ⊔ A))
  canonical : S ≃* SL(3,ZMod 2)
  canonical_action : ∀ s v, tensor.multiplicity s v = (canonical s).val.mulVec v

/-- Construct the tensor marking from sharp displacement and canonical faithfulness. -/
theorem Data.exists_naturalTensor [Finite Q] [FiniteDimensional (ZMod 2) V]
    [Group.IsPerfect S] [Nontrivial S]
    (d : Data ρ S K A support) (hc : ⁅S,K ⊔ A⁆ = ⊥)
    (hf : Function.Injective ((sectionRepresentation (ρ.comp (actorGroup S K A).subtype)
      d.lower d.upper).comp (inclusion (show S ≤ actorGroup S K A from le_sup_left))))
    (hd : fixedCodim (sectionRepresentation (ρ.comp (actorGroup S K A).subtype)
      d.lower d.upper) (A.subgroupOf (actorGroup S K A)) = 3) :
    Nonempty (d.NaturalTensor hc) := by
  let σ := sectionRepresentation (ρ.comp (actorGroup S K A).subtype) d.lower d.upper
  let δ := d.productRepresentation hc
  let : IsIrreducible δ :=
    (irreducible_comp_surjective_iff (commutingProduct S (K ⊔ A) hc)
      (commutingProduct_surjective S (K ⊔ A) hc) σ).mpr d.irreducible
  have hright : δ.comp (MonoidHom.inr ↥(K ⊔ A) S) =
      σ.comp (inclusion (show S ≤ actorGroup S K A from le_sup_left)) := by
    apply MonoidHom.ext
    intro s
    apply LinearMap.ext
    intro v
    exact d.productRepresentation_right hc s v
  have hfix : fixedSpace (ProductIsotypic.left δ) (A.subgroupOf (K ⊔ A)) =
      fixedSpace σ (A.subgroupOf (actorGroup S K A)) := by
    ext v
    constructor
    · intro hv a
      have hh := hv ⟨⟨a.val,mem_sup_right a.property⟩,a.property⟩
      change δ (⟨a.val,mem_sup_right a.property⟩,1) v = v at hh
      rw [d.productRepresentation_left] at hh
      exact hh
    · intro hv a
      have hh := hv ⟨inclusion (show K ⊔ A ≤ actorGroup S K A from le_sup_right) a.val,a.property⟩
      change δ (a.val,1) v = v
      rw [d.productRepresentation_left]
      exact hh
  have hcod : fixedCodim (ProductIsotypic.left δ) (A.subgroupOf (K ⊔ A)) = 3 := by
    unfold fixedCodim
    rw [hfix]
    exact hd
  obtain ⟨t,e,he⟩ := ProductIsotypic.exists_natural_sharpTensor δ (hright.symm ▸ hf) _ hcod
  exact ⟨⟨t,e,he⟩⟩
end Representation.CommonChief

namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥}

/-- The actor remains faithful on the actual tensor constituent. -/
theorem Data.NaturalTensor.actor_faithful [K.Normal] [IsSimpleGroup K]
    (d : c.NaturalTensor hc) (hf : A ⊓ centralizer (K : Set Q) = ⊥) :
    ∀ a ∈ A.subgroupOf (K ⊔ A),
      (∀ v, d.tensor.constituent.toRepresentation a v = v) → a = 1 := by
  intro a ha hfix
  have hk : a ∈ d.tensor.constituent.toRepresentation.ker := LinearMap.ext hfix
  rw [d.tensor.constituent_kernel] at hk
  let aF : actorGroup S K A := inclusion (show K ⊔ A ≤ actorGroup S K A from le_sup_right) a
  have hF : aF = 1 := simple_normal_inclusion_actor_faithful K (actorGroup S K A) A
    (le_sup_left.trans le_sup_right) _ c.second_moves hf aF ha (fun v => by
      have hh := LinearMap.congr_fun hk v
      change c.productRepresentation hc (a,1) v = v at hh
      rw [c.productRepresentation_left] at hh
      exact hh)
  exact Subtype.ext (congrArg (fun x : actorGroup S K A => (x : Q)) hF)

/-- Passing to the constructed constituent loses no actor rank. -/
theorem Data.NaturalTensor.actor_rank [Finite Q] [K.Normal] [IsSimpleGroup K]
    (d : c.NaturalTensor hc) (hf : A ⊓ centralizer (K : Set Q) = ⊥) :
    rank (actionSubgroup d.tensor.constituent.toRepresentation (A.subgroupOf (K ⊔ A))) =
      rank A := by
  rw [actionSubgroup_rank _ _ (d.actor_faithful hf)]
  unfold rank
  rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ K ⊔ A from le_sup_right)).toEquiv]
end Representation.CommonChief
