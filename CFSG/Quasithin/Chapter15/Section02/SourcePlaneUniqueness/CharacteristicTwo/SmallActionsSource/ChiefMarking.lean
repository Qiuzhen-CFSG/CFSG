module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.MarkedWreath

public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryGroupAction

/-!
# Centralizer markings in the original natural chief action

The natural coordinate planes pull back to complementary four-groups in the
original chief module. Their pointwise centralizers are exactly the two
marked actor factors, and conjugation follows the literal wreath permutation.
The coordinate transvections have displacement rank one, so their cyclic
subgroups are best offenders. Hence the image of the offender subgroup
contains the distinguished paired base. The source Thompson equality is
applied to this containment in MarkedAssembly.

Source: Aschbacher--Smith, Notation15.2.9 and15.2.21(1), printed pp.1110,1114.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource

abbrev ChiefWreathActor := RegularWreathProduct
  (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))
abbrev ChiefWreathSpace := Multiplicative (ZMod 2) → Multiplicative (Fin 2 → ZMod 2)

/-- Whole action coordinates, retaining the literal actor homomorphism. -/
structure ChiefWreathCoordinates {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W) where
  actor : D →* ChiefWreathActor
  surjective : Function.Surjective actor
  kernel : actor.ker = (actionHom ρ).ker
  vectors : Multiplicative W ≃* ChiefWreathSpace
  intertwines : ∀ g v i, vectors (Multiplicative.ofAdd (ρ g v.toAdd)) i =
    Multiplicative.ofAdd (Matrix.mulVec ((actor g).left i).1
      ((vectors v ((actor g).right⁻¹ * i)).toAdd))

private theorem base_le_image_offenders
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (e : D ≃* ChiefWreath.Actor) (c : Multiplicative W ≃* ChiefWreath.Space)
    (he : ∀ g v, c (Multiplicative.ofAdd (ρ g v.toAdd)) = ChiefWreath.action (e g) (c v)) :
    ChiefWreath.base ≤ (offenderSubgroup ρ).map e.toMonoidHom := by
  have hdim : Module.finrank (ZMod 2) W = 4 := by
    have hc : Nat.card W = 16 := by
      change Nat.card (Multiplicative W) = 16
      rw [Nat.card_congr c.toEquiv]
      change Nat.card (ZMod 2 → Fin 2 → ZMod 2) = 16
      simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
      rfl
    have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod,hc] at hp
    exact (Nat.pow_right_injective (by decide : 1 < 2) hp).symm
  apply ChiefWreath.base_le_of_transvections
  intro i b
  let a := e.symm (ChiefWreath.coordinate i (ChiefWreath.transvection b))
  have ha : a^2=1 := by
    apply e.injective
    rw [map_pow,map_one]
    change (e (e.symm _))^2=1
    rw [e.apply_symm_apply,←map_pow,(ChiefWreath.transvection_involution b).1,map_one]
  have hne : a ≠ 1 := by
    intro hh
    have hh' := congrArg e hh
    have hh'' : ChiefWreath.coordinate i (ChiefWreath.transvection b) = ChiefWreath.coordinate i 1 := by
      simpa [a] using hh'
    exact (ChiefWreath.transvection_involution b).2 (ChiefWreath.coordinate_injective i hh'')
  have hfix (v : W) :
      v ∈ fixedSpace ρ (zpowers a) ↔
        ChiefWreath.action (ChiefWreath.coordinate i (ChiefWreath.transvection b))
          (c (Multiplicative.ofAdd v)) = c (Multiplicative.ofAdd v) := by
    rw [mem_fixedSpace_zpowers_iff ρ a v]
    have hh := he a (Multiplicative.ofAdd v)
    change c (Multiplicative.ofAdd (ρ a v)) = _ at hh
    rw [e.apply_symm_apply] at hh
    rw [←hh,c.injective.eq_iff]
    rfl
  let E : fixedSpace ρ (zpowers a) ≃
      {v : ChiefWreath.Space // ChiefWreath.action
        (ChiefWreath.coordinate i (ChiefWreath.transvection b)) v = v} :=
    { toFun := fun v => ⟨c (Multiplicative.ofAdd v.val),(hfix v).mp v.property⟩
      invFun := fun v => ⟨(c.symm v.val).toAdd,(hfix _).mpr (by simpa using v.property)⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  have hcard : Nat.card (fixedSpace ρ (zpowers a)) = 8 := by
    rw [Nat.card_congr E,Nat.card_eq_fintype_card,ChiefWreath.transvection_fixed_card]
  have hfdim : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 3 := by
    have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (zpowers a))
    rw [Nat.card_zmod,hcard] at hp
    exact (Nat.pow_right_injective (by decide : 1 < 2) hp).symm
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1 := by
    rw [←fixedCodim_zpowers_eq_displacement_rank ρ a]
    have hh := fixedCodim_add_finrank ρ (zpowers a)
    rw [hdim,hfdim] at hh
    omega
  exact ⟨a,(bestOffender_of_involution_displacement_le_one ρ a ha hne hr).le_offenderSubgroup (ρ := ρ)
    (mem_zpowers a),e.apply_symm_apply _⟩

namespace ChiefWreath
noncomputable def baseEquiv : base ≃* (C2 → SL2) where
  toFun g := g.val.left
  invFun f := ⟨⟨f,1⟩,rfl⟩
  left_inv g := Subtype.ext (RegularWreathProduct.ext rfl g.property.symm)
  right_inv _ := rfl
  map_mul' g h := by
    funext i
    change (g.val*h.val).left i = g.val.left i * h.val.left i
    simp [RegularWreathProduct.mul_left, show g.val.right=1 from g.property]

theorem base_card : Nat.card base = 36 := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  rw [Nat.card_congr baseEquiv.toEquiv,Nat.card_fun,Nat.card_congr e.toEquiv]
  change Nat.card (Equiv.Perm (Fin 3)) ^ Nat.card (ZMod 2) = 36
  norm_num [Nat.card_perm,Nat.card_fin,Nat.card_zmod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
end ChiefWreath

namespace ChiefWreathCoordinates
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} (c : ChiefWreathCoordinates ρ)

/-- The literal plane in the original module, before passing to actor images. -/
def plane (i : ChiefWreath.C2) : Subgroup (Multiplicative W) :=
  (ChiefWreath.plane i).comap c.vectors.toMonoidHom

/-- The original actor centralizer factor, defined through its marked coordinate. -/
def factor (i : ChiefWreath.C2) : Subgroup D :=
  (ChiefWreath.factor i).comap c.actor

theorem vectors_action (g : D) (v : Multiplicative W) :
    c.vectors (Multiplicative.ofAdd (ρ g v.toAdd)) =
      ChiefWreath.action (c.actor g) (c.vectors v) := by
  funext i
  exact c.intertwines g v i

/-- The marked factor is exactly the centralizer of the opposite original plane. -/
theorem fixing_plane_eq (i : ChiefWreath.C2) :
    let := BinaryGroupAction.action ρ
    fixingSubgroup D (c.plane i : Set (Multiplicative W)) = c.factor (ChiefWreath.flip*i) := by
  let := BinaryGroupAction.action ρ
  ext g
  rw [mem_fixingSubgroup_iff]
  change (∀ v, c.vectors v ∈ ChiefWreath.plane i → Multiplicative.ofAdd (ρ g v.toAdd) = v) ↔
    c.actor g ∈ ChiefWreath.factor (ChiefWreath.flip*i)
  rw [←ChiefWreath.fixes_plane_iff]
  constructor
  · intro hg v hv
    obtain ⟨w,rfl⟩ := c.vectors.surjective v
    rw [←c.vectors_action,hg w hv]
  · intro hg v hv
    apply c.vectors.injective
    rw [c.vectors_action,hg _ hv]

/-- The natural chief planes remain complementary on the original vectors. -/
theorem planes_compl : IsCompl (c.plane 1) (c.plane ChiefWreath.flip) := by
  constructor
  · rw [disjoint_iff]
    change (ChiefWreath.plane 1).comap c.vectors.toMonoidHom ⊓
      (ChiefWreath.plane ChiefWreath.flip).comap c.vectors.toMonoidHom = ⊥
    rw [←comap_inf,ChiefWreath.plane_compl.inf_eq_bot]
    change c.vectors.toMonoidHom.ker = ⊥
    exact (MonoidHom.ker_eq_bot_iff _).mpr c.vectors.injective
  · apply codisjoint_iff.mpr
    change (ChiefWreath.plane 1).comap c.vectors.toMonoidHom ⊔
      (ChiefWreath.plane ChiefWreath.flip).comap c.vectors.toMonoidHom = ⊤
    rw [comap_sup_eq c.vectors.toMonoidHom _ _ c.vectors.surjective,ChiefWreath.plane_compl.sup_eq_top,comap_top]

noncomputable def planeEquiv (i : ChiefWreath.C2) : c.plane i ≃* ChiefWreath.plane i :=
  MulEquiv.ofBijective (c.vectors.toMonoidHom.subgroupComap (ChiefWreath.plane i))
    ⟨fun _ _ h => Subtype.ext (c.vectors.injective (congrArg Subtype.val h)),
      MonoidHom.subgroupComap_surjective_of_surjective _ _ c.vectors.surjective⟩

theorem plane_card (i : ChiefWreath.C2) : Nat.card (c.plane i) = 4 := by
  rw [Nat.card_congr (c.planeEquiv i).toEquiv,ChiefWreath.plane_card]

theorem factor_sup_eq_base : c.factor 1 ⊔ c.factor ChiefWreath.flip = ChiefWreath.base.comap c.actor := by
  change (ChiefWreath.factor 1).comap c.actor ⊔ (ChiefWreath.factor ChiefWreath.flip).comap c.actor = _
  rw [comap_sup_eq c.actor _ _ c.surjective,ChiefWreath.factor_sup_eq_base]

/-- Restriction of the actual actor map to one marked factor is onto SL₂(2). -/
theorem factor_image (i : ChiefWreath.C2) : (c.factor i).map c.actor = ChiefWreath.factor i :=
  map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr c.surjective]; exact le_top)

noncomputable def imageEquiv : actionImage ρ ≃* ChiefWreath.Actor :=
  (QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective).symm.trans
    (QuotientGroup.liftEquiv (actionHom ρ).ker c.surjective c.kernel.symm)

@[simp] theorem imageEquiv_actionHom (g : D) : c.imageEquiv (actionHom ρ g) = c.actor g := by
  change QuotientGroup.liftEquiv (actionHom ρ).ker c.surjective c.kernel.symm
    ((QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective).symm (actionHom ρ g)) = _
  rw [show (QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective).symm (actionHom ρ g) =
      QuotientGroup.mk' (actionHom ρ).ker g from
      (MulEquiv.symm_apply_eq _).mpr rfl]
  rfl

theorem factor_conj (g : D) (i : ChiefWreath.C2) :
    (c.factor i).map (MulAut.conj g).toMonoidHom =
      c.factor ((c.actor g).right*i) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change c.actor (g*x*g⁻¹) ∈ ChiefWreath.factor ((c.actor g).right*i)
    rw [map_mul,map_mul,map_inv]
    rw [← ChiefWreath.factor_map_conj]
    exact mem_map_of_mem _ hx
  · intro x hx
    refine ⟨g⁻¹*x*g,?_,by simp [mul_assoc]⟩
    change c.actor (g⁻¹*x*g) ∈ ChiefWreath.factor i
    rw [map_mul,map_mul,map_inv]
    change c.actor x ∈ ChiefWreath.factor ((c.actor g).right*i) at hx
    have hh := mem_map_of_mem (MulAut.conj (c.actor g)⁻¹).toMonoidHom hx
    rw [ChiefWreath.factor_map_conj] at hh
    simpa using hh

theorem base_le_image_offenders [Finite D] [FiniteDimensional (ZMod 2) W] :
    ChiefWreath.base ≤ (offenderSubgroup (imageRepresentation ρ)).map c.imageEquiv.toMonoidHom := by
  apply SmallActionsSource.base_le_image_offenders (imageRepresentation ρ) c.imageEquiv c.vectors
  intro g v
  obtain ⟨x,rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective g
  change c.vectors (Multiplicative.ofAdd (ρ x v.toAdd)) =
    ChiefWreath.action (c.imageEquiv (actionHom ρ x)) (c.vectors v)
  rw [c.imageEquiv_actionHom]
  exact c.vectors_action x v

end ChiefWreathCoordinates
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
