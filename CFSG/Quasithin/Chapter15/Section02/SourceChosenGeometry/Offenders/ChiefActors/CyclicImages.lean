module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ChiefMarking

/-!
# Cyclic offenders in the two marked natural factors

An elementary four-subgroup of the wreath base has a nontrivial kernel under
either coordinate projection: its order cannot divide the order-six target.
This gives an actual coordinate involution in each factor. On the natural
four-space each fixes a hyperplane, while the pair fixes a plane. Transport
through the literal action image therefore gives cyclic best offenders and
excludes strong offending by the whole four-image.

The finite certificates involve only SL₂(2) and its sixteen natural vectors.
The original-chief consumer is in InternalLift. Quotient involutions are
never treated as involutions of the original group.

Source: Aschbacher--Smith B.1.8(4), B.2.9(1), and Notation 15.2.9,
printed pp.70,77,1110; refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

/-- A four-subgroup in the base contains an actual involution in either factor. -/
theorem four_subgroup_coordinate (E : Subgroup Actor) [IsElementaryAbelian 2 E]
    (hEb : E ≤ base) (hE : Nat.card E = 4) (i : C2) :
    ∃ a : SL2, a^2=1 ∧ a≠1 ∧ coordinate i a ∈ E := by
  let f : E →* SL2 :=
    { toFun := fun g => g.val.left (flip*i)
      map_one' := rfl
      map_mul' := by
        intro g h
        change (g.val*h.val).left (flip*i) = _
        simp [RegularWreathProduct.mul_left,show g.val.right=1 from hEb g.property] }
  have hf : ¬ Function.Injective f := by
    intro hf
    have hd := Subgroup.card_dvd_of_injective f hf
    have hc : Nat.card SL2=6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hE,hc] at hd
    norm_num at hd
  have hker : f.ker ≠ ⊥ := fun hz => hf ((MonoidHom.ker_eq_bot_iff f).mp hz)
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  have hx0 : x.val.val.left (flip*i)=1 := x.property
  have hxf : x.val.val ∈ factor i := by
    apply (mem_factor _ _).mpr
    refine ⟨hEb x.val.property,?_⟩
    intro j hj
    have hji : j=flip*i := by
      rcases index_cases i with rfl | rfl <;> rcases index_cases j with rfl | rfl <;>
        simp_all [show flip*flip=1 by decide]
    exact hji ▸ hx0
  obtain ⟨a,ha⟩ := hxf
  refine ⟨a,?_,?_,ha.symm ▸ x.val.property⟩
  · apply coordinate_injective i
    rw [map_pow,map_one,ha]
    exact elemPow_eq_one_of_isElementaryAbelian x.val.val x.val.property
  · intro hz
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    rw [←ha,hz,map_one]
    rfl

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 10000 in
private theorem coordinate_involution_fixed : ∀ (i : C2) (a : SL2),
    a^2=1 → a≠1 →
      Fintype.card {v : Space // action (coordinate i a) v=v}=8 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 10000 in
private theorem coordinate_pair_fixed_card : ∀ (a b : SL2),
    a^2=1 → a≠1 → b^2=1 → b≠1 →
      Fintype.card {v : Space // action (coordinate 1 a) v=v ∧
        action (coordinate flip b) v=v}=4 := by
  decide +kernel

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

/-- A coordinate involution in the faithful chief image is a cyclic best offender. -/
theorem coordinate_bestOffender (c : ChiefWreathCoordinates ρ)
    (i : ChiefWreath.C2) (a : ChiefWreath.SL2) (ha : a^2=1) (hn : a≠1) :
    let b := c.imageEquiv.symm (ChiefWreath.coordinate i a)
    Nat.card (zpowers b)=2 ∧ IsBestOffender (imageRepresentation ρ) (zpowers b) := by
  let b := c.imageEquiv.symm (ChiefWreath.coordinate i a)
  have hb : b^2=1 := by
    apply c.imageEquiv.injective
    rw [map_pow,map_one,c.imageEquiv.apply_symm_apply,←map_pow,ha,map_one]
  have hbn : b≠1 := by
    intro hh
    have hh' := congrArg c.imageEquiv hh
    have hh'' : ChiefWreath.coordinate i a = ChiefWreath.coordinate i 1 := by simpa [b] using hh'
    exact hn (ChiefWreath.coordinate_injective i hh'')
  have hc : Nat.card (zpowers b)=2 := by rw [Nat.card_zpowers]; exact orderOf_eq_prime hb hbn
  refine ⟨hc,bestOffender_of_involution_displacement_le_one (imageRepresentation ρ) b hb hbn ?_⟩
  have hdim : Module.finrank (ZMod 2) W=4 := by
    have hcard : Nat.card W=16 := by
      change Nat.card (Multiplicative W)=16
      rw [Nat.card_congr c.vectors.toEquiv]
      change Nat.card (ZMod 2 → Fin 2 → ZMod 2)=16
      simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
      rfl
    have hp := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=W)
    rw [Nat.card_zmod,hcard] at hp
    exact (Nat.pow_right_injective (by decide : 1<2) hp).symm
  have he (g : actionImage ρ) (v : Multiplicative W) :
      c.vectors (Multiplicative.ofAdd ((imageRepresentation ρ) g v.toAdd)) =
        ChiefWreath.action (c.imageEquiv g) (c.vectors v) := by
    obtain ⟨x,rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective g
    change c.vectors (Multiplicative.ofAdd (ρ x v.toAdd)) =
      ChiefWreath.action (c.imageEquiv (actionHom ρ x)) (c.vectors v)
    rw [c.imageEquiv_actionHom]
    exact c.vectors_action x v
  have hfix (v : W) : v∈fixedSpace (imageRepresentation ρ) (zpowers b) ↔
      ChiefWreath.action (ChiefWreath.coordinate i a) (c.vectors (Multiplicative.ofAdd v)) =
        c.vectors (Multiplicative.ofAdd v) := by
    rw [mem_fixedSpace_zpowers_iff]
    have hh := he b (Multiplicative.ofAdd v)
    rw [c.imageEquiv.apply_symm_apply] at hh
    rw [←hh,c.vectors.injective.eq_iff]
    rfl
  let F : fixedSpace (imageRepresentation ρ) (zpowers b) ≃
      {v : ChiefWreath.Space // ChiefWreath.action (ChiefWreath.coordinate i a) v=v} :=
    { toFun := fun v => ⟨c.vectors (Multiplicative.ofAdd v.val),(hfix v).mp v.property⟩
      invFun := fun v => ⟨(c.vectors.symm v.val).toAdd,(hfix _).mpr (by simpa using v.property)⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  have hcard : Nat.card (fixedSpace (imageRepresentation ρ) (zpowers b))=8 := by
    rw [Nat.card_congr F,Nat.card_eq_fintype_card,ChiefWreath.coordinate_involution_fixed i a ha hn]
  have hfdim : Module.finrank (ZMod 2) (fixedSpace (imageRepresentation ρ) (zpowers b))=3 := by
    have hp := Module.natCard_eq_pow_finrank (K:=ZMod 2)
      (V:=fixedSpace (imageRepresentation ρ) (zpowers b))
    rw [Nat.card_zmod,hcard] at hp
    exact (Nat.pow_right_injective (by decide : 1<2) hp).symm
  rw [←fixedCodim_zpowers_eq_displacement_rank]
  have hh := fixedCodim_add_finrank (imageRepresentation ρ) (zpowers b)
  rw [hdim,hfdim] at hh
  omega

/-- Every four-image in the base contains an order-two best offender on the
literal module. No involution of D is obtained by lifting a quotient involution. -/
theorem four_image_contains_cyclic_bestOffender (c : ChiefWreathCoordinates ρ)
    (A : Subgroup D) [IsElementaryAbelian 2 A] (i : ChiefWreath.C2)
    (hbase : A.map c.actor ≤ ChiefWreath.base)
    (hcard : Nat.card (A.map c.actor)=4) :
    ∃ E : Subgroup (actionImage ρ), E ≤ actionSubgroup ρ A ∧ Nat.card E=2 ∧
      IsBestOffender (imageRepresentation ρ) E ∧
      E ≤ (ChiefWreath.factor i).comap c.imageEquiv.toMonoidHom := by
  let : IsElementaryAbelian 2 (A.map c.actor) := IsElementaryAbelian.map c.actor
  obtain ⟨a,ha,hn,hm⟩ := ChiefWreath.four_subgroup_coordinate (A.map c.actor) hbase hcard i
  let b := c.imageEquiv.symm (ChiefWreath.coordinate i a)
  obtain ⟨g,hg,hga⟩ := hm
  have hb : b=actionHom ρ g := by
    apply c.imageEquiv.injective
    rw [c.imageEquiv.apply_symm_apply,c.imageEquiv_actionHom,hga]
  obtain ⟨hc,hbest⟩ := c.coordinate_bestOffender i a ha hn
  refine ⟨zpowers b,zpowers_le.mpr ?_,hc,hbest,zpowers_le.mpr ?_⟩
  · rw [hb]
    exact mem_map_of_mem _ hg
  · change c.imageEquiv b ∈ ChiefWreath.factor i
    rw [c.imageEquiv.apply_symm_apply]
    exact ⟨a,rfl⟩
omit [Finite D] in
/-- A four-image in the paired base is not a strong offender. This uses the
actual two coordinate involutions, not a lifting assertion in D. -/
theorem four_image_not_strong (c : ChiefWreathCoordinates ρ)
    (A : Subgroup D) [IsElementaryAbelian 2 A]
    (hbase : A.map c.actor ≤ ChiefWreath.base)
    (hcard : Nat.card (A.map c.actor)=4) :
    ¬ IsStrongOffender (imageRepresentation ρ) (actionSubgroup ρ A) := by
  let : IsElementaryAbelian 2 (A.map c.actor) := IsElementaryAbelian.map c.actor
  obtain ⟨a,ha,han,g,hg,hga⟩ := ChiefWreath.four_subgroup_coordinate (A.map c.actor) hbase hcard 1
  obtain ⟨b,hb,hbn,k,hk,hkb⟩ := ChiefWreath.four_subgroup_coordinate (A.map c.actor) hbase hcard ChiefWreath.flip
  let F := {v : ChiefWreath.Space // ChiefWreath.action (ChiefWreath.coordinate 1 a) v=v ∧
    ChiefWreath.action (ChiefWreath.coordinate ChiefWreath.flip b) v=v}
  let f : fixedSpace ρ A → F := fun v =>
    ⟨c.vectors (Multiplicative.ofAdd v.val),by
      constructor
      · rw [←hga,←c.vectors_action]
        exact congrArg (fun w => c.vectors (Multiplicative.ofAdd w)) (v.property ⟨g,hg⟩)
      · rw [←hkb,←c.vectors_action]
        exact congrArg (fun w => c.vectors (Multiplicative.ofAdd w)) (v.property ⟨k,hk⟩)⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact c.vectors.injective (congrArg Subtype.val huv)
  have hc : Nat.card (fixedSpace ρ A) ≤ 4 := by
    have hF : Nat.card F=4 := by
      dsimp only [F]
      rw [Nat.card_eq_fintype_card,ChiefWreath.coordinate_pair_fixed_card a b ha han hb hbn]
    exact (Nat.card_le_card_of_injective f hf).trans_eq hF
  have hd : Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 2 := by
    have hp := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=fixedSpace ρ A)
    rw [Nat.card_zmod] at hp
    rw [hp] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
      (show 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 2^2 from hc)
  have hdim : Module.finrank (ZMod 2) W=4 := by
    have hc : Nat.card W=16 := by
      change Nat.card (Multiplicative W)=16
      rw [Nat.card_congr c.vectors.toEquiv]
      change Nat.card (ZMod 2 → Fin 2 → ZMod 2)=16
      simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
      rfl
    have hp := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=W)
    rw [Nat.card_zmod,hc] at hp
    exact (Nat.pow_right_injective (by decide : 1<2) hp).symm
  have himage : Nat.card (actionSubgroup ρ A)=4 := by
    change Nat.card (A.map (actionHom ρ))=4
    rw [←Subgroup.relIndex_ker,←c.kernel]
    rwa [←Subgroup.relIndex_ker] at hcard
  rintro ⟨_,hlt⟩
  rw [fixedCodim_actionSubgroup,rank,himage] at hlt
  have hh := fixedCodim_add_finrank ρ A
  rw [hdim] at hh
  rw [show Nat.log 2 4=2 by decide] at hlt
  omega

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
