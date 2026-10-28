module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Action.Displacement

/-!
# The centralizer of V has inner actor image

The source t exchanges the natural and dual summands. Index two of the
inner subgroup consequently makes every outer actor exchange them. Such
an actor injects the eight-element natural summand into its displacement
subgroup. The order-four displacement in 15.3.53 therefore makes V inner.
Faithfulness of the natural representation supplies a nonzero pure natural
displacement vector. An element centralizing V fixes that vector, because
[U,V] ≤ V, and hence cannot be outer. Once U = Q_H, the previously proved
U ≤ K lifts this innerness to the required C_T(V) ≤ K.

All displacement subgroups and actions below are formed on the literal U/Z.
The argument uses no assumed image-generation or residual-containment clause.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.53(2), 15.3.58(1,3), and 15.3.59, printed pp.1146–1150.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open Matrix.PSL3Two
open scoped commutatorElement

variable {G : Type*} [Group G] {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- A pure natural vector in the actual quotient, using the supplied coordinates. -/
@[expose] def naturalVector (d : RecognizedAction T Z ZS V t) (v : BinaryLinearThree.Vector) :
    VectorQuotient Z ZS := d.coordinates.symm (Multiplicative.ofAdd (v, 0))

/-- The image of the actual subgroup [U,V] in the literal U/Z. -/
@[expose] def vectorDisplacement (Z ZS V : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal] :
    Subgroup (VectorQuotient Z ZS) :=
  (⁅closureU Z ZS, V⁆.subgroupOf (closureU Z ZS)).map (QuotientGroup.mk' _)

/-- Every action displacement is the image of an actual ambient commutator. -/
theorem quotient_displacement_mem (v : centralizerH Z) (hv : (v : G) ∈ V)
    (w : VectorQuotient Z ZS) :
    quotientAction Z ZS v w * w⁻¹ ∈ vectorDisplacement Z ZS V := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w
  refine ⟨closureCommutator v u, ?_, quotient_closureCommutator v u⟩
  change ⁅(v : G), (u : G)⁆ ∈ ⁅closureU Z ZS, V⁆
  rw [commutator_comm]
  exact commutator_mem_commutator hv u.property

/-- Centralizing V fixes its displacement pointwise when [U,V] ≤ V. -/
theorem vectorDisplacement_fixed (h : centralizerH Z)
    (hh : (h : G) ∈ centralizer (V : Set G))
    (hd : ⁅closureU Z ZS, V⁆ ≤ V)
    (w : VectorQuotient Z ZS) (hw : w ∈ vectorDisplacement Z ZS V) :
    quotientAction Z ZS h w = w := by
  obtain ⟨u, hu, rfl⟩ := hw
  rw [quotientAction_mk]
  apply congrArg (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)))
  apply Subtype.ext
  change (h : G) * (u : G) * (h : G)⁻¹ = (u : G)
  have hc : (u : G) * (h : G) = (h : G) * (u : G) := hh _ (hd hu)
  rw [← hc, mul_inv_cancel_right]

/-- The supplied summand swap makes the actual t-actor outer. -/
theorem source_t_actor_not_inner (d : RecognizedAction T Z ZS V t) :
    d.actorEquiv (actorProjection Z ⟨t, d.t_mem_H⟩) ∉ MulAut.innerSubgroup SL := by
  rintro ⟨g, hg⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : BinaryLinearThree.Vector)
  have he := congrArg Prod.fst (d.equivariant ⟨t, d.t_mem_H⟩ g hg.symm (naturalVector d v))
  have hs := d.swaps_natural v
  have hz : BinaryLinearThree.W g v = 0 := by
    simpa only [naturalVector, MulEquiv.apply_symm_apply, toAdd_ofAdd] using he.symm.trans hs
  exact hv ((BinaryLinearThree.W.apply_bijective g).injective (hz.trans (map_zero _).symm))

theorem quotientAction_eq_of_actor_eq
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (h k : centralizerH Z) (he : actorProjection Z h = actorProjection Z k) :
    quotientAction Z ZS h = quotientAction Z ZS k := by
  exact congrArg (fun a : ActorQuotient Z =>
    (actorQuotientEquivRange Z ZS hkernel a : MulAut (VectorQuotient Z ZS))) he

variable [Finite G]

/-- Every outer actor carries the natural summand into the dual summand. -/
theorem outer_actor_swaps_natural (d : RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (h : centralizerH Z)
    (hout : d.actorEquiv (actorProjection Z h) ∉ MulAut.innerSubgroup SL)
    (v : BinaryLinearThree.Vector) :
    (d.coordinates (quotientAction Z ZS h (naturalVector d v))).toAdd.1 = 0 := by
  let th : centralizerH Z := ⟨t, d.t_mem_H⟩
  let a := d.actorEquiv (actorProjection Z h)
  let b := d.actorEquiv (actorProjection Z th)
  have ht : b ∉ MulAut.innerSubgroup SL := source_t_actor_not_inner d
  have hm : a * b⁻¹ ∈ MulAut.innerSubgroup SL :=
    (mul_mem_iff_of_index_two Automorphisms.card_outer_sl).mpr
      (iff_of_false hout (fun hb => ht (inv_mem_iff.mp hb)))
  obtain ⟨g, hg⟩ := hm
  obtain ⟨k, hk⟩ := exists_residual_lift_inner Z d.actorEquiv g
  let kh := inclusion (residual_le_H Z) k
  have he : actorProjection Z h = actorProjection Z (kh * th) := by
    apply d.actorEquiv.injective
    rw [map_mul, map_mul]
    change a = d.actorEquiv (residualActor Z k) * b
    rw [hk, hg, inv_mul_cancel_right]
  rw [quotientAction_eq_of_actor_eq hkernel h (kh * th) he, map_mul, MulAut.mul_apply]
  have hc := d.equivariant kh g hk (quotientAction Z ZS th (naturalVector d v))
  rw [hc]
  change BinaryLinearThree.W g
    (d.coordinates (quotientAction Z ZS th (naturalVector d v))).toAdd.1 = 0
  have hs : (d.coordinates (quotientAction Z ZS th (naturalVector d v))).toAdd.1 = 0 :=
    d.swaps_natural v
  rw [hs, map_zero]

/-- A displacement subgroup smaller than the natural summand excludes an outer V-actor. -/
theorem actor_inner_of_displacement_card_lt_eight (d : RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hcard : Nat.card (vectorDisplacement Z ZS V) < 8)
    (h : centralizerH Z) (hv : (h : G) ∈ V) :
    d.actorEquiv (actorProjection Z h) ∈ MulAut.innerSubgroup SL := by
  by_contra hout
  let f : BinaryLinearThree.Vector → vectorDisplacement Z ZS V := fun v =>
    ⟨quotientAction Z ZS h (naturalVector d v) * (naturalVector d v)⁻¹,
      quotient_displacement_mem h hv _⟩
  have hc (v : BinaryLinearThree.Vector) : (d.coordinates (f v).val).toAdd.1 = -v := by
    change (d.coordinates (quotientAction Z ZS h (naturalVector d v) *
      (naturalVector d v)⁻¹)).toAdd.1 = -v
    rw [map_mul, map_inv]
    simp only [toAdd_mul, toAdd_inv, Prod.fst_add, Prod.fst_neg]
    rw [outer_actor_swaps_natural d hkernel h hout]
    simp only [naturalVector, MulEquiv.apply_symm_apply, toAdd_ofAdd, zero_add]
  have hf : Function.Injective f := by
    intro v w he
    have he' := congrArg (fun x : vectorDisplacement Z ZS V => (d.coordinates x.val).toAdd.1) he
    rw [hc, hc] at he'
    exact neg_injective he'
  have hle := Nat.card_le_card_of_injective f hf
  have hcV : Nat.card BinaryLinearThree.Vector = 8 := by
    simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]
  rw [hcV] at hle
  omega


/-- The nontrivial V-action has a nonzero pure natural displacement vector. -/
theorem exists_natural_displacement (d : RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hcard : Nat.card (vectorDisplacement Z ZS V) < 8)
    (hVH : V ≤ centralizerH Z) (hVQ : ¬ V ≤ coreQ Z) :
    ∃ v : BinaryLinearThree.Vector, v ≠ 0 ∧
      naturalVector d v ∈ vectorDisplacement Z ZS V := by
  classical
  obtain ⟨v, hv, hvQ⟩ := Set.not_subset.mp hVQ
  let vh : centralizerH Z := ⟨v, hVH hv⟩
  obtain ⟨g, hg⟩ := actor_inner_of_displacement_card_lt_eight d hkernel hcard vh hv
  have hgone : g ≠ 1 := by
    intro he
    apply hvQ
    apply (actorProjection_eq_one_iff Z vh).mp
    apply d.actorEquiv.injective
    rw [← hg, he, map_one, map_one]
  have hm : ∃ x : BinaryLinearThree.Vector, BinaryLinearThree.W g x ≠ x := by
    by_contra hn
    push Not at hn
    apply hgone
    apply BinaryLinearThree.natural_injective
    apply LinearMap.ext
    intro x
    simpa only [map_one, Module.End.one_apply] using hn x
  obtain ⟨x, hx⟩ := hm
  refine ⟨BinaryLinearThree.W g x - x, sub_ne_zero.mpr hx, ?_⟩
  have he : quotientAction Z ZS vh (naturalVector d x) * (naturalVector d x)⁻¹ =
      naturalVector d (BinaryLinearThree.W g x - x) := by
    apply d.coordinates.injective
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [d.equivariant vh g hg.symm]
    simp only [naturalVector, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      map_zero, Prod.mk_sub_mk, sub_self]
  exact he ▸ quotient_displacement_mem vh hv (naturalVector d x)

/-- Every element of H centralizing V has inner actor image. -/
theorem centralizer_actor_inner (d : RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hcard : Nat.card (vectorDisplacement Z ZS V) < 8)
    (hVH : V ≤ centralizerH Z) (hVQ : ¬ V ≤ coreQ Z)
    (hd : ⁅closureU Z ZS, V⁆ ≤ V)
    (h : centralizerH Z) (hh : (h : G) ∈ centralizer (V : Set G)) :
    d.actorEquiv (actorProjection Z h) ∈ MulAut.innerSubgroup SL := by
  obtain ⟨v, hv, hvm⟩ := exists_natural_displacement d hkernel hcard hVH hVQ
  by_contra hout
  have he := congrArg (fun w : VectorQuotient Z ZS => (d.coordinates w).toAdd.1)
    (vectorDisplacement_fixed h hh hd (naturalVector d v) hvm)
  rw [outer_actor_swaps_natural d hkernel h hout] at he
  apply hv
  simpa only [naturalVector, MulEquiv.apply_symm_apply, toAdd_ofAdd] using he.symm

/-- Once U = Q_H, the centralizer in T of V lies in the actual residual. -/
theorem sylow_centralizer_le_residual (d : RecognizedAction T Z ZS V t)
    [IsExtraspecial 2 (closureU Z ZS)]
    (hTH : T ≤ centralizerH Z)
    (hcenter : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hcard : Nat.card (vectorDisplacement Z ZS V) < 8)
    (hVH : V ≤ centralizerH Z) (hVQ : ¬ V ≤ coreQ Z)
    (hd : ⁅closureU Z ZS, V⁆ ≤ V) (hUQ : closureU Z ZS = coreQ Z) :
    T ⊓ centralizer (V : Set G) ≤ residualK Z := by
  have hUH : closureU Z ZS ≤ centralizerH Z := hUQ.le.trans (map_subtype_le _)
  have hQK : coreQ Z ≤ residualK Z := hUQ.symm.le.trans (closure_le_residual d hUH hcenter)
  intro c hc
  exact mem_residual_of_actor_inner Z d.actorEquiv hQK ⟨c, hTH hc.1⟩
    (centralizer_actor_inner d hkernel hcard hVH hVQ hd ⟨c, hTH hc.1⟩ hc.2)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
