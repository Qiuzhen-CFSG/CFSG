module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Representative
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldModels
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Inputs and faithful embeddings for the field-component sieve

Keep the selected component K normal relative to its SQTK overgroup H.
Conjugation by an involution v in H defines an automorphism of K even when
v is outside K. Its fixed subgroup is exactly K ∩ C_G(v), so the supplied
ordinary component retains its actual PSL₃(2) isomorphism there.

The PSL₃(2) component also embeds faithfully in K/Z(K): the kernel is normal
in this simple group, and a nontrivial kernel would make its faithful image
central and hence abelian. Lagrange therefore gives 168 dividing |K/Z(K)|.
These are preparation lemmas, not the three-model sieve or a cover classification.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of 15.3.38,
printed p.1137; Theorem C, p.33; A.3.6, pp.43--45; A.3.18, pp.51--52.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
universe u
variable {G : Type u} [Group G]

/-- The exact local inputs on printed p.1137, retaining relative normality and
the actual centralizer component isomorphism. No model conclusion is a field. -/
structure Input (H K : Subgroup G) (v : G) where
  le : K ≤ H
  sqtk : IsSQTK CFSG.KnownSimple.IsKnownSimple H
  component : IsComponent H (K.subgroupOf H)
  normal : (K.subgroupOf H).Normal
  rank : primeRank 3 K = 2
  involution_mem : v ∈ H
  involution_order : orderOf v = 2
  centralizerComponent : Subgroup (K ⊓ centralizer ({v} : Set G) : Subgroup G)
  centralizerComponent_isComponent :
    IsComponent (K ⊓ centralizer ({v} : Set G) : Subgroup G) centralizerComponent
  centralizerComponent_equiv : centralizerComponent ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)

variable {H K : Subgroup G} {v : G} (d : Input H K v)
include d

/-- Relative componenthood gives intrinsic quasisimplicity of K. -/
theorem Input.quasisimple : IsQuasisimple K := by
  let := d.component.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe d.le)

/-- The original SQTK hypothesis restricts to K. -/
theorem Input.component_sqtk [Finite G] : IsSQTK CFSG.KnownSimple.IsKnownSimple K :=
  (IsSQTK.equiv (subgroupOfEquivOfLe d.le)).mp (d.sqtk.subgroup _)

/-- Relative normality supplies the normalizer needed for conjugation. -/
theorem Input.le_normalizer : H ≤ normalizer (K : Set G) :=
  (normal_subgroupOf_iff_le_normalizer d.le).mp d.normal

/-- Conjugation by H on K; K need not be normal in the ambient group. -/
@[expose] def Input.action : H →* MulAut K :=
  K.normalizerMonoidHom.comp (inclusion d.le_normalizer)

/-- The action of the given involution, which need not lie in K. -/
@[expose] def Input.involutionAction : MulAut K := d.action ⟨v, d.involution_mem⟩

/-- The action is literal ambient conjugation. -/
theorem Input.involutionAction_apply (k : K) :
    (d.involutionAction k : G) = v * (k : G) * v⁻¹ := rfl

/-- The induced automorphism has square one. -/
theorem Input.involutionAction_sq : d.involutionAction ^ 2 = 1 := by
  have hv : (⟨v, d.involution_mem⟩ : H) ^ 2 = 1 :=
    Subtype.ext (d.involution_order ▸ pow_orderOf_eq_one v)
  exact (map_pow d.action _ 2).symm.trans (by rw [hv, map_one])

/-- The relative element centralizer is the actual fixed subgroup of the action. -/
@[expose] def Input.centralizerEquivFixed :
    (K ⊓ centralizer ({v} : Set G) : Subgroup G) ≃* d.involutionAction.fixedSubgroup where
  toFun x := ⟨⟨x, x.property.1⟩, by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    change v * (x : G) * v⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp x.property.2).symm⟩
  invFun x := ⟨(x : K), (x : K).property, by
    apply mem_centralizer_singleton_iff.mpr
    have hx := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Transport the ordinary component and its PSL₃(2) isomorphism to the fixed subgroup. -/
theorem Input.exists_fixed_component :
    ∃ D : Subgroup d.involutionAction.fixedSubgroup,
      IsComponent d.involutionAction.fixedSubgroup D ∧
      Nonempty (D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let e := d.centralizerEquivFixed
  exact ⟨d.centralizerComponent.map e.toMonoidHom,
    d.centralizerComponent_isComponent.map_equiv e,
    ⟨(d.centralizerComponent.equivMapOfInjective e.toMonoidHom e.injective).symm.trans
      d.centralizerComponent_equiv⟩⟩


/-- The given ordinary component embedded in K through the two inclusions. -/
@[expose] def Input.componentEmbedding : d.centralizerComponent →* K :=
  (inclusion (show K ⊓ centralizer ({v} : Set G) ≤ K from inf_le_left)).comp
    d.centralizerComponent.subtype

/-- The original component embedding is faithful. -/
theorem Input.componentEmbedding_injective : Function.Injective d.componentEmbedding :=
  (inclusion_injective inf_le_left).comp d.centralizerComponent.subtype_injective

/-- A simple nonabelian component meets the center of K trivially, so its
embedding survives the central quotient. -/
theorem Input.componentQuotientEmbedding_injective :
    Function.Injective ((QuotientGroup.mk' (center K)).comp d.componentEmbedding) := by
  let : IsSimpleGroup d.centralizerComponent :=
    (MulEquiv.isSimpleGroup_congr d.centralizerComponent_equiv).mpr
      (Atlas.psl_simple_high_rank 3 (by decide))
  let := d.centralizerComponent_isComponent.2
  let f := (QuotientGroup.mk' (center K)).comp d.componentEmbedding
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hz (x : d.centralizerComponent) : d.componentEmbedding x ∈ center K := by
      apply (QuotientGroup.eq_one_iff _).mp
      have hx : x ∈ f.ker := ht ▸ mem_top x
      exact hx
    exact (Group.IsPerfect.not_isMulCommutative d.centralizerComponent
      (IsMulCommutative.of_comm fun a b => d.componentEmbedding_injective (by
        simpa only [map_mul] using mem_center_iff.mp (hz b) (d.componentEmbedding a)))).elim

/-- The literal PSL₃(2) carrier embedded in K/Z(K). -/
@[expose] def Input.psl3TwoQuotientEmbedding :
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) →* (K ⧸ center K) :=
  ((QuotientGroup.mk' (center K)).comp d.componentEmbedding).comp
    d.centralizerComponent_equiv.symm.toMonoidHom

/-- The model embedding in the central quotient is faithful. -/
theorem Input.psl3TwoQuotientEmbedding_injective :
    Function.Injective d.psl3TwoQuotientEmbedding :=
  d.componentQuotientEmbedding_injective.comp d.centralizerComponent_equiv.symm.injective

/-- Every possible central quotient has order divisible by 168. -/
theorem Input.centralQuotient_card_dvd [Finite G] : 168 ∣ Nat.card (K ⧸ center K) := by
  simpa only [Matrix.PSL3Two.card_PSL] using
    card_dvd_of_injective d.psl3TwoQuotientEmbedding d.psl3TwoQuotientEmbedding_injective

omit d in
/-- The order of the embedded odd center is its intrinsic order. -/
theorem card_oddCenterIn (K : Subgroup G) :
    Nat.card (oddCenterIn K) = Nat.card (pPrimeCore 2 (center K)) := by
  exact (Nat.card_congr ((pPrimeCore 2 (center K)).equivMapOfInjective
    (K.subtype.comp (center K).subtype)
    (K.subtype_injective.comp (center K).subtype_injective)).toEquiv).symm


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
