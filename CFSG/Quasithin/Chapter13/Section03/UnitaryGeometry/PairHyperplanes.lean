module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.OffenderIntersections
public import Theory.Representation.G2BinaryIsotropicThree.PairHyperplanes


/-!
# Intrinsic actor hyperplanes on the original unitary module

The sharp offender rank determines the actor centralizer as well as the
module centralizer. Once the actual common three-space is marked, its
pointwise stabilizer identifies the full actor image with ABC. For each
original normalizer element the concrete singular-parameter test becomes
exactly the source condition R<C_V(g); all conjugation maps and coordinates
are retained. This discharges the first intrinsic U₅ description without
assuming a rank or a centralizer conclusion.

Source: Aschbacher–Smith 13.3.12(4), printed p.890. The prior offender and
common-space marking are supplied by the preceding intersection/source
conjugator work; completing the simultaneous flag alignment remains separate.
-/

public section

open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] [Finite G] {V U : Subgroup G}
  [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]

omit [Finite G] in
private theorem marked_action_injective
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v)) : Function.Injective f := by
  intro a b hab
  apply automizerRepresentation_injective V
  apply LinearMap.ext
  intro v
  apply E.injective
  rw [he,he,hab]

theorem actor_centralizer_card_of_offender
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hA : IsOffender rho ((inducedAutomizer V U).map f))
    (hc : ⁅V,U⁆≤V⊓U) (hU : Nat.card U=64) : Nat.card (U⊓centralizer (V:Set G) : Subgroup G)=8 := by
  have hUN : U≤normalizer (V:Set G) := le_normalizer_iff_commutator_le_left.mpr (hc.trans inf_le_left)
  have hnative : rank ((inducedAutomizer V U).map f)=3 :=
    Atlas.G2.NaturalOffenders.natural_offender_rank (F:=K) (n:=1) (by norm_num) (by decide) _
      ((Atlas.G2.NaturalOffenders.natural_offender_iff _).mpr hA)
  rw [rank_map_injective f (marked_action_injective E f he),rank_inducedAutomizer V U hUN] at hnative
  have hdimU : finrank (ZMod 2) (Additive U)=6 := by
    have hh := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive U)
    change Nat.card U=_ at hh
    rw [Nat.card_zmod,hU] at hh
    exact Nat.pow_right_injective (by decide : 1<(2:ℕ)) hh.symm
  have hdim := ambientSpace_finrank_add_corank (V:=U) (U⊓centralizer (V:Set G))
  rw [hnative,hdimU] at hdim
  have hr : finrank (ZMod 2) (ambientSpace (V:=U) (U⊓centralizer (V:Set G)))=3 := by omega
  have hh := Module.natCard_eq_pow_finrank (K:=ZMod 2)
    (V:=ambientSpace (V:=U) (U⊓centralizer (V:Set G)))
  rw [hr,Nat.card_zmod] at hh
  have hcE : Nat.card (ambientSpace (V:=U) (U⊓centralizer (V:Set G)))=
      Nat.card (U⊓centralizer (V:Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show U⊓centralizer (V:Set G)≤U from inf_le_left)).toEquiv
  rw [←hcE,hh]
  decide

theorem actor_centralizer_eq_intersection_of_offender
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hA : IsOffender rho ((inducedAutomizer V U).map f))
    (hc : ⁅V,U⁆≤V⊓U) (hU : Nat.card U=64) : U⊓centralizer (V:Set G)=V⊓U := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
    (le_inf inf_le_right (inf_le_left.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)))
  rw [actor_centralizer_card_of_offender E f he hA hc hU,
    intersection_card_of_offender E f he hA hc]

omit [Finite G] in
theorem image_eq_elementary_of_intersection_marking
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hA : IsOffender rho ((inducedAutomizer V U).map f))
    (hUN : U≤normalizer (V:Set G))
    (hR : (ambientSpace (V:=V) (V⊓U)).map E.toLinearMap=target false) :
    (inducedAutomizer V U).map f=Atlas.G2.EvenTwoRank.elementary K := by
  have hfix : target false≤fixedSpace rho ((inducedAutomizer V U).map f) := by
    rw [←hR,←fixedSpace_map_equivariant (automizerRepresentation V) rho f E he]
    apply Submodule.map_mono
    intro v hv
    apply (mem_fixedSpace_inducedAutomizer V U hUN v).mpr
    exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance) hv.2
  have hle : (inducedAutomizer V U).map f≤Atlas.G2.EvenTwoRank.elementary K := by
    intro a ha
    apply (pointwise_target_eq_elementary a).mp
    intro v hv
    exact hfix hv ⟨a,ha⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  have hr : rank ((inducedAutomizer V U).map f)=3 :=
    Atlas.G2.NaturalOffenders.natural_offender_rank (F:=K) (n:=1) (by norm_num) (by decide) _
      ((Atlas.G2.NaturalOffenders.natural_offender_iff _).mpr hA)
  rw [Atlas.G2.EvenTwoRank.elementary_card,Nat.card_zmod,hA.1.card_eq_two_pow_rank,hr]


omit [Finite G] [IsElementaryAbelian 2 U] in
theorem actor_hyperplane_criterion
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (R : Subgroup G) (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false)
    (g : normalizer (V:Set G)) (q : Three)
    (hq : f (V.normalizerMonoidHom.rangeRestrict g)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd q)) :
    (∃v∈V,v∉R ∧ Commute g.val v) ↔ q 2=0 := by
  rw [←elementary_fixed_outside_target]
  have hmem (v : Additive V) : E v∈target false ↔ v.toMul.val∈R := by
    rw [←hR]
    constructor
    · rintro ⟨w,hw,heq⟩
      exact E.injective heq ▸ hw
    · intro hv
      exact ⟨v,hv,rfl⟩
  have hfix (v : Additive V) :
      rho (Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd q)) (E v)=E v ↔
        Commute g.val v.toMul.val := by
    rw [←hq,←he]
    constructor
    · intro hh
      have hv := congrArg (fun v : Additive V=>v.toMul.val) (E.injective hh)
      change (V.normalizerMonoidHom g v.toMul).val=v.toMul.val at hv
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hv
      exact mul_inv_eq_iff_eq_mul.mp hv
    · intro hh
      apply congrArg E
      change Additive.ofMul (V.normalizerMonoidHom g v.toMul)=v
      apply Additive.toMul.injective
      apply Subtype.ext
      change (V.normalizerMonoidHom g v.toMul).val=v.toMul.val
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe,hh.eq,mul_inv_cancel_right]
  constructor
  · rintro ⟨v,hv,hr,hg⟩
    let w : Additive V := Additive.ofMul ⟨v,hv⟩
    exact ⟨E w,fun hh=>hr ((hmem w).mp hh),(hfix w).mpr hg⟩
  · rintro ⟨w,hw,hg⟩
    obtain ⟨v,rfl⟩ := E.surjective w
    exact ⟨v.toMul.val,v.toMul.property,fun hh=>hw ((hmem v).mpr hh),(hfix v).mp hg⟩


omit [Finite G] [IsElementaryAbelian 2 U] in
theorem actor_strict_centralizer_criterion
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (R : Subgroup G) (hRV : R≤V)
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false)
    (g : normalizer (V:Set G)) (q : Three)
    (hq : f (V.normalizerMonoidHom.rangeRestrict g)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd q)) :
    R<V⊓centralizer ({g.val}:Set G) ↔ q 2=0 := by
  have hfix : R≤V⊓centralizer ({g.val}:Set G) := by
    intro v hv
    refine ⟨hRV hv,?_⟩
    let w : Additive V := Additive.ofMul ⟨v,hRV hv⟩
    have hw : E w∈target false := by rw [←hR];exact ⟨w,hv,rfl⟩
    have hh := (pointwise_target_eq_elementary
      (Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd q))).mpr ⟨_,rfl⟩ _ hw
    rw [←hq,←he] at hh
    have heq := congrArg (fun v : Additive V=>v.toMul.val) (E.injective hh)
    change (V.normalizerMonoidHom g w.toMul).val=v at heq
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at heq
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq).symm
  rw [←actor_hyperplane_criterion E f he R hR g q hq]
  constructor
  · intro hlt
    obtain ⟨v,hv,hr⟩ := SetLike.exists_of_lt hlt
    exact ⟨v,hv.1,hr,(Subgroup.mem_centralizer_singleton_iff.mp hv.2).symm⟩
  · rintro ⟨v,hv,hr,hg⟩
    exact lt_of_le_of_ne hfix (fun hh=>hr (hh.symm ▸
      (show v∈V⊓centralizer ({g.val}:Set G) from
        ⟨hv,Subgroup.mem_centralizer_singleton_iff.mpr hg.eq.symm⟩)))
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
