module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoCartanOrbits
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedProjection
public import Theory.Representation.G2NaturalTransitivity.FieldTransport
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# The original G₂ natural fixed-vector marking

The chosen central involution in the tensor line survives the moved/fixed
quotient: vanishing would make it centralize the residual and the common
Sylow, hence the center-free overgroup. The actual field-four action
selection then supplies natural G₂ coordinates. Transporting the field
and conjugating the common Sylow together with the nonzero vector gives
the required standard marking, retaining the literal actionMk map and
old residual image. The linear rows are already excluded by their Cartan
orbits; the symplectic row has a different group order.

The final row assembly is in GenerationTwoCartanComplete. No normality
of the H-conjugate span under L is assumed.
Source: Aschbacher--Smith 9.3.6--9, printed pp.733--734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterC.MSCentralOrbit
open ChapterB.QuasisimpleSource

private theorem projected_g2_fixed
    {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) {K : Subgroup X}
    (s : MovedSection ρ K) (hm : moved ρ K = ⊤)
    (F : BinaryField) (a : ActionEquiv (s.central.quotientRepresentation.comp K.subtype) (binaryG2 F))
    (x : K) (v : V) (hv : ρ x v = v) :
    Atlas.G2.Natural.action F.Carrier (a.groupEquiv x)
      (a.linearEquiv (s.fullProjection hm v)) = a.linearEquiv (s.fullProjection hm v) := by
  have hp := s.fullProjection_intertwines hm (x : X) v
  exact (a.intertwines x (s.fullProjection hm v)).symm.trans
    (congrArg a.linearEquiv (hp.symm.trans (congrArg (s.fullProjection hm) hv)))

private theorem mark_g2_sylow_fixed_vector
    {X Y F : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    [Field F] [Finite F] [CharP F 2]
    (q : X →* Y) (hq : Function.Surjective q) (a : Y ≃* Atlas.G2.Model F)
    (R : Sylow 2 X) (B : Subgroup X)
    (v : Atlas.G2.Natural.Space F) (hv : v ≠ 0)
    (hR : ∀ r ∈ (R : Subgroup X), Atlas.G2.Natural.action F (a (q r)) v = v)
    (hB : ∀ b ∈ B, Atlas.G2.Natural.action F (a (q b)) v = v) :
    ∃ a' : Y ≃* Atlas.G2.Model F, ∃ v' : Atlas.G2.Natural.Space F,
      (R : Subgroup X).map (a'.toMonoidHom.comp q) = Atlas.G2.unipotent ∧
      v' ≠ 0 ∧
      (∀ u ∈ Atlas.G2.unipotent (K := F), Atlas.G2.Natural.action F u v' = v') ∧
      ∀ b ∈ B.map (a'.toMonoidHom.comp q), Atlas.G2.Natural.action F b v' = v' := by
  let S := (R.mapSurjective hq).mapSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F) S
    (Atlas.G2.LieParabolicSetup.sylow (F := F))
  let b := MulAut.conj g
  let a' := a.trans b
  let ρ := Atlas.G2.Natural.action F
  have hS : (S : Subgroup (Atlas.G2.Model F)).map b.toMonoidHom = Atlas.G2.unipotent := by
    rw [←Atlas.G2.LieParabolicSetup.sylow_coe,←hg,Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
    rfl
  have hmap : (R : Subgroup X).map (a'.toMonoidHom.comp q) = Atlas.G2.unipotent := by
    rw [←hS]
    change _ = (((R : Subgroup X).map q).map a.toMonoidHom).map b.toMonoidHom
    rw [map_map,map_map]
    rfl
  have hconj (x : Atlas.G2.Model F) (hx : ρ x v = v) : ρ (b x) (ρ g v) = ρ g v := by
    change ρ (g*x*g⁻¹) (ρ g v) = ρ g v
    rw [map_mul,Module.End.mul_apply,ρ.inv_self_apply,map_mul,Module.End.mul_apply,hx]
  refine ⟨a',ρ g v,hmap,?_,?_,?_⟩
  · intro hh
    have he := congrArg (ρ g⁻¹) hh
    rw [ρ.inv_self_apply,map_zero] at he
    exact hv he
  · intro u hu
    rw [←hmap] at hu
    obtain ⟨r,hr,rfl⟩ := hu
    exact hconj (a (q r)) (hR r hr)
  · rintro u ⟨x,hx,rfl⟩
    exact hconj (a (q x)) (hB x hx)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}
namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

/-- A nonzero Sylow-fixed vector survives the residual central quotient. -/
theorem sylow_fixed_not_residual_fixed
    (W : Subgroup c.M) [W.Normal] [IsElementaryAbelian 2 W]
    (N : Subgroup (ActionQuotient W))
    (hJN : (pResidual 2 c.M).map (actionMk W) ≤ N)
    (hzM : center c.M = ⊥)
    (v : Additive W) (hv : v ≠ 0)
    (hvR : ∀ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M),
      action W (actionMk W r) v = v) :
    v ∉ Representation.BinaryOffender.fixedSpace ((action W).comp N.subtype)
      (((pResidual 2 c.M).map (actionMk W)).subgroupOf N) := by
  intro hfix
  have hcomm (k : c.M) (hk : k ∈ pResidual 2 c.M) :
      k * (v.toMul : c.M) = (v.toMul : c.M) * k := by
    have hq : actionMk W k ∈ (pResidual 2 c.M).map (actionMk W) := mem_map_of_mem _ hk
    have hh := hfix ⟨⟨actionMk W k,hJN hq⟩,hq⟩
    change action W (actionMk W k) v = v at hh
    have he := congrArg (fun x : Additive W => (x.toMul : c.M)) hh
    rw [action_apply] at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  have hrcomm (r : c.M)
      (hr : r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)) :
      r * (v.toMul : c.M) = (v.toMul : c.M) * r := by
    have he := congrArg (fun x : Additive W => (x.toMul : c.M)) (hvR r hr)
    rw [action_apply] at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  have hc : (v.toMul : c.M) ∈ center c.M := by
    rw [mem_center_iff]
    intro g
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 g
    rw [mul_assoc,hrcomm r hr,←mul_assoc,hcomm k hk,mul_assoc]
  have hz : (v.toMul : c.M) = 1 := mem_bot.mp (hzM ▸ hc)
  exact hv (Additive.toMul.injective (Subtype.ext hz))

end GenerationTwoOvergroup

variable (m)

/-- The original Omega action admits the required G₂ marking and nonzero fixed vector. -/
theorem g2FixedVectorInput : m.G2FixedVectorInput := by
  have ho : ∀ c : m.GenerationTwoOvergroup, c.CartanOrbits := fun c => c.cartanOrbits
  intro c W hr ha
  let := hr.normal
  let := hr.elementary
  obtain ⟨hUcore,_,_,hcenter,hr',hUW,hJN,hm,h,hs⟩ := c.fourField_models c.hasMaximalOutside
  let ρ := action W
  let N := Representation.BinaryOffender.offenderSubgroup ρ
  let J := pResidual 2 c.M
  let A := J.map (actionMk W)
  let i : A ≃* A.subgroupOf N := (subgroupOfEquivOfLe hJN).symm
  let F₀ := BinaryField.four
  have field_equiv (F : BinaryField) (hc : Nat.card F.Carrier = 4) :
      Nonempty (F.Carrier ≃+* F₀.Carrier) := by
    let := Fintype.ofFinite F.Carrier
    let := Fintype.ofFinite F₀.Carrier
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hc,F₀.card_eq]; rfl)⟩
  cases hs with
  | linearThree F hc _ a =>
    obtain ⟨f⟩ := field_equiv F hc
    exact False.elim (c.not_linear_of_cartanOrbits (ho c) hr
      ⟨i.trans (a.groupEquiv.trans (Atlas.fieldEquivSL 3 f))⟩)
  | doubleThree F hc a =>
    obtain ⟨f⟩ := field_equiv F hc
    exact False.elim (c.not_linear_of_cartanOrbits (ho c) hr
      ⟨i.trans (a.groupEquiv.trans (Atlas.fieldEquivSL 3 f))⟩)
  | symplectic F hc _ _ a =>
    obtain ⟨aG⟩ := ha
    have he := Nat.card_congr ((i.trans a.groupEquiv).symm.trans aG).toEquiv
    rw [Theory.SpecificGroups.SymplecticFour.card_sp,Atlas.G2.card_Model,hc,
      BinaryField.four.card_eq] at he
    norm_num [BinaryField.four] at he
  | g2 F hc _ _ a =>
    obtain ⟨f⟩ := field_equiv F hc
    let a₀ := i.trans a.groupEquiv
    let a₁ := a₀.trans (Atlas.G2.fieldEquiv f)
    obtain ⟨z,hz2,hzU,hzT⟩ := m.exists_central_involution_tensorLine
    have hzM : z ∈ c.M := (map_subtype_le (pCore 2 c.M)) (hUcore hzU)
    let w : Additive W := Additive.ofMul ⟨⟨z,hzM⟩,hUW hzU⟩
    have hw : w ≠ 0 := by
      intro hh
      have hz1 : z = 1 := congrArg (fun x : Additive W => ((x.toMul : c.M) : G)) hh
      rw [hz1,orderOf_one] at hz2
      omega
    have hwfix (x : c.M) (hx : (x : G)*z = z*(x : G)) : ρ (actionMk W x) w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change (((ρ (actionMk W x) w).toMul : c.M) : G) = z
      rw [action_apply]
      change (x : G)*z*(x : G)⁻¹ = z
      rw [hx,mul_inv_cancel_right]
    have hwR : ∀ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M),
        action W (actionMk W r) w = w := fun r hr => hwfix r (hzT r hr.1)
    have hwn := c.sylow_fixed_not_residual_fixed W N hJN hcenter w hw hwR
    let s := h.sectionData
    let v := a.linearEquiv (s.fullProjection hm w)
    have hv : v ≠ 0 := by
      intro hh
      have he : s.fullProjection hm w = 0 := a.linearEquiv.map_eq_zero_iff.mp hh
      exact hwn ((s.fullProjection_eq_zero_iff hm w).mp he)
    let v₁ := Atlas.G2.Natural.Transitivity.fieldTransport f v
    have hv₁ : v₁ ≠ 0 := fun hh => hv ((Atlas.G2.Natural.Transitivity.fieldTransport f).map_eq_zero_iff.mp hh)
    let q := (actionMk W).subgroupMap J
    have equiv_fixed (x : J) (hx : ρ (actionMk W x) w = w) :
        Atlas.G2.Natural.action F₀.Carrier (a₁ (q x)) v₁ = v₁ := by
      let x' : A.subgroupOf N := i (q x)
      have he' : Atlas.G2.Natural.action F.Carrier (a₀ (q x)) v = v :=
        projected_g2_fixed (ρ.comp N.subtype) s hm F a x' w hx
      have hf := Atlas.G2.Natural.Transitivity.fieldTransport_action f (a₀ (q x)) v
      rw [he'] at hf
      exact hf.symm
    obtain ⟨_,_,_,_,_,_,_,_,R,hR,_,_⟩ := m.old_residual_pair_action_data
      c.hstar c.large c.M c.core_ne_bot c.generated c.line_centralized W hUW
    let B := (((pResidual 2 c.H).map c.H.subtype).subgroupOf c.M).subgroupOf J
    obtain ⟨a',v',hS,hv',hU,hB⟩ := mark_g2_sylow_fixed_vector q
      ((actionMk W).subgroupMap_surjective J) a₁ R B v₁ hv₁
      (by
        intro r hr
        apply equiv_fixed r
        apply hwR r
        rw [hR] at hr
        exact hr)
      (by
        intro b hb
        apply equiv_fixed b
        apply hwfix b
        exact ((c.line_centralized hb) z hzU).symm)
    refine ⟨⟨a',?_,v',hv',hU,hB⟩⟩
    rw [←hR]
    exact hS

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
