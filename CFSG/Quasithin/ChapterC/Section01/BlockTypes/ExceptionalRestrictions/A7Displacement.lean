module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.A7
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements

/-!
# Fixed-line displacements in the exceptional A7 block

The original block commutator U has dimension four and a faithful action
of K/O2(K). An actor centralizing a subgroup of order two and moving U
into it has square one on U. Every nontrivial A7 involution moves a plane,
so this actor must belong to O2(K).

Source: Aschbacher--Smith, C.1.22 and 14.6.10(5), printed pp.129 and1029.
This is the actual block action used by the second-parabolic span argument.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {K : Type*} [Group K]

theorem IsExceptionalA7Block.u_finrank (h : IsExceptionalA7Block K) :
    letI := h.1.elementary
    Module.finrank (ZMod 2) (Additive (blockU K)) = 4 := by
  let := h.1.finite
  let := h.1.elementary
  apply Nat.pow_right_injective (by decide : 1 < 2)
  calc
    2 ^ Module.finrank (ZMod 2) (Additive (blockU K)) =
        Nat.card (Additive (blockU K)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    _ = Nat.card (blockU K) := Nat.card_congr Additive.toMul
    _ = 2^4 := h.u_card

theorem IsExceptionalA7Block.uRepresentation_faithful (h : IsExceptionalA7Block K) :
    letI := h.1.elementary
    Function.Injective (uRepresentation h.1) := by
  let := h.1.finite
  let := h.1.elementary
  let := h.1.module_elementary
  obtain ⟨a⟩ := h.2.1
  let σ := (moduleRepresentation h.1).comp a.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective _).mpr
      (moduleRepresentation_irreducible h.1)
  have hi := binaryAlternatingSeven_faithful_of_irreducible_four σ h.module_finrank
  intro g j he
  apply a.injective
  apply hi
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := moduleProjection_surjective w
  change moduleRepresentation h.1 (a.symm (a g)) (moduleProjection v) =
    moduleRepresentation h.1 (a.symm (a j)) (moduleProjection v)
  rw [a.symm_apply_apply,a.symm_apply_apply,←moduleProjection_equivariant,
    ←moduleProjection_equivariant,he]

/-- An actor fixing a subgroup of order two cannot move the full exceptional
four-space only into that subgroup unless it belongs to the two-core. -/
theorem IsExceptionalA7Block.mem_core_of_line_displacement (h : IsExceptionalA7Block K)
    (Z : Subgroup K) (hZ : Nat.card Z = 2) (k : K)
    (hkZ : k ∈ centralizer (Z : Set K))
    (hmove : ∀ v : blockU K, ⁅k,(v : K)⁆ ∈ Z) : k ∈ pCore 2 K := by
  let := h.1.finite
  let := h.1.elementary
  let W := Additive (blockU K)
  let ρ := uRepresentation h.1
  let q := QuotientGroup.mk' (pCore 2 K)
  let ZW : Submodule (ZMod 2) W :=
    AddSubgroup.toZModSubmodule 2 (Z.subgroupOf (blockU K)).toAddSubgroup
  have hZcard : Nat.card ZW ≤ 2 := by
    change Nat.card (Z.subgroupOf (blockU K)) ≤ 2
    exact (Nat.card_le_card_of_injective
      (fun z : Z.subgroupOf (blockU K) => (⟨z.val.val,z.property⟩ : Z))
      (by intro x y he; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : Z => (z : K)) he)).trans_eq hZ
  have hZd : Module.finrank (ZMod 2) ZW ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hZcard
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (show 2 ^ Module.finrank (ZMod 2) ZW ≤ 2^1 from hZcard)
    exact this
  have hrange : LinearMap.range (ρ (q k) - LinearMap.id) ≤ ZW := by
    rintro _ ⟨v,rfl⟩
    change (((ρ (q k) v - v).toMul : blockU K) : K) ∈ Z
    change (k * (v.toMul : K) * k⁻¹) / (v.toMul : K) ∈ Z
    simpa only [div_eq_mul_inv,commutatorElement_def] using hmove v.toMul
  have hs : q k ^ 2 = 1 := by
    apply h.uRepresentation_faithful
    rw [map_pow,map_one]
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    have hc := mem_centralizer_iff.mp hkZ _ (hmove v.toMul)
    have hd : ⁅k,(v.toMul : K)⁆ ^ 2 = 1 := by
      have hh := (pow_card_eq_one' (x := (⟨⁅k,(v.toMul : K)⁆,hmove v.toMul⟩ : Z)))
      rw [hZ] at hh
      exact congrArg Subtype.val hh
    change k*(k*(v.toMul : K)*k⁻¹)*k⁻¹ = (v.toMul : K)
    have hdconj : k*⁅k,(v.toMul : K)⁆*k⁻¹ = ⁅k,(v.toMul : K)⁆ := by
      rw [←hc,mul_inv_cancel_right]
    calc
      _ = (k*⁅k,(v.toMul : K)⁆*k⁻¹)*⁅k,(v.toMul : K)⁆*(v.toMul : K) := by
        simp only [commutatorElement_def]; group
      _ = _ := by rw [hdconj,←pow_two,hd,one_mul]
  apply (QuotientGroup.eq_one_iff _).mp
  by_contra hn
  obtain ⟨a⟩ := h.2.1
  let σ := ρ.comp a.symm.toMonoidHom
  have ha : orderOf (a (q k)) = 2 := orderOf_eq_prime
    (by rw [←map_pow,hs,map_one]) (fun he => hn (a.injective (he.trans a.map_one.symm)))
  have hh := AlternatingSevenConjugatePair.Model.involution_fixedCodim σ
    (h.uRepresentation_faithful.comp a.symm.injective) h.u_finrank (a (q k)) ha
  have hsmall : fixedCodim σ (zpowers (a (q k))) ≤ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    have he : σ (a (q k)) = ρ (q k) := by
      change ρ (a.symm (a (q k))) = _
      rw [a.symm_apply_apply]
    have hr : LinearMap.range (σ (a (q k)) - LinearMap.id) ≤ ZW := by
      rintro _ ⟨v,rfl⟩
      change σ (a (q k)) v - v ∈ ZW
      rw [he]
      exact hrange ⟨v,rfl⟩
    exact (Submodule.finrank_mono hr).trans hZd
  omega
end CFSG.Quasithin.ChapterC
