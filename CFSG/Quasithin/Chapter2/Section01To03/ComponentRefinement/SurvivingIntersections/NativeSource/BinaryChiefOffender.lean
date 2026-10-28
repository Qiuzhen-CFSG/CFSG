module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.BinarySocle
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Offender
public import Theory.Representation.NormalElementaryQuotient.MinimalNormal
public import Theory.Representation.BinaryOffender.SimpleSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The actual binary M₂₂ chief offender

The preceding source result constructs a minimal nontrivial elementary
M-normal subgroup W containing z and the binary hexad radical V. Conjugation
on W descends through the literal quotient M/C_M(W), faithfully and
irreducibly. The constructed native A₆ section embeds in this quotient.
Its actual augmentation-core embedding j satisfies W = j(V₅) + C_W(A₆),
and j carries the constant line to the original covering center Z(L).

The concrete paired four is therefore an offender in this original action.
A best offender contained in it is nontrivial; normality of J(M/C_M(W),W)
and simplicity of A₆ put the whole actual A₆ image inside J. These are
constructed inputs to the independent B.5.6 comparison, not an assumed
module classification or the final binary exclusion.

Source: Aschbacher--Smith 2.3.9(7), pp.525–526; I.2.2(6), p.412;
B.1.4–7 and B.5.3–6 for the offender-generated subgroup.
-/

public section
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers M22Local Sporadic.Mathieu.M22CentralCover
open BinaryPermutation BinaryPermutation.SixCoreExtension
open Representation Representation.BinaryOffender Representation.NormalElementaryQuotient
variable {G : Type*} [Group G] [Finite G] {L M : Subgroup G}

private theorem hexad_offender_data [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* M22) (hZ : Nat.card (center L) = 2)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (W : Subgroup M) [W.Normal] [IsElementaryAbelian 2 W]
    (hIM : (hexadPreimage e B).map L.subtype ≤ M)
    (hVW : (hexadRadical e B).map L.subtype ≤ W.map M.subtype)
    (hgen : W.map M.subtype = (hexadRadical e B).map L.subtype ⊔
      (W.map M.subtype ⊓ centralizer (L : Set G))) :
    let q := QuotientGroup.mk' (centralizer (W : Set M))
    let ρ := representation W q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ∃ f : A →* M, Function.Injective (q.comp f) ∧
      ∃ j : V →ₗ[ZMod 2] Additive W, Function.Injective j ∧
        (∀ a v, j (coreAltRepresentation a v) = ρ (q (f a)) (j v)) ∧
        j.range ⊔ Representation.invariants (ρ.comp (q.comp f)) = ⊤ ∧
        (∀ v, (((j v).toMul : M) : G) ∈ (center L).map L.subtype ↔
          coreToNatural (Fin 6) v = 0) ∧
        IsOffender ρ (pairedFour.map (q.comp f)) ∧
        (q.comp f).range ≤ offenderSubgroup ρ := by
  dsimp only
  let q := QuotientGroup.mk' (centralizer (W : Set M))
  let ρ := representation W q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  obtain ⟨d⟩ := M22Local.Binary.exists_hexadRecognition_of_perfect e hZ hB
  let U := hexadRadical e B
  let I := hexadPreimage e B
  let g : I →* M := {
    toFun x := ⟨(x : L), hIM (mem_map_of_mem L.subtype x.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let f := g.comp d.sectionHom
  let i : U →* W := {
    toFun v := ⟨⟨v, map_subtype_le W (hVW (mem_map_of_mem L.subtype v.property))⟩, by
      obtain ⟨w,hw,he⟩ := hVW (mem_map_of_mem L.subtype v.property)
      exact (show w = ⟨(v : L),_⟩ from Subtype.ext he) ▸ hw⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let j : V →ₗ[ZMod 2] Additive W :=
    (i.comp d.radicalEquiv.symm.toMonoidHom).toAdditiveRight.toZModLinearMap 2
  have hi : Function.Injective i := by
    intro v w he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : W => ((a : M) : G)) he
  have hj : Function.Injective j := hi.comp d.radicalEquiv.symm.injective
  have he (a : A) (v : V) : j (coreAltRepresentation a v) = ρ (q (f a)) (j v) := by
    let r := d.radicalEquiv.symm (Multiplicative.ofAdd v)
    have hr : d.radicalEquiv.symm (Multiplicative.ofAdd (coreAltRepresentation a v)) =
        hexadConjugation e B (d.sectionHom a) r := by
      apply d.radicalEquiv.injective
      apply Multiplicative.toAdd.injective
      rw [d.radicalEquiv.apply_symm_apply,d.equivariant]
      change coreAltRepresentation a v = coreRepresentation (Fin 6) a.val
        (d.radicalEquiv (d.radicalEquiv.symm (Multiplicative.ofAdd v))).toAdd
      rw [d.radicalEquiv.apply_symm_apply]
      rfl
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    change ((d.radicalEquiv.symm (Multiplicative.ofAdd (coreAltRepresentation a v)) : U) : L).val =
      ((d.sectionHom a : I) : L).val * ((r : U) : L).val * ((d.sectionHom a : I) : L).val⁻¹
    rw [hr]
    rfl
  have hphi : Function.Injective (q.comp f) := by
    intro a b hab
    apply coreAltRepresentation_injective
    apply LinearMap.ext
    intro v
    apply hj
    rw [he,he]
    exact congrArg (fun a => ρ a (j v)) hab
  have hs : j.range ⊔ Representation.invariants (ρ.comp (q.comp f)) = ⊤ := by
    apply top_unique
    intro w _
    have hn : W.map M.subtype ⊓ centralizer (L : Set G) ≤
        normalizer ((hexadRadical e B).map L.subtype : Set G) :=
      (inf_le_right.trans (centralizer_le (map_subtype_le _))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hw : ((w.toMul : W) : M).val ∈
        (((hexadRadical e B).map L.subtype : Subgroup G) : Set G) *
          ((W.map M.subtype ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hn,← hgen]
      exact mem_map_of_mem M.subtype w.toMul.property
    obtain ⟨v,⟨v,hv,rfl⟩,c,⟨hcW,hcL⟩,hvc⟩ := hw
    obtain ⟨cm,hcm,hce⟩ := hcW
    let u : U := ⟨v,hv⟩
    let cv : Additive W := Additive.ofMul ⟨cm,hcm⟩
    have hfix : cv ∈ Representation.invariants (ρ.comp (q.comp f)) := by
      intro a
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change (((ρ (q (f a)) cv).toMul : M) : G) = (cm : G)
      rw [NormalElementaryQuotient.representation_apply]
      have hh := mem_centralizer_iff.mp hcL ((d.sectionHom a : I) : L) (d.sectionHom a).val.property
      change _ = _ at hh
      change (cm : G) = c at hce
      change ((f a : M) : G) * (cm : G) * ((f a : M) : G)⁻¹ = (cm : G)
      rw [hce]
      change ((d.sectionHom a : I) : L).val * c * ((d.sectionHom a : I) : L).val⁻¹ = c
      rw [hh,mul_inv_cancel_right]
    change (cm : G) = c at hce
    have hwEq : j (d.radicalEquiv u).toAdd + cv = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change ((d.radicalEquiv.symm (d.radicalEquiv u) : U) : L).val * (cm : G) = _
      rw [d.radicalEquiv.symm_apply_apply,hce]
      exact hvc
    rw [← hwEq]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left ⟨_,rfl⟩) (Submodule.mem_sup_right hfix)
  have hoff := pairedFour_extension_offender (ρ.comp (q.comp f)) j he hs
  have hjcenter (v : V) : (((j v).toMul : M) : G) ∈ (center L).map L.subtype ↔
      coreToNatural (Fin 6) v = 0 := by
    let r := d.radicalEquiv.symm (Multiplicative.ofAdd v)
    have hr : (r : L) ∈ center L ↔ coreToNatural (Fin 6) v = 0 := by
      rw [d.center_iff,d.radicalEquiv.apply_symm_apply]
      rfl
    rw [← hr]
    constructor
    · rintro ⟨x,hx,he⟩
      exact (show x = (r : L) from Subtype.ext he) ▸ hx
    · intro hx
      exact mem_map_of_mem L.subtype hx
  have hoff' := hoff.map_equivariant (ρ.comp (q.comp f)) ρ (q.comp f) hphi
    (LinearEquiv.refl _ _) (fun _ _ => rfl)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨f,hphi,j,hj,he,hs,hjcenter,hoff',
    simple_range_le_offenderSubgroup ρ (q.comp f) pairedFour hoff'⟩

omit [Finite G] in
private theorem projection_quotient_eq {z : G} {t u : L}
    (ht : IsConjugationProjection L z t) (hu : IsConjugationProjection L z u) :
    QuotientGroup.mk' (center L) t = QuotientGroup.mk' (center L) u := by
  apply QuotientGroup.eq.mpr
  apply mem_center_iff.mpr
  intro x
  have he : t * x * t⁻¹ = u * x * u⁻¹ := Subtype.ext ((ht x).symm.trans (hu x))
  calc
    x * (t⁻¹ * u) = t⁻¹ * (t * x * t⁻¹) * u := by group
    _ = t⁻¹ * (u * x * u⁻¹) * u := by rw [he]
    _ = (t⁻¹ * u) * x := by group


variable {C : GroupClass} {H : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original binary source configuration supplies a faithful irreducible
FF-module for the literal centralizer quotient of M, with the actual A₆
section and covering-center line retained. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_chief_offender
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    let h := c.localSetup hG structural115Input sourceC
    let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      let B := m22FixedPoints (projection e t)
      B ∈ m22Blocks ∧ ∃ W : Subgroup M,
        W.Normal ∧ W ≠ ⊥ ∧ W ≤ pCore 2 M ∧ IsElementaryAbelian 2 W ∧
        (∀ U : Subgroup M, U.Normal → U ≤ W → U = ⊥ ∨ U = W) ∧
        z ∈ W.map M.subtype ∧
        W.map M.subtype = (hexadRadical e B).map L.subtype ⊔
          (W.map M.subtype ⊓ centralizer (L : Set G)) ∧
        ∀ (hn : W.Normal) (hE : IsElementaryAbelian 2 W),
          letI : W.Normal := hn
          letI : IsElementaryAbelian 2 W := hE
          let q := QuotientGroup.mk' (centralizer (W : Set M))
          let ρ := NormalElementaryQuotient.representation W q
            (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
          Function.Injective ρ ∧ IsIrreducible ρ ∧
          ∃ f : A →* M, Function.Injective (q.comp f) ∧
            ∃ j : V →ₗ[ZMod 2] Additive W, Function.Injective j ∧
              (∀ a v, j (coreAltRepresentation a v) = ρ (q (f a)) (j v)) ∧
              j.range ⊔ Representation.invariants (ρ.comp (q.comp f)) = ⊤ ∧
              (∀ v, (((j v).toMul : M) : G) ∈ (center L).map L.subtype ↔
                coreToNatural (Fin 6) v = 0) ∧
              IsOffender ρ (pairedFour.map (q.comp f)) ∧
        (q.comp f).range ≤ offenderSubgroup ρ := by
  dsimp only
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  let := h.quasisimple
  obtain ⟨t,ht,hto,htn,hB,W,hWn,hWne,hWQ,hWe,hWmin,hzW,hsplit⟩ :=
    c.mathieuTwentyTwo_binary_minimal_core_decomposition hG sourceC d hc
  refine ⟨t,ht,hto,htn,hB,W,hWn,hWne,hWQ,hWe,hWmin,hzW,hsplit,?_⟩
  intro hn hE
  let : W.Normal := hn
  let : IsElementaryAbelian 2 W := hE
  refine ⟨representation_injective W _ _ _,
    irreducible_of_minimal_normal W hWne hWmin _ _ _,?_⟩
  obtain ⟨u,hu,_,_,_,_,_,hjoin⟩ := c.mathieuTwentyTwo_binary_hexad_join_le hG sourceC d hc
  have hIM : (hexadPreimage e (m22FixedPoints (projection e u))).map L.subtype ≤ M :=
    (show (hexadPreimage e (m22FixedPoints (projection e u))).map L.subtype ≤
      (hexadPreimage e (m22FixedPoints (projection e u))).map L.subtype ⊔
        (S : Subgroup H).map H.subtype from le_sup_left).trans hjoin
  have he : projection e u = projection e t := congrArg e (projection_quotient_eq hu ht)
  rw [he] at hIM
  have hVW : (hexadRadical e (m22FixedPoints (projection e t))).map L.subtype ≤ W.map M.subtype := by
    rw [hsplit]
    exact le_sup_left
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
  exact hexad_offender_data e hZ hB W hIM hVW hsplit

end CFSG.Quasithin.Chapter2.ComponentRefinement
