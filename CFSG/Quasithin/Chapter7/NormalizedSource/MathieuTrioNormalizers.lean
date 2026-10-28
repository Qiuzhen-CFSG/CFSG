module
public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.PlaneAction
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.Representation.BinaryConjugationSection.NaturalGeneration

/-!
# The actual normalizer action on a marked Mathieu three-space

The native trio lifts every linear automorphism of its affine-plane three-space.
A surjection from the original component to M24 therefore lifts those operators
to the component normalizer of the actual subgroup U. The action kernel is
exactly its relative centralizer. Perfectness of GL(3,2) gives the same full
image for the intrinsic solvable residual; every nontrivial seed in U generates
U under that residual. Coordinates preserve the original conjugation action.

The companion NonFFSourceMathieuM24Normalizers applies these results to the
original offender fixed space. This proves the natural-action part of the
M24 cocode row of 8.2.6; componenthood and two-core identification are separate.
Source: Aschbacher--Smith H.15.6(2), 8.2.5--6, printed pp.401,716--717,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode MathieuCode.TrioCalculation
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

variable {G : Type*} [Group G]

private theorem plane_coordinates (W U : Subgroup G) [IsElementaryAbelian 2 W]
    (hUW : U ≤ W) (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    ∃ e : U ≃* Multiplicative Vector, ∀ u : U,
      standardPlaneMap (e u).toAdd = F (Additive.ofMul (inclusion hUW u)) := by
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUW
  let i : Additive U →ₗ[ZMod 2] Additive W :=
    (inclusion hUW).toAdditive.toZModLinearMap 2
  let j : Additive U →ₗ[ZMod 2] standardPlaneMap.range :=
    (F.toLinearMap.comp i).codRestrict _ (fun u => (hplane _).mp u.toMul.property)
  have hj : Function.Bijective j := by
    constructor
    · intro x y hxy
      have hh := F.injective (congrArg Subtype.val hxy)
      exact Additive.toMul.injective (Subtype.ext (congrArg (fun w : Additive W => w.toMul.val) hh))
    · intro v
      obtain ⟨w,hw⟩ := F.surjective v.val
      have hu : w.toMul.val ∈ U := (hplane w.toMul).mpr (hw ▸ v.property)
      refine ⟨Additive.ofMul ⟨w.toMul.val,hu⟩,Subtype.ext ?_⟩
      exact hw
  let P := LinearEquiv.ofInjective standardPlaneMap standardPlaneMap_injective
  let E := (LinearEquiv.ofBijective j hj).trans P.symm
  let e : U ≃* Multiplicative Vector :=
    { toFun := fun u => Multiplicative.ofAdd (E (Additive.ofMul u))
      invFun := fun v => (E.symm v.toAdd).toMul
      left_inv := fun u => E.symm_apply_apply (Additive.ofMul u)
      right_inv := fun v => E.apply_symm_apply v.toAdd
      map_mul' := fun x y => E.map_add (Additive.ofMul x) (Additive.ofMul y) }
  refine ⟨e,fun u => ?_⟩
  exact congrArg Subtype.val (P.apply_symm_apply (j (Additive.ofMul u)))

/-- The native plane action lifts to the literal component normalizer. -/
theorem plane_normalizer_action (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* M24) (hq : Function.Surjective q)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    ∃ (e : U ≃* Multiplicative Vector)
      (π : (L ⊓ normalizer (U : Set G) : Subgroup G) →* BinaryLinear.GL Vector),
      Function.Surjective π ∧
      π.ker = (centralizer (U : Set G)).subgroupOf (L ⊓ normalizer (U : Set G)) ∧
      (∀ u : U, standardPlaneMap (e u).toAdd =
        F (Additive.ofMul (inclusion hUW u))) ∧
      ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (u : U),
        (e (U.normalizerMonoidHom ⟨l,l.property.2⟩ u)).toAdd = π l (e u).toAdd := by
  obtain ⟨e,he⟩ := plane_coordinates W U hUW F hplane
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUW
  let fE : Additive U →+ Vector :=
    { toFun := fun u => (e u.toMul).toAdd
      map_zero' := e.map_one
      map_add' := fun x y => e.map_mul x.toMul y.toMul }
  let E : Additive U ≃ₗ[ZMod 2] Vector :=
    LinearEquiv.ofBijective (fE.toZModLinearMap 2) e.bijective
  let H := L ⊓ normalizer (U : Set G)
  let ρ : Representation (ZMod 2) H (Additive U) :=
    (automizerRepresentation U).comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion inf_le_right))
  let π : H →* BinaryLinear.GL Vector :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vector).toMonoidHom.comp
      ((Units.mapEquiv E.conjRingEquiv.toMulEquiv).toMonoidHom.comp ρ.asGroupHom)
  have hπ (l : H) (u : U) :
      π l (e u).toAdd = (e (U.normalizerMonoidHom ⟨l,l.property.2⟩ u)).toAdd := by
    change E (ρ l (E.symm (E (Additive.ofMul u)))) = _
    rw [E.symm_apply_apply]
    rfl
  refine ⟨e,π,?_,?_,he,fun l u => (hπ l u).symm⟩
  · intro f
    obtain ⟨t,ht⟩ := standardPlaneMap_full_action f
    obtain ⟨l,hl⟩ := hq t.val
    have hconj (w : W) :
        (w : G) ∈ U ↔ (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w : G) ∈ U := by
      rw [hplane,hplane,hF,hl]
      constructor
      · rintro ⟨v,hv⟩
        rw [←hv,ht]
        exact LinearMap.mem_range_self _ _
      · intro hv
        obtain ⟨v,hv⟩ := hv
        refine ⟨f.symm v,?_⟩
        have hh := ht (f.symm v)
        rw [f.apply_symm_apply] at hh
        have hinj := (LinearMap.GeneralLinearGroup.toLinearEquiv
          (cocodeRepresentation.asGroupHom t.val)).injective
        exact hinj (hh.trans hv)
    have hlU : (l : G) ∈ normalizer (U : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact (hconj ⟨x,hUW hx⟩).mp hx
      · intro hx
        have hxW : x ∈ W := (mem_normalizer_iff.mp (hLW l.property) x).mpr (hUW hx)
        exact (hconj ⟨x,hxW⟩).mpr hx
    refine ⟨⟨l,l.property,hlU⟩,?_⟩
    apply LinearEquiv.ext
    intro v
    obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd v)
    have huv : (e u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←huv,hπ]
    apply standardPlaneMap_injective
    rw [he]
    change F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ (inclusion hUW u))) = _
    rw [hF,hl,←he,ht]
  · ext l
    change π l = 1 ↔ (l : G) ∈ centralizer (U : Set G)
    constructor
    · intro hl
      rw [mem_centralizer_iff]
      intro u hu
      have hh := hπ l ⟨u,hu⟩
      rw [hl] at hh
      have hc : l.val * u * l.val⁻¹ = u :=
        congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh.symm))
      exact (mul_inv_eq_iff_eq_mul).mp hc |>.symm
    · intro hl
      apply LinearEquiv.ext
      intro v
      obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd v)
      have huv : (e u).toAdd = v := congrArg Multiplicative.toAdd hu
      rw [←huv,hπ]
      change (e (U.normalizerMonoidHom ⟨l,l.property.2⟩ u)).toAdd = (e u).toAdd
      apply congrArg Multiplicative.toAdd
      apply congrArg e
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul).mpr (mem_centralizer_iff.mp hl u u.property).symm

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

/-- Perfectness of GL(3,2) makes the original residual induce the same full action. -/
theorem residual_surjective {H : Type*} [Group H] [Finite H]
    (π : H →* BinaryLinear.GL Vector) (hπ : Function.Surjective π) :
    Function.Surjective (π.comp (solvableResidual H).subtype) := by
  let : Group.IsPerfect (BinaryLinear.GL Vector) := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  have ht : (solvableResidual H).map π = ⊤ := by
    rw [map_solvableResidual_eq π hπ,solvableResidual_eq_top]
  intro f
  obtain ⟨h,hh,he⟩ := (show f ∈ (solvableResidual H).map π from ht ▸ mem_top f)
  exact ⟨⟨h,hh⟩,he⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
variable {G : Type*} [Group G] [Finite G]

/-- Every nontrivial seed in the actual three-space generates it under the
intrinsic solvable residual of its full linear actor. -/
theorem plane_residual_conjugateSpan (U H : Subgroup G)
    (hHU : H ≤ normalizer (U : Set G))
    (e : U ≃* Multiplicative Vector) (π : H →* BinaryLinear.GL Vector)
    (hπ : Function.Surjective π)
    (hact : ∀ (h : H) (u : U),
      (e (U.normalizerMonoidHom ⟨h,hHU h.property⟩ u)).toAdd = π h (e u).toAdd)
    (B : Subgroup G) (hBU : B ≤ U) (hB : B ≠ ⊥) :
    conjugateSpanBy B ((solvableResidual H).map H.subtype) = U := by
  have hR : (solvableResidual H).map H.subtype ≤ normalizer (U : Set G) :=
    (map_subtype_le _).trans hHU
  apply le_antisymm (conjugateSpanBy_le hBU hR)
  obtain ⟨b,hb,hb1⟩ := B.bot_or_exists_ne_one.resolve_left hB
  let bU : U := ⟨b,hBU hb⟩
  let v := (e bU).toAdd
  have hv : v ≠ 0 := by
    intro hz
    have he : e bU = e 1 := hz.trans e.map_one.symm
    exact hb1 (congrArg Subtype.val (e.injective he))
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1]; exact one_mem _
  let uU : U := ⟨u,hu⟩
  let w := (e uU).toAdd
  have hw : w ≠ 0 := by
    intro hz
    have he : e uU = e 1 := hz.trans e.map_one.symm
    exact hu1 (congrArg Subtype.val (e.injective he))
  let ev := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) Vector v hv
  let ew := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) Vector w hw
  obtain ⟨f,hf⟩ := Submodule.exists_linearEquiv_restrict_eq (ev.symm.trans ew)
  have hfv : f v = w := by
    have hh := hf (ev 1)
    simp only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] at hh
    simpa [ev,ew] using hh.symm
  obtain ⟨r,hr⟩ := residual_surjective π hπ f
  have hmove : (r.val.val : G) * b * (r.val.val : G)⁻¹ = u := by
    have hh := hact r.val bU
    change (e (U.normalizerMonoidHom ⟨r.val,hHU r.val.property⟩ bU)).toAdd = π r.val v at hh
    rw [show π r.val = f from hr,hfv] at hh
    exact congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh))
  exact subset_closure ⟨r.val.val,⟨r.val,r.property,rfl⟩,b,hb,hmove⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
