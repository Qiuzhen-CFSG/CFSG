module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
public import Mathlib.LinearAlgebra.Projection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Coordinates

/-!
# Extending the quotient-line marking to the radical omega center

Odd-order averaging splits the kernel of the original projection V₁ → F from
its moved subspace. The corrected center identity extends that splitting to
Z₁, with C_{Z₁}(L) as its literal fixed factor. A scalar character of the
original Cartan then descends through Y → Y/C_Y(Z₁), since an element acting
trivially on Z₁ acts trivially on its marked line.

`Geometry.lean` supplies the character from the preceding fixed-line identity
and applies the resulting marking to the existing Cartan–TI input. No
vanishing of C_V(L), splitting of the original central kernel, or TI assertion
is assumed in this construction.
Source: Aschbacher–Smith, 11.1.5, printed p.766.
-/

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open Representation.BinaryOffender Representation.GoldschmidtONan
open Representation.RegularCyclicNormalClosure
open CFSG.Quasithin.ChapterB.QuasisimpleSource
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair

private theorem scalar_extension_coordinates
    {H A U : Type*} [Group H] [Finite H]
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup U] [Module (ZMod 2) U]
    {F : BinaryField} (hF : 1 < F.degree)
    (ρ : Representation (ZMod 2) H A) (σ : Representation (ZMod 2) H U)
    (j : U →ₗ[ZMod 2] A) (p : U →ₗ[ZMod 2] F.Carrier)
    (C : Submodule (ZMod 2) A) (χ : H →* F.Carrierˣ)
    (hodd : Odd (Nat.card H)) (hj : Function.Injective j) (hp : Function.Surjective p)
    (hχ : Function.Surjective χ)
    (hker : ∀ u, p u = 0 ↔ j u ∈ C)
    (hspan : j.range ⊔ C = ⊤)
    (hfixed : ∀ (x : H) (z : C), ρ x z = z)
    (hcompat : ∀ x u, ρ x (j u) = j (σ x u))
    (hscalar : ∀ x u, p (σ x u) = (χ x : F.Carrier) * p u) :
    ∃ e : A ≃ₗ[ZMod 2] F.Carrier × C,
      (∀ z : C, e z = (0,z)) ∧
      ∀ x z, e (ρ x z) = ((χ x : F.Carrier) * (e z).1, (e z).2) := by
  have hcard : 1 < Nat.card F.Carrierˣ := by
    rw [Nat.card_units, F.card_eq]
    have hpow : 2 ^ 2 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide) hF
    omega
  let : Nontrivial F.Carrierˣ := (Finite.one_lt_card_iff_nontrivial).mp hcard
  obtain ⟨a,ha⟩ := exists_ne (1 : F.Carrierˣ)
  obtain ⟨x,hx⟩ := hχ a
  have hfixker : fixedSpace σ ⊤ = p.ker := by
    ext u
    constructor
    · intro hu
      have he := hscalar x u
      rw [show σ x u = u from hu ⟨x, mem_top _⟩, hx] at he
      change p u = 0
      by_contra hne
      apply ha
      apply Units.ext
      exact mul_right_cancel₀ hne (he.symm.trans (one_mul _).symm)
    · intro hu y
      apply hj
      change j (σ (y : H) u) = j u
      rw [← hcompat]
      exact hfixed y ⟨j u,(hker u).mp hu⟩
  let W := displacementSpan σ ⊤ ⊤
  have hc : IsCompl W p.ker := by
    rw [← hfixker]
    exact (isCompl_fixed_moved_of_odd (ρ := σ) (Y := ⊤)
      (by simpa only [Subgroup.card_top] using hodd)).symm
  let q : W →ₗ[ZMod 2] F.Carrier := p.comp W.subtype
  have hq : Function.Bijective q := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro w hw
      apply Subtype.ext
      exact (Submodule.mem_bot (R := ZMod 2)).mp
        (hc.inf_eq_bot ▸ (show w.val ∈ W ⊓ p.ker from ⟨w.property,hw⟩))
    · intro v
      obtain ⟨u,hu⟩ := hp v
      obtain ⟨w,hw,k,hk,he⟩ := Submodule.mem_sup.mp
        (show u ∈ W ⊔ p.ker by rw [hc.sup_eq_top]; trivial)
      refine ⟨⟨w,hw⟩, ?_⟩
      change p w = v
      rw [← hu, ← he, map_add, show p k = 0 from hk, add_zero]
  let eW := LinearEquiv.ofBijective q hq
  let s : W × C →ₗ[ZMod 2] A := (j.comp W.subtype).coprod C.subtype
  have hs : Function.Bijective s := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      rintro ⟨w,z⟩ hz
      change j w + z = 0 at hz
      have hwC : j w ∈ C := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact C.neg_mem z.property
      have hw0 : w = 0 := by
        apply eW.injective
        exact ((hker w).mpr hwC).trans eW.map_zero.symm
      apply Prod.ext hw0
      apply Subtype.ext
      change (z : A) = 0
      simpa only [hw0, Submodule.coe_zero, map_zero, zero_add] using hz
    · intro z
      obtain ⟨u,hu,c,hc',he⟩ := Submodule.mem_sup.mp
        (show z ∈ j.range ⊔ C by rw [hspan]; trivial)
      obtain ⟨v,rfl⟩ := hu
      obtain ⟨w,hw,k,hk,he'⟩ := Submodule.mem_sup.mp
        (show v ∈ W ⊔ p.ker by rw [hc.sup_eq_top]; trivial)
      refine ⟨(⟨w,hw⟩,⟨j k + c,C.add_mem ((hker k).mp hk) hc'⟩), ?_⟩
      change j w + (j k + c) = z
      rw [← add_assoc, ← map_add, he', he]
  let es := LinearEquiv.ofBijective s hs
  let e : A ≃ₗ[ZMod 2] F.Carrier × C :=
    es.symm.trans (eW.prodCongr (LinearEquiv.refl (ZMod 2) C))
  have he (w : W) (z : C) : e (j w + z) = (eW w,z) := by
    change (eW.prodCongr (LinearEquiv.refl (ZMod 2) C)) (es.symm (es (w,z))) = _
    rw [es.symm_apply_apply]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro z
    simpa only [Submodule.coe_zero, map_zero, zero_add] using he 0 z
  · intro x z
    obtain ⟨⟨w,k⟩,rfl⟩ := es.surjective z
    have hw : σ x w ∈ W := moved_mem_action (ρ := σ) (⟨x, mem_top _⟩ : (⊤ : Subgroup H)) w.property
    change e (ρ x (j w + k)) = ((χ x : F.Carrier) * (e (j w + k)).1, (e (j w + k)).2)
    rw [map_add, hcompat, hfixed, he ⟨σ x w,hw⟩ k, he w k]
    exact Prod.ext (hscalar x w) rfl


variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} {c : Coordinates D F}

/-- Scalar coordinates on the literal omega center, with its original fixed
subspace as second factor. No vanishing of the seed's central kernel is used. -/
theorem scalarDecomposition_of_line_character (f : InvariantFlag c)
    (hF : 1 < F.degree) {X : Subgroup G} (hX : IsCartan T L X)
    (hXY : X ≤ normalizer (f.Ri 0 : Set G))
    (hXU : X ≤ normalizer (f.Vi 0 : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (χ : X →* F.Carrierˣ) (hχ : Function.Surjective χ)
    (hline : ∀ (x : X) (v : Additive (f.Vi 0)),
      lineProjection f (lineAction f (inclusion hXU x) v) =
        (χ x : F.Carrier) • lineProjection f v) :
    Nonempty (ScalarDecomposition (f.Ri 0) L X F) := by
  let R := f.Ri 0
  let Z := radicalOmegaCenter R
  let C := fixedSubspace R L
  have hUZ : f.Vi 0 ≤ Z := by
    change f.Vi 0 ≤ radicalOmegaCenter (f.Ri 0)
    rw [hcenter]
    exact le_sup_left
  let j : Additive (f.Vi 0) →ₗ[ZMod 2] Additive Z :=
    (inclusion hUZ).toAdditive.toZModLinearMap 2
  let eF : f.space 0 ≃ₗ[F.Carrier] F.Carrier :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one (f.dimension 0)).some.symm
  let p : Additive (f.Vi 0) →ₗ[ZMod 2] F.Carrier :=
    (eF.restrictScalars (ZMod 2)).toLinearMap.comp (lineProjection f)
  have hj : Function.Injective j := fun _ _ he =>
    Additive.toMul.injective (Subtype.ext (congrArg (fun z : Additive Z => z.toMul.val) he))
  have hp : Function.Surjective p := eF.surjective.comp (lineProjection_surjective f)
  have hker (u : Additive (f.Vi 0)) : p u = 0 ↔ j u ∈ C := by
    have he : p u = 0 ↔ lineProjection f u = 0 := by
      change eF (lineProjection f u) = 0 ↔ _
      rw [← eF.map_zero, eF.injective.eq_iff]
    rw [he]
    change lineProjection f u = 0 ↔ (u.toMul.val ∈ Z ∧
      u.toMul.val ∈ centralizer (L : Set G))
    have hz := hUZ u.toMul.property
    constructor
    · intro hu
      refine ⟨hz, ?_⟩
      apply (c.projection_eq_one_iff (inclusion (D.centralQuotientPreimage_le _) u.toMul)).mp
      exact congrArg (fun v : f.space 0 => Multiplicative.ofAdd v.val) hu
    · rintro ⟨_,hu⟩
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        ((c.projection_eq_one_iff (inclusion (D.centralQuotientPreimage_le _) u.toMul)).mpr hu)
  have hspan : j.range ⊔ C = ⊤ := by
    apply top_unique
    intro z _
    have hz : z.toMul ∈ (f.Vi 0).subgroupOf Z ⊔ (radicalFixedCenter R L).subgroupOf Z := by
      rw [← subgroupOf_sup hUZ (show radicalFixedCenter R L ≤ Z from inf_le_left)]
      exact hcenter ▸ z.toMul.property
    obtain ⟨u,hu,w,hw,he⟩ := Subgroup.mem_sup_of_normal_right.mp hz
    refine Submodule.mem_sup.mpr ⟨j (Additive.ofMul ⟨u,hu⟩), ⟨_,rfl⟩,
      Additive.ofMul w, hw, ?_⟩
    exact congrArg Additive.ofMul he
  let τ : X →* Actor R := (projection R).comp (inclusion hXY)
  let ρ := (representation R).comp τ
  let σ : Representation (ZMod 2) X (Additive (f.Vi 0)) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((lineAction f).comp (inclusion hXU))
  have hcfix (x : X) (z : C) : ρ x z = z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x : G) * (z.val.toMul : G) * (x : G)⁻¹ = (z.val.toMul : G)
    exact mul_inv_eq_iff_eq_mul.mpr
      (z.property.2 x.val (hX.1.trans inf_le_left x.property))
  have hcompat (x : X) (u : Additive (f.Vi 0)) : ρ x (j u) = j (σ x u) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  have hscalar (x : X) (u : Additive (f.Vi 0)) :
      p (σ x u) = (χ x : F.Carrier) * p u := by
    change eF (lineProjection f (lineAction f (inclusion hXU x) u)) = _
    rw [hline x u, map_smul]
    rfl
  obtain ⟨e,hefix,he⟩ := scalar_extension_coordinates hF ρ σ j p C χ hX.odd hj hp
    hχ hker hspan hcfix hcompat hscalar
  let t : X →* cartanImage R X := τ.codRestrict _
    (fun x => mem_map_of_mem (projection R) x.property)
  have ht : Function.Surjective t := by
    rintro ⟨a,y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩
  have htk : t.ker ≤ χ.ker := by
    intro x hx
    change t x = 1 at hx
    have hx' : τ x = 1 := congrArg Subtype.val hx
    have hρ : ρ x = 1 := by change representation R (τ x) = 1; rw [hx',map_one]
    have hh := he x (e.symm (1,0))
    rw [hρ, Module.End.one_apply, e.apply_symm_apply] at hh
    apply Units.ext
    simpa only [mul_one, Units.val_one] using (congrArg Prod.fst hh).symm
  let χbar := t.liftOfSurjective ht ⟨χ,htk⟩
  have hχbar (x : X) : χbar (t x) = χ x := by
    simp only [χbar, MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]
  refine ⟨{ equiv := e, character := χbar, onto := ?_, intertwines := ?_, fixed := hefix }⟩
  · intro a
    obtain ⟨x,hx⟩ := hχ a
    exact ⟨t x, (hχbar x).trans hx⟩
  · intro a z
    obtain ⟨x,rfl⟩ := ht a
    rw [hχbar]
    exact he x z

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
