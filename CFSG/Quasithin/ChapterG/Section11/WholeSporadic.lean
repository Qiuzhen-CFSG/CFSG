module
public import Theory.Representation.BinaryNormalExtension
public import Theory.Representation.JankoTwo.NormalSylowBound
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TraceCompleteness
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.Completeness
public import Theory.Representation.Mathieu.SmallModules.M22Recognition
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.NoFF
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions
public import Theory.Mathieu.M22.Properties.TwoRank

/-!
# Excluding the remaining whole sporadic components

The actual normal M12 and M22 components are recognized in their small
binary degree windows. Their trivial linear centralizers identify every
ambient operator with the native automorphism action, including outer
involutions. The checked displacement bounds then contradict the original
low-rank witness. For J2, relative Sylow normality bounds the original
actor by eight, forcing degree at most eight instead of twelve.

`StrictWholePair` applies these exclusions to the original strict
quotient, with all marked spaces and actions unchanged.
Source: Aschbacher--Smith G.9.3, G.11.7 and H.11--H.13, pp.353--356,367,392--395.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.WholeSporadic
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X} {C : GroupClass}
open Sporadic.Mathieu Representation.BinaryOffender Representation.MathieuSmall
open ChapterH.Section10To12.M12Calculations

private theorem m12_involution_bound (a : MulAut M12) (ha : orderOf a=2) :
    4 ≤ fixedCodim Ambient.automorphismRepresentation (zpowers a) := by
  by_cases hi : a ∈ MulAut.innerSubgroup M12
  · obtain ⟨b,rfl⟩ := hi
    have hb : orderOf b = 2 :=
      (orderOf_injective _ M12AutomorphismRank.conjugation_injective b).symm.trans ha
    have he := fixedSpace_comp_map Ambient.automorphismRepresentation MulAut.conj (zpowers b)
    rw [Ambient.automorphismRepresentation_inner,MonoidHom.map_zpowers] at he
    unfold fixedCodim
    rw [←he]
    exact (fixedCodim_involution b hb).ge
  · exact (LocalActors.fixedCodim_native_outer outer_involution_fusion
      Ambient.automorphismRepresentation Ambient.automorphismRepresentation_faithful hi ha).ge.trans'
        (by decide : 4≤5)

set_option backward.isDefEq.respectTransparency false in
/-- The original rank-two witness excludes a whole M12 component, including
ambient outer involutions. -/
theorem not_mathieu_twelve
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (e : L ≃* M12) : False := by
  let := h9.normal_H
  let := h9.irreducible
  have hd := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hd
  have hb := M12AutomorphismRank.twoRank_le_four
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  obtain ⟨f⟩ := Representation.MathieuSmall.M12Recognition.equiv_heart_of_faithful_finrank_le_ten
    σ (h.faithful.comp (L.subtype_injective.comp e.symm.injective)) (by omega)
  have hf (l : L) (u : V) : f (ρ l u) = m12HeartRepresentation (e l) (f u) := by
    have hh := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (e l) u
    change f (ρ (e.symm (e l)) u) = m12HeartRepresentation (e l) (f u) at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  let φ : G →* MulAut M12 := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L))
  have hφ (g : G) (u : V) : f (ρ g u) = Ambient.automorphismRepresentation (φ g) (f u) :=
    BinaryNormalExtension.equivariant ρ L m12HeartRepresentation
      Ambient.automorphismRepresentation Ambient.automorphismRepresentation_inner
      (fun c hc => Ambient.heart_centralizer c hc) e f.toLinearEquiv hf g u
  obtain ⟨a,_,ho,_,hr,_⟩ := hw.exists_involution h.point_ne_zero
  have hφi : Function.Injective φ := by
    apply (injective_iff_map_eq_one _).mpr
    intro g hg
    apply h.faithful
    ext u
    apply f.injective
    rw [map_one,Module.End.one_apply]
    change f (ρ g u) = f u
    simpa only [hg,map_one,Module.End.one_apply] using hφ g u
  have he := RankTwo.finrank_movedSpace_transport ρ
    (Ambient.automorphismRepresentation.comp φ) (MulEquiv.refl G) f.toLinearEquiv hφ a
  simp only [MulEquiv.refl_apply] at he
  have hlo := m12_involution_bound (φ a) ((orderOf_injective φ hφi a).trans ho)
  rw [fixedCodim_zpowers_eq_displacement_rank] at hlo
  change 4 ≤ finrank (ZMod 2) (RankTwo.movedSpace (Ambient.automorphismRepresentation.comp φ) a) at hlo
  rw [←he] at hlo
  omega

open MathieuCode

set_option backward.isDefEq.respectTransparency false in
private theorem not_m22_model {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (h : Section10.Hypothesis ρ B v W X X₀) [L.Normal]
    (hw : LowRankWitness ρ v X)
    (σ : Representation (ZMod 2) M22 U) [σ.IsIrreducible] [σ.IsAbsolutelyIrreducible]
    (τ : Representation (ZMod 2) (MulAut M22) U) (hi : τ.comp MulAut.conj = σ)
    (hb : ∀ a : MulAut M22, orderOf a=2 → 3 ≤ fixedCodim τ (zpowers a))
    (e : L ≃* M22) (f : V ≃ₗ[ZMod 2] U)
    (hf : ∀ l : L, ∀ u, f (ρ l u) = σ (e l) (f u)) : False := by
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial σ
  let φ : G →* MulAut M22 := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L))
  have hφ (g : G) (u : V) : f (ρ g u) = τ (φ g) (f u) :=
    BinaryNormalExtension.equivariant ρ L σ τ hi
      (BinaryNormalExtension.centralizer_eq_one_of_absolutelyIrreducible σ) e f hf g u
  have hφi : Function.Injective φ := by
    apply (injective_iff_map_eq_one _).mpr
    intro g hg
    apply h.faithful
    ext u
    apply f.injective
    rw [map_one,Module.End.one_apply]
    change f (ρ g u) = f u
    simpa only [hg,map_one,Module.End.one_apply] using hφ g u
  obtain ⟨a,_,ho,_,hr,_⟩ := hw.exists_involution h.point_ne_zero
  have he := RankTwo.finrank_movedSpace_transport ρ (τ.comp φ) (MulEquiv.refl G) f hφ a
  simp only [MulEquiv.refl_apply] at he
  have hlo := hb (φ a) ((orderOf_injective φ hφi a).trans ho)
  rw [fixedCodim_zpowers_eq_displacement_rank] at hlo
  change 3 ≤ finrank (ZMod 2) (RankTwo.movedSpace (τ.comp φ) a) at hlo
  rw [←he] at hlo
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Recognition of both native M22 modules and their full automorphism
extensions excludes every rank-two ambient involution. -/
theorem not_mathieu_twenty_two
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (e : L ≃* M22) : False := by
  let := h9.normal_H
  have hd := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hd
  have hb := m22_automorphism_twoRank_le_five
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  obtain ⟨a,hc | hc⟩ := Representation.MathieuSmall.M22Recognition.of_small_degree σ
    (h.faithful.comp (L.subtype_injective.comp e.symm.injective)) (by omega)
  · obtain ⟨f⟩ := hc
    let := m22Cocode_isIrreducible
    let := m22Cocode_isAbsolutelyIrreducible
    apply not_m22_model h hw m22CocodeRepresentation m22AutCocodeRepresentation
      (by
        apply MonoidHom.ext
        intro g
        apply LinearMap.ext
        intro u
        exact m22AutCocodeRepresentation_inner g u)
      (fun g hg => ?_) (e.trans a) f.toLinearEquiv
      (fun l u => ?_)
    · have hh := (m22Outer_involution_displacement_ge_three
        (m22PairStabilizerEquivAut.symm g)
        ((m22PairStabilizerEquivAut.symm.orderOf_eq g).trans hg)).2
      simpa only [m22AutCocodeRepresentation, m22AutCodeRepresentation,
        fixedCodim_zpowers_eq_displacement_rank, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hh
    · change f (ρ l u) = _
      have hh := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (e l) u
      change f (ρ (e.symm (e l)) u) = m22CocodeRepresentation (a (e l)) (f u) at hh
      rw [e.symm_apply_apply] at hh
      exact hh
  · obtain ⟨f⟩ := hc
    let := m22Code_isIrreducible
    let := m22Code_isAbsolutelyIrreducible
    apply not_m22_model h hw m22CodeRepresentation m22AutCodeRepresentation
      (by
        apply MonoidHom.ext
        intro g
        apply LinearMap.ext
        intro u
        exact m22AutCodeRepresentation_inner g u)
      (fun g hg => ?_) (e.trans a) f.toLinearEquiv
      (fun l u => ?_)
    · have hh := (m22Outer_involution_displacement_ge_three
        (m22PairStabilizerEquivAut.symm g)
        ((m22PairStabilizerEquivAut.symm.orderOf_eq g).trans hg)).1
      simpa only [m22AutCocodeRepresentation, m22AutCodeRepresentation,
        fixedCodim_zpowers_eq_displacement_rank, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hh
    · change f (ρ l u) = _
      have hh := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (e l) u
      change f (ρ (e.symm (e l)) u) = m22CodeRepresentation (a (e l)) (f u) at hh
      rw [e.symm_apply_apply] at hh
      exact hh
/-- Relative normality of the actual elementary actor excludes a whole
Hall–Janko component. No bound on the actor is assumed. -/
theorem not_janko_two
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hn : NormalSylow ρ v X) (e : L ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let := h9.normal_H
  let := h9.irreducible
  obtain ⟨S,_,hXS,hXn⟩ := hn
  have hc := Representation.JankoTwo.normal_elementary_actor_card_le_eight
    ρ h.faithful L e S X hXS hXn
  have he : Nat.card X = 2 ^ finrank (ZMod 2) (Additive X) := by
    rw [← Nat.card_congr (Additive.toMul (α := X))]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X))
  have hr : finrank (ZMod 2) (Additive X) ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (by simpa only [←he] using hc)
  have hd := (setup h).degree_le
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hσi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hσf : Function.Injective σ := h.faithful.comp
    (L.subtype_injective.comp e.symm.injective)
  have hdeg := Representation.JankoTwo.SmallBinaryDegrees.finrank_twelve_of_lt_twentyEight
    σ hσf hσi (by omega)
  omega

end CFSG.Quasithin.ChapterG.Section11.WholeSporadic
