module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Configuration
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# Selecting the original S₃ factor in B.5.8

The noncentral-offender clause of B.1.9 selects a coordinate containing A.
Its marked inclusion makes the kernel of the coordinate projection the actual
complementary subgroup, with multiplication of the two inclusions as product map.

The selected odd factor is the characteristic odd core of the selected S₃.
Odd-order averaging splits its moved and fixed spaces. Equality of the odd-core
and S₃ moved spaces makes this fixed complement S₃-fixed. The faithful action
on the remaining binary plane has trivial invertible commutant, so the other
group factor fixes that plane. These constructions supply every field of
`Configuration`, with the complete universal `EarlierB19` as the only earlier
source input. The later rank bound and B.5.8 induction are separate.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.1.9,
printed pp.71–72, and B.5.8, printed p.106.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
section Plane
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  [Module.Finite (ZMod 2) W]

private theorem plane_centralizer (σ : Representation (ZMod 2) H W)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W = 2)
    (eg : H ≃* Equiv.Perm (Fin 3)) (T : Module.End (ZMod 2) W)
    (hT : Function.Injective T) (hcomm : ∀ g w, T (σ g w) = σ g (T w)) :
    ∀ w, T w = w := by
  let t := eg.symm (Equiv.swap 0 1)
  let u := eg.symm (Equiv.swap 1 2)
  have htt : t * t = 1 := by
    apply eg.injective
    simp only [map_mul, map_one, t, MulEquiv.apply_symm_apply, Equiv.swap_mul_self]
  have huu : u * u = 1 := by
    apply eg.injective
    simp only [map_mul, map_one, u, MulEquiv.apply_symm_apply, Equiv.swap_mul_self]
  have htn : t ≠ 1 := by
    intro he
    have hh := congrArg eg he
    have hn : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
    apply hn
    simpa only [t, MulEquiv.apply_symm_apply, map_one] using hh
  have hun : u ≠ 1 := by
    intro he
    have hh := congrArg eg he
    have hn : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
    apply hn
    simpa only [u, MulEquiv.apply_symm_apply, map_one] using hh
  have htu : t ≠ u := by
    intro he
    have hh := congrArg eg he
    have hn : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ≠ Equiv.swap 1 2 := by decide
    apply hn
    simpa only [t, u, MulEquiv.apply_symm_apply] using hh
  obtain ⟨e,f,ha⟩ := Glauberman.BlockConstruction.PairRecognition.exists_natural_model
    σ hf hd t u htt huu htn hun htu
  let S : Module.End (ZMod 2) (Fin 2 → ZMod 2) :=
    f.toLinearMap.comp (T.comp f.symm.toLinearMap)
  have hS : Function.Injective S := f.injective.comp (hT.comp f.symm.injective)
  obtain ⟨c,hc⟩ := SL2NaturalOffenders.centralizer_scalar S.toAddMonoidHom (by
    intro g v
    obtain ⟨a,rfl⟩ := e.surjective g
    obtain ⟨w,rfl⟩ := f.surjective v
    change f (T (f.symm (specialLinearNatural 2 (e a) (f w)))) =
      specialLinearNatural 2 (e a) (f (T (f.symm (f w))))
    rw [← ha, f.symm_apply_apply, f.symm_apply_apply, hcomm, ha])
  have hc1 : c = 1 := by
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases c with hc0 | hc1
    · have hz : S (1 : Fin 2 → ZMod 2) = S 0 := by
        rw [map_zero]
        simpa only [LinearMap.toAddMonoidHom_coe, hc0, zero_smul] using hc 1
      exact False.elim (one_ne_zero (hS hz))
    · exact hc1
  intro w
  apply f.injective
  have hh := hc (f w)
  simpa only [S, LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, f.symm_apply_apply, hc1, one_smul] using hh

end Plane

universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Delete only the selected coordinate, retaining the other coordinates and residual. -/
private theorem selected_product (d : B19Conclusion ρ) (hg : offenderSubgroup ρ = ⊤)
    (i : Fin d.count) : ∃ B : Subgroup G, Nonempty (InternalProduct (d.factor i) B) := by
  classical
  let R := generatedBy {A | IsBestOffender ρ A} (centralizer (fittingMoved ρ : Set G))
  let e : (((j : Fin d.count) → d.factor j) × R) ≃* G :=
    d.groupProduct.trans ((MulEquiv.subgroupCongr hg).trans Subgroup.topEquiv)
  have hs (a : d.factor i) : e (Pi.mulSingle i a, 1) = a := d.groupProduct_single i a
  let p : G →* d.factor i := {
    toFun g := (e.symm g).1 i
    map_one' := by simp
    map_mul' g h := by simp }
  have hp (a : d.factor i) : p (a : G) = a := by
    change (e.symm (a : G)).1 i = a
    rw [← hs a, e.symm_apply_apply]
    simp
  let B := p.ker
  have hb (b : B) : (e.symm (b : G)).1 i = 1 := b.property
  have hc (a : d.factor i) (b : B) : (a : G) * (b : G) = (b : G) * (a : G) := by
    apply e.symm.injective
    rw [map_mul, map_mul, ← hs a, e.symm_apply_apply]
    apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j
        simp [hb b]
      · simp [Pi.mulSingle_eq_of_ne hj]
    · simp
  let f : (d.factor i × B) →* G := {
    toFun x := (x.1 : G) * (x.2 : G)
    map_one' := by simp
    map_mul' x y := by
      change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
        ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
      simp only [mul_assoc]
      rw [← mul_assoc (y.1 : G), hc y.1 x.2, mul_assoc] }
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a,b⟩ ⟨c,d⟩ he
      have hac : a = c := by
        have hh := congrArg p he
        change p ((a : G) * (b : G)) = p ((c : G) * (d : G)) at hh
        simpa only [map_mul, hp, show p (b : G) = 1 from b.property,
          show p (d : G) = 1 from d.property, mul_one] using hh
      subst c
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel he))
    · intro g
      let a := p g
      have hh : (a : G)⁻¹ * g ∈ B := by
        change p ((a : G)⁻¹ * g) = 1
        rw [map_mul, map_inv, hp]
        exact inv_mul_cancel (p g)
      exact ⟨(a, ⟨(a : G)⁻¹ * g, hh⟩), mul_inv_cancel_left _ _⟩
  exact ⟨B, ⟨⟨MulEquiv.ofBijective f hf, fun _ _ => rfl⟩⟩⟩

private theorem product_commute {A B : Subgroup G} (h : InternalProduct A B)
    (a : A) (b : B) : (a : G) * (b : G) = (b : G) * (a : G) := by
  have hh : h.equiv ((a,1) * (1,b)) = h.equiv ((1,b) * (a,1)) := by simp
  rw [map_mul, map_mul] at hh
  simpa only [h.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using hh

private theorem product_first_normal {A B : Subgroup G} (h : InternalProduct A B) :
    A.Normal := by
  let e : (B × A) ≃* G := MulEquiv.prodComm.trans h.equiv
  let h' : InternalProduct B A := ⟨e, fun b a => (h.apply_eq a b).trans (product_commute h a b)⟩
  exact h'.second_normal

/-- Averaging over the actual odd core also splits the selected S₃ action. -/
private theorem selected_split [Finite G] (d : B19Conclusion ρ) (i : Fin d.count)
    [(d.factor i).Normal] : IsCompl (moved ρ (d.factor i)) (fixedSpace ρ (d.factor i)) := by
  let H := d.factor i
  let N := d.oddFactor i
  have hn : N.Normal := by
    dsimp only [N]
    rw [d.oddFactor_eq i]
    infer_instance
  let : N.Normal := hn
  have hnH : N ≤ H := by
    dsimp only [N, H]
    rw [d.oddFactor_eq i]
    exact Subgroup.map_subtype_le _
  have ho : Odd (Nat.card N) := by
    have he : Nat.card N = 3 := by
      rw [Nat.card_congr (d.oddFactorModel i).toEquiv]
      simp [Nat.card_eq_fintype_card]
    rw [he]
    decide
  have he : RegularCyclicNormalClosure.displacementSpan ρ N ⊤ = moved ρ H := by
    rw [← d.moved_eq i]
    unfold moved subspaceCommutator RegularCyclicNormalClosure.displacementSpan
    congr 1
    ext v
    simp only [eq_comm]
    rfl
  have hc : IsCompl (fixedSpace ρ N) (moved ρ H) := by
    rw [← he]
    exact GoldschmidtONan.isCompl_fixed_moved_of_odd ho
  have hfix : fixedSpace ρ N = fixedSpace ρ H := by
    apply le_antisymm
    · intro v hv a
      apply sub_eq_zero.mp
      apply Submodule.disjoint_def.mp hc.disjoint (ρ a v - v)
      · exact (fixedSpace ρ N).sub_mem
          ((fixedSpace_stable_of_normal ρ N (mem_top (a : G)) v).2 hv) hv
      · exact Submodule.subset_span ⟨a, a.property, v, by trivial, rfl⟩
    · intro v hv n
      exact hv ⟨n, hnH n.property⟩
  rw [hfix] at hc
  exact hc.symm

private theorem configuration_of_b19 [Finite G] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (hg : offenderSubgroup ρ = ⊤)
    (d : B19Conclusion ρ) {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hn : ¬ A ≤ centralizer (fittingSubgroup G : Set G)) :
    Nonempty (Configuration ρ A) := by
  obtain ⟨i,S,hS⟩ := (d.noncentral_offenders A).mp ⟨hA,hn⟩
  obtain ⟨B,⟨hp⟩⟩ := selected_product d hg i
  let : (d.factor i).Normal := product_first_normal hp
  let U := (MovedSection.ofNormal ρ (d.factor i)).space
  let W : Subrepresentation ρ :=
    ⟨fixedSpace ρ (d.factor i), fun g v hv =>
      (fixedSpace_stable_of_normal ρ (d.factor i) (mem_top g) v).2 hv⟩
  have hc : IsCompl U.toSubmodule W.toSubmodule := selected_split d i
  have hfaith : Function.Injective (U.toRepresentation.comp (d.factor i).subtype) :=
    faithful_on_supplement ρ hf (d.factor i) W U hc.symm.sup_eq_top le_rfl
  have hx : U.toSubmodule ≤ fixedSpace ρ B := by
    intro v hv b
    have h := plane_centralizer (U.toRepresentation.comp (d.factor i).subtype)
      hfaith (d.dimension i) (d.factorModel i) (U.toRepresentation (b : G))
      (GoldschmidtONan.action_injective (ρ := U.toRepresentation) (b : G)) (by
        intro a w
        change U.toRepresentation (b : G) (U.toRepresentation (a : G) w) =
          U.toRepresentation (a : G) (U.toRepresentation (b : G) w)
        simp only [← Module.End.mul_apply, ← map_mul]
        exact congrArg (fun g : G => U.toRepresentation g w) (product_commute hp a b).symm)
      (⟨v,hv⟩ : U)
    exact congrArg Subtype.val h
  refine ⟨⟨d.factor i, B, ?_, hp, d.factorModel i, U, rfl, d.dimension i,
    W, rfl, hc, hx⟩⟩
  rw [← hS]
  exact Subgroup.map_subtype_le _

/-- A noncentral minimal best offender selects its original S₃ factor in B.1.9.
The other original coordinates and residual factor form the complementary group.
Odd-core averaging and the faithful binary-plane action give the actual moved
plane and its fixed complement, with the other group fixing the plane. -/
theorem FFHypothesis.fitting_configuration [Finite G] {K : GroupClass.{u}}
    (hyp : FFHypothesis K ρ) (h19 : EarlierB19.{u,v})
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hn : ¬ A ≤ centralizer (fittingSubgroup G : Set G)) :
    Nonempty (Configuration ρ A) := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  obtain ⟨d⟩ := FFHypothesis.b19 hyp h19 hA hn
  exact configuration_of_b19 hyp.faithful hyp.generated d hA hn

end CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
