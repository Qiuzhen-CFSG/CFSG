module
public import Theory.SpecificGroups.PSL3.IndependentScalarObstruction
public import Theory.SpecificGroups.PSL3.LinearReflectionObstruction
public import Theory.LinearAlgebra.OddDeterminantOneDisplacement

/-!
# Odd actors in a covered paired linear SL₃ action

Both three-spaces retain the same original SL₃ actor, with a prescribed
automorphism on the second. The covering group's odd-prime rank excludes
rank-one displacement on either projection. If a projection is the identity,
the other centralizes SL₃ and is an independent scalar, also excluded by
the three-axis argument. Thus each projection moves at least two field
dimensions. The rank bound remains on the source of the surjection.

Source: Aschbacher--Smith H.4.1, printed p.379, and A.1.31(1).
-/
public section
open Subgroup Matrix Module
namespace Matrix.SL3Reflection
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Group K] [Finite K]
  {p : ℕ} [Fact p.Prime]

omit [Finite F] [CharP F 2] in
private theorem scalar_of_centralizes_SL (S : GL (Fin 3) F)
    (hS : ∀ X : SpecialLinearGroup (Fin 3) F, X.toGL*S=S*X.toGL) :
    ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin 3) c=S := by
  have hm : S.val ∈ Set.range (Matrix.scalar (Fin 3)) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    exact congrArg Units.val (hS ⟨t.toMatrix,by simp⟩)
  have hc := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hm
  rwa [GeneralLinearGroup.center_eq_range_scalar] at hc

private theorem first_ne_one
    (a : MulAut (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (GL (Fin 3) F × GL (Fin 3) F))
    (hSL : ∀ X : SpecialLinearGroup (Fin 3) F, (X.toGL,(a X).toGL) ∈ H)
    (hp : Odd p) (f : K →* H) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (S : H) (ho : orderOf S=p) (α : MulAut (SpecialLinearGroup (Fin 3) F))
    (hfirst : ∀ X, S.val.1*X.toGL*S.val.1⁻¹=(α X).toGL)
    (hsecond : ∀ X, S.val.2*(a X).toGL*S.val.2⁻¹=(a (α X)).toGL) : S.val.1 ≠ 1 := by
  intro hzero
  have hα (X : SpecialLinearGroup (Fin 3) F) : α X=X := by
    apply SpecialLinearGroup.toGL_injective
    simpa only [hzero,one_mul,inv_one,mul_one] using (hfirst X).symm
  obtain ⟨c,hc⟩ := scalar_of_centralizes_SL S.val.2 (by
    intro X
    have hh := hsecond (a.symm X)
    rw [hα,a.apply_symm_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm)
  have hpair : S.val=(1,GeneralLinearGroup.scalar (Fin 3) c) := Prod.ext hzero hc.symm
  have horder : orderOf (GeneralLinearGroup.scalar (Fin 3) c)=p := by
    have hh := (orderOf_injective H.subtype H.subtype_injective S).trans ho
    change orderOf S.val=p at hh
    rw [hpair] at hh
    let i : GL (Fin 3) F →* GL (Fin 3) F × GL (Fin 3) F := MonoidHom.inr _ _
    have hi : Function.Injective i := fun _ _ he => congrArg Prod.snd he
    exact (orderOf_injective i hi _).symm.trans hh
  have hscalar : Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Fˣ →* GL (Fin 3) F) := by
    intro u v he
    apply Units.ext
    exact congrArg (fun X : GL (Fin 3) F => X.val 0 0) he
  have hcorder : orderOf c=p := (orderOf_injective _ hscalar c).symm.trans horder
  exact no_independent_scalar_in_rank_two_section (SpecialLinearGroup.toGL.comp a.toMonoidHom)
    H hSL hp f hf hrank c hcorder (hpair ▸ S.property)

private theorem first_two_le
    (a : MulAut (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (GL (Fin 3) F × GL (Fin 3) F))
    (hSL : ∀ X : SpecialLinearGroup (Fin 3) F, (X.toGL,(a X).toGL) ∈ H)
    (hp : Odd p) (f : K →* H) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (S : H) (ho : orderOf S=p) (α : MulAut (SpecialLinearGroup (Fin 3) F))
    (hfirst : ∀ X, S.val.1*X.toGL*S.val.1⁻¹=(α X).toGL)
    (hsecond : ∀ X, S.val.2*(a X).toGL*S.val.2⁻¹=(a (α X)).toGL) :
    2 ≤ finrank F (LinearMap.range (Matrix.toLin' S.val.1.val - LinearMap.id)) := by
  have hne := first_ne_one a H hSL hp f hf hrank S ho α hfirst hsecond
  let π : H →* GL (Fin 3) F := (MonoidHom.fst _ _).comp H.subtype
  have hsorder : orderOf S.val.1=p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp (ho ▸ orderOf_map_dvd π S)).resolve_left
      (fun he => hne (orderOf_eq_one_iff.mp he))
  let e := (GeneralLinearGroup.toLin S.val.1).toLinearEquiv
  have he : e.toLinearMap=Matrix.toLin' S.val.1.val := rfl
  have hene : e ≠ 1 := by
    intro heq
    apply hne
    apply GeneralLinearGroup.toLin.injective
    apply Units.ext
    rw [map_one]
    change Matrix.toLin' S.val.1.val=LinearMap.id
    rw [←he]
    exact congrArg LinearEquiv.toLinearMap heq
  have heorder : orderOf e=orderOf S.val.1 :=
    orderOf_injective
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).toMonoidHom.comp
        GeneralLinearGroup.toLin.toMonoidHom)
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).injective.comp
        GeneralLinearGroup.toLin.injective) S.val.1
  by_contra! hsmall
  have hpos : 0 < finrank F (LinearMap.range (Matrix.toLin' S.val.1.val - LinearMap.id)) := by
    by_contra! hz
    have hh := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz))
    apply hene
    apply LinearEquiv.toLinearMap_injective
    exact sub_eq_zero.mp hh
  have hr : finrank F (LinearMap.range (Matrix.toLin' S.val.1.val - LinearMap.id))=1 := by omega
  have hd : GeneralLinearGroup.det S.val.1 ≠ 1 := by
    intro hd
    have hdet : e.det=1 := by
      apply Units.ext
      rw [LinearEquiv.coe_det,he,LinearMap.det_toLin']
      exact congrArg Units.val hd
    have hb := e.two_le_displacement_of_odd_det_one hene (heorder ▸ hsorder ▸ hp) hdet
    rw [he] at hb
    omega
  apply no_linear_reflection_in_injective_image (MonoidHom.id _) Function.injective_id
    (π.comp f) hrank hp ?_ S.val.1 ?_ hsorder hr hd
  · intro X
    obtain ⟨k,hk⟩ := hf ⟨(X.toGL,(a X).toGL),hSL X⟩
    exact ⟨k,congrArg π hk⟩
  · obtain ⟨k,hk⟩ := hf S
    exact ⟨k,congrArg π hk⟩

/-- An odd-prime actor on a paired linear SL₃ module moves at least four
field dimensions when its actual covering group has prime rank at most two. -/
theorem paired_linear_odd_displacement_of_cover
    (a : MulAut (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (GL (Fin 3) F × GL (Fin 3) F))
    (hSL : ∀ X : SpecialLinearGroup (Fin 3) F, (X.toGL,(a X).toGL) ∈ H)
    (hp : Odd p) (f : K →* H) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (S : H) (ho : orderOf S=p) (α : MulAut (SpecialLinearGroup (Fin 3) F))
    (hfirst : ∀ X, S.val.1*X.toGL*S.val.1⁻¹=(α X).toGL)
    (hsecond : ∀ X, S.val.2*(a X).toGL*S.val.2⁻¹=(a (α X)).toGL) :
    4 ≤ finrank F (LinearMap.range (Matrix.toLin' S.val.1.val - LinearMap.id)) +
      finrank F (LinearMap.range (Matrix.toLin' S.val.2.val - LinearMap.id)) := by
  have h1 := first_two_le a H hSL hp f hf hrank S ho α hfirst hsecond
  let swap : GL (Fin 3) F × GL (Fin 3) F ≃* GL (Fin 3) F × GL (Fin 3) F := MulEquiv.prodComm
  let H' := H.map swap.toMonoidHom
  let E := H.equivMapOfInjective swap.toMonoidHom swap.injective
  have hSL' (X : SpecialLinearGroup (Fin 3) F) : (X.toGL,(a.symm X).toGL) ∈ H' := by
    refine ⟨((a.symm X).toGL,(a (a.symm X)).toGL),hSL (a.symm X),?_⟩
    simp [swap]
  let S' := E S
  have hS' : S'.val=(S.val.2,S.val.1) := rfl
  have ho' : orderOf S'=p := (orderOf_injective E.toMonoidHom E.injective S).trans ho
  let α' := MulAut.congr a α
  have hf' (X : SpecialLinearGroup (Fin 3) F) :
      S'.val.1*X.toGL*S'.val.1⁻¹=(α' X).toGL := by
    rw [hS']
    change S.val.2*X.toGL*S.val.2⁻¹=(a (α (a.symm X))).toGL
    simpa only [a.apply_symm_apply] using hsecond (a.symm X)
  have hs' (X : SpecialLinearGroup (Fin 3) F) :
      S'.val.2*(a.symm X).toGL*S'.val.2⁻¹=(a.symm (α' X)).toGL := by
    rw [hS']
    simpa only [α',MulAut.congr_apply,MulEquiv.trans_apply,a.symm_apply_apply]
      using hfirst (a.symm X)
  have h2 := first_two_le a.symm H' hSL' hp (E.toMonoidHom.comp f)
    (E.surjective.comp hf) hrank S' ho' α' hf' hs'
  rw [hS'] at h2
  exact Nat.add_le_add h1 h2

/-- The paired bound in an injective ambient image, with the covering group
restricted to the field-linear part rather than assigning rank to a quotient. -/
theorem paired_linear_odd_displacement_in_injective_image
    {B : Type*} [Group B]
    (a : MulAut (SpecialLinearGroup (Fin 3) F))
    (r : GL (Fin 3) F × GL (Fin 3) F →* B) (hinj : Function.Injective r)
    (f : K →* B) (hrank : primeRank p K ≤ 2) (hp : Odd p)
    (hSL : ∀ X : SpecialLinearGroup (Fin 3) F, r (X.toGL,(a X).toGL) ∈ f.range)
    (S : GL (Fin 3) F × GL (Fin 3) F) (hS : r S ∈ f.range) (ho : orderOf S=p)
    (α : MulAut (SpecialLinearGroup (Fin 3) F))
    (hfirst : ∀ X, S.1*X.toGL*S.1⁻¹=(α X).toGL)
    (hsecond : ∀ X, S.2*(a X).toGL*S.2⁻¹=(a (α X)).toGL) :
    4 ≤ finrank F (LinearMap.range (Matrix.toLin' S.1.val - LinearMap.id)) +
      finrank F (LinearMap.range (Matrix.toLin' S.2.val - LinearMap.id)) := by
  let P := r.range.comap f
  let e := MonoidHom.ofInjective hinj
  let g : P →* GL (Fin 3) F × GL (Fin 3) F :=
    e.symm.toMonoidHom.comp (f.subgroupComap r.range)
  have hpre (A : GL (Fin 3) F × GL (Fin 3) F) (hA : r A ∈ f.range) : A ∈ g.range := by
    obtain ⟨k,hk⟩ := hA
    have hkP : k ∈ P := ⟨A,hk.symm⟩
    refine ⟨⟨k,hkP⟩,?_⟩
    apply hinj
    change (e (e.symm ⟨f k,hkP⟩)).val = r A
    rw [e.apply_symm_apply]
    exact hk
  let S' : g.range := ⟨S,hpre S hS⟩
  have horder : orderOf S'=p :=
    (orderOf_injective g.range.subtype g.range.subtype_injective S').symm.trans ho
  exact paired_linear_odd_displacement_of_cover a g.range
    (fun X => hpre _ (hSL X)) hp g.rangeRestrict g.rangeRestrict_surjective
    ((primeRank_subgroup_le p P).trans hrank) S' horder α hfirst hsecond
end Matrix.SL3Reflection
