module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionLinearThreeFF
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionLinearThree
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.NormalType

/-!
# Inner actors on the two quotient constituent types

An elementary actor inducing inner automorphisms of a normal component
fixes each simple module type. Odd-copy selection gives invariant copies.
The centralizing difference between the actor and its inner lift acts
trivially on every such copy: its displacement is a square-zero
intertwining endomorphism, so Schur's lemma applies in characteristic two.

Two distinct natural SL₃ types therefore exclude an offender whenever
the inner lift is injective. Disjoint component copies pass through the
literal invariant quotient, so the same result applies there without
assuming that the original copies were actor-invariant. The actual
chosen-seed application is SeedAlternativesMovedExhaustionQuotientFF.

Source: Aschbacher--Smith D.3.9(1), D.3.13 and B.4.9(2), printed
pp.92--94 and199--202. Full Source325 assembly remains with qt-baumann-fsu.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]

private theorem square_one_intertwiner_eq_id
    (σ : Representation (ZMod 2) H E) [IsIrreducible σ]
    (f : σ.IntertwiningMap σ) (hf : ∀ v, f (f v) = v) : ∀ v, f v = v := by
  let d : σ.IntertwiningMap σ := f - 1
  have hd (v : E) : d (d v) = 0 := by
    change f (f v - v) - (f v - v) = 0
    rw [map_sub,hf]
    have htwo (w : E) : w + w = 0 := by
      have he := @two_smul (ZMod 2) E _ _ _ w
      have hz : (2 : ZMod 2) = 0 := by decide
      rw [hz,zero_smul] at he
      exact he.symm
    have hn (w : E) : -w = w := neg_eq_iff_add_eq_zero.mpr (htwo w)
    simp only [sub_eq_add_neg,hn]
    rw [add_assoc,←add_assoc (f v),htwo,zero_add,htwo]
  have hz : d = 0 := by
    rcases IsIrreducible.injective_or_eq_zero d with hi | hz
    · ext v
      apply hi
      simpa using hd v
    · exact hz
  intro v
  exact sub_eq_zero.mp (congrArg (fun q : σ.IntertwiningMap σ => q v) hz)

/-- An inner elementary actor agrees with its lift on every invariant
irreducible component submodule. The centralizing difference is unipotent
and hence trivial by Schur's lemma in characteristic two. -/
private theorem inner_lift_agrees_on_irreducible
    (ρ : Representation (ZMod 2) H E) (K A : Subgroup H)
    (hA : IsElementaryAbelian 2 A) (f : A →* K)
    (he : ∀ (a : A) (k : K), a.val*k.val*a.val⁻¹ = (f a : H)*k.val*(f a : H)⁻¹)
    (I : Subrepresentation (ρ.comp K.subtype)) (hi : IsIrreducible I.toRepresentation)
    (hs : A ≤ subspaceStabilizer ρ I.toSubmodule) :
    ∀ (a : A) (v : I), ρ a.val v.val = ρ (f a : H) v.val := by
  let := hi
  let := hA
  intro a
  have ha : a.val ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a.val a.property
  have hfa : (f a : H)^2 = 1 := by
    change ((f a)^2 : K).val = (1 : K).val
    rw [←map_pow,show a^2 = 1 from Subtype.ext ha,map_one]
  have hcomm : Commute a.val (f a : H) := by
    have hh := he a (f a)
    simp only [mul_inv_cancel_right] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let x : H := (f a : H)⁻¹*a.val
  have hx : x^2 = 1 := by
    dsimp [x]
    rw [hcomm.symm.inv_left.mul_pow,inv_pow,hfa,ha,inv_one,one_mul]
  have hc : x ∈ centralizer (K : Set H) := by
    intro k hk
    have hh := he a ⟨k,hk⟩
    change k*x = x*k
    dsimp [x]
    calc
      k*((f a : H)⁻¹*a.val) = (f a : H)⁻¹*((f a : H)*k*(f a : H)⁻¹)*a.val := by group
      _ = (f a : H)⁻¹*(a.val*k*a.val⁻¹)*a.val := by rw [hh]
      _ = _ := by group
  have hxi : ∀ v ∈ I.toSubmodule, ρ x v ∈ I.toSubmodule := by
    intro v hv
    change ρ ((f a : H)⁻¹*a.val) v ∈ I.toSubmodule
    rw [map_mul,Module.End.mul_apply]
    exact I.apply_mem_toSubmodule (f a)⁻¹ ((hs a.property v).mpr hv)
  let d : I.toRepresentation.IntertwiningMap I.toRepresentation := {
    toLinearMap := (ρ x).restrict hxi
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change ρ x (ρ k.val v.val) = ρ k.val (ρ x v.val)
      rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,hc k.val k.property] }
  have hd := square_one_intertwiner_eq_id I.toRepresentation d (by
    intro v
    apply Subtype.ext
    change ρ x (ρ x v.val) = v.val
    rw [←Module.End.mul_apply,←map_mul,←pow_two,hx,map_one,Module.End.one_apply])
  intro v
  have hv := congrArg Subtype.val (hd v)
  have hh := congrArg (ρ (f a : H)) hv
  change ρ (f a : H) (ρ x v.val) = ρ (f a : H) v.val at hh
  simpa only [←Module.End.mul_apply,←map_mul,x,mul_inv_cancel_left] using hh

/-- Inner action fixes every simple module type, so odd-copy selection
constructs an actual invariant copy of that type. -/
private theorem exists_inner_invariant_copy
    (ρ : Representation (ZMod 2) H E) [Finite E]
    (K : Subgroup H) [K.Normal] (A : Subgroup H) (hA : IsPGroup 2 A)
    (f : A →* K)
    (he : ∀ (a : A) (k : K), a.val*k.val*a.val⁻¹ = (f a : H)*k.val*(f a : H)⁻¹)
    (I : Subrepresentation (ρ.comp K.subtype)) (hi : IsIrreducible I.toRepresentation) :
    ∃ J : Subrepresentation (ρ.comp K.subtype), SameModule I J ∧
      IsIrreducible J.toRepresentation ∧ A ≤ subspaceStabilizer ρ J.toSubmodule := by
  have ht (a : A) : SameModule I ((normalTypeAction ρ K).conjugate a.val I) := by
    have hc : (f a : H)⁻¹*a.val ∈ centralizer (K : Set H) := by
      intro k hk
      have hh := he a ⟨k,hk⟩
      change k*((f a : H)⁻¹*a.val) = ((f a : H)⁻¹*a.val)*k
      calc
        _ = (f a : H)⁻¹*((f a : H)*k*(f a : H)⁻¹)*a.val := by group
        _ = (f a : H)⁻¹*(a.val*k*a.val⁻¹)*a.val := by rw [hh]
        _ = _ := by group
    have h1 := normal_le_typeInertia ρ K I (f a).property
    have h2 := centralizer_le_typeInertia ρ K I hc
    have hm := ((normalTypeAction ρ K).inertia I).mul_mem h1 h2
    have hm' : a.val ∈ (normalTypeAction ρ K).inertia I := by
      simpa only [mul_inv_cancel_left] using hm
    exact hm'
  obtain ⟨J,hs,hj,hfix⟩ := fixed_simple_copy ρ K A hA I hi ht
  refine ⟨J,hs,hj,?_⟩
  intro a ha
  exact (subspace_map_eq_iff ρ J.toSubmodule a).mp (hfix ⟨a,ha⟩)


/-- Two distinct natural SL₃ types exclude an offender from any elementary
actor which embeds into the component and induces that inner action.
The input copies need not be invariant under the actor. -/
theorem not_offender_of_inner_two_natural_types
    (ρ : Representation (ZMod 2) H E) [Finite E]
    (K : Subgroup H) [K.Normal] (A : Subgroup H) (hA : IsElementaryTwo A)
    (f : A →* K) (hf : Function.Injective f)
    (he : ∀ (a : A) (k : K), a.val*k.val*a.val⁻¹ = (f a : H)*k.val*(f a : H)⁻¹)
    (I J : Subrepresentation (ρ.comp K.subtype))
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (F : BinaryField)
    (a : ActionEquiv I.toRepresentation (linearNatural F 3))
    (b : ActionEquiv J.toRepresentation (linearNatural F 3))
    (hne : ¬ SameModule I J) : ¬ IsOffender ρ A := by
  let := hA.2
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  obtain ⟨I',hii,hi',hAI⟩ := exists_inner_invariant_copy ρ K A
    (IsElementaryAbelian.isPGroup 2 A) f he I hi
  obtain ⟨J',hjj,hj',hAJ⟩ := exists_inner_invariant_copy ρ K A
    (IsElementaryAbelian.isPGroup 2 A) f he J hj
  let ei : I.toRepresentation.Equiv I'.toRepresentation :=
    .mk hii.choose (fun k => LinearMap.ext (hii.choose_spec k))
  let ej : J.toRepresentation.Equiv J'.toRepresentation :=
    .mk hjj.choose (fun k => LinearMap.ext (hjj.choose_spec k))
  have hne' : ¬ Nonempty (I'.toRepresentation.Equiv J'.toRepresentation) := by
    rintro ⟨c⟩
    let e := ei.trans (c.trans ej.symm)
    exact hne ⟨e.toLinearEquiv,fun k v => LinearMap.congr_fun (e.isIntertwining' k) v⟩
  have hd : Disjoint I'.toSubmodule J'.toSubmodule := by
    have hh := ((Subrepresentation.irreducible_iff_isAtom I').mp hi').disjoint_of_ne
      ((Subrepresentation.irreducible_iff_isAtom J').mp hj') (fun hz =>
        hne' ⟨Representation.Equiv.mk (LinearEquiv.ofEq _ _
          (congrArg Subrepresentation.toSubmodule hz)) (by subst J'; intro k; rfl)⟩)
    exact disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hh.eq_bot)
  let a' : ActionEquiv I'.toRepresentation (linearNatural F 3) :=
    ⟨a.groupEquiv,ei.symm.toLinearEquiv.trans a.linearEquiv,by
      intro k v
      exact (congrArg a.linearEquiv (LinearMap.congr_fun (ei.symm.isIntertwining' k) v)).trans
        (a.intertwines k (ei.symm v))⟩
  let b' : ActionEquiv J'.toRepresentation (linearNatural F 3) :=
    ⟨b.groupEquiv,ej.symm.toLinearEquiv.trans b.linearEquiv,by
      intro k v
      exact (congrArg b.linearEquiv (LinearMap.congr_fun (ej.symm.isIntertwining' k) v)).trans
        (b.intertwines k (ej.symm v))⟩
  let c := I'.toSubmodule.subtype.coprod J'.toSubmodule.subtype
  have hc : Function.Injective c := by
    apply (injective_iff_map_eq_zero c).mpr
    intro v hv
    change v.1.val + v.2.val = 0 at hv
    have hu : v.1.val ∈ J'.toSubmodule := by
      rw [eq_neg_of_add_eq_zero_left hv]
      exact J'.toSubmodule.neg_mem v.2.property
    have hz := (Submodule.disjoint_def.mp hd) v.1.val v.1.property hu
    have hw : v.2.val = 0 := by simpa only [hz,zero_add] using hv
    exact Prod.ext (Subtype.ext hz) (Subtype.ext hw)
  intro hoff
  have hh := (hoff.subgroupOf ρ le_rfl).map_of_embedding
    (ρ.comp A.subtype) (I'.toRepresentation.prod J'.toRepresentation) f c hc
    (by
      intro z v
      change ρ z.val (v.1.val + v.2.val) =
        ρ (f z : H) v.1.val + ρ (f z : H) v.2.val
      rw [map_add,inner_lift_agrees_on_irreducible ρ K A hA.2 f he I' hi' hAI,
        inner_lift_agrees_on_irreducible ρ K A hA.2 f he J' hj' hAJ]) hf
  exact hne' (LinearThreePair.same_of_ff _ _ F a' b' ⟨_,hh⟩)


/-- A component submodule disjoint from the actual invariant subspace
embeds equivariantly into its literal quotient. -/
private theorem quotient_contains_disjoint_copy
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H)
    (S : Subrepresentation ρ) (I : Subrepresentation (ρ.comp K.subtype))
    (hd : Disjoint I.toSubmodule S.toSubmodule) :
    ∃ J : Subrepresentation (S.quotientRepresentation.comp K.subtype),
      Nonempty (I.toRepresentation.Equiv J.toRepresentation) := by
  let f : I.toRepresentation.IntertwiningMap (S.quotientRepresentation.comp K.subtype) := {
    toLinearMap := S.toSubmodule.mkQ.comp I.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f.toLinearMap).mpr
    intro v hv
    exact Subtype.ext ((Submodule.disjoint_def.mp hd) v.val v.property
      ((Submodule.Quotient.mk_eq_zero _).mp hv))
  let e : I.toSubmodule ≃ₗ[ZMod 2] f.range.toSubmodule := LinearEquiv.ofInjective f.toLinearMap hf
  exact ⟨f.range,⟨.mk e (by intro k; rfl)⟩⟩

/-- Disjoint simple copies retain their natural models and their distinct
component-module types in the literal quotient. -/
private theorem quotient_natural_type_pair
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H)
    (S : Subrepresentation ρ) (I J : Subrepresentation (ρ.comp K.subtype))
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (hIS : Disjoint I.toSubmodule S.toSubmodule) (hJS : Disjoint J.toSubmodule S.toSubmodule)
    (F : BinaryField)
    (a : ActionEquiv I.toRepresentation (linearNatural F 3))
    (b : ActionEquiv J.toRepresentation (linearNatural F 3))
    (hne : ¬ SameModule I J) :
    ∃ I' J' : Subrepresentation (S.quotientRepresentation.comp K.subtype),
      IsIrreducible I'.toRepresentation ∧ IsIrreducible J'.toRepresentation ∧
      Nonempty (ActionEquiv I'.toRepresentation (linearNatural F 3)) ∧
      Nonempty (ActionEquiv J'.toRepresentation (linearNatural F 3)) ∧ ¬ SameModule I' J' := by
  obtain ⟨I',⟨ei⟩⟩ := quotient_contains_disjoint_copy ρ K S I hIS
  obtain ⟨J',⟨ej⟩⟩ := quotient_contains_disjoint_copy ρ K S J hJS
  let a' : ActionEquiv I'.toRepresentation (linearNatural F 3) :=
    ⟨a.groupEquiv,ei.symm.toLinearEquiv.trans a.linearEquiv,by
      intro k v
      exact (congrArg a.linearEquiv (LinearMap.congr_fun (ei.symm.isIntertwining' k) v)).trans
        (a.intertwines k (ei.symm v))⟩
  let b' : ActionEquiv J'.toRepresentation (linearNatural F 3) :=
    ⟨b.groupEquiv,ej.symm.toLinearEquiv.trans b.linearEquiv,by
      intro k v
      exact (congrArg b.linearEquiv (LinearMap.congr_fun (ej.symm.isIntertwining' k) v)).trans
        (b.intertwines k (ej.symm v))⟩
  refine ⟨I',J',(RepEquiv.irreducible_euqiv ⟨ei.toLinearEquiv,ei.isIntertwining'⟩).mp hi,
    (RepEquiv.irreducible_euqiv ⟨ej.toLinearEquiv,ej.isIntertwining'⟩).mp hj,⟨a'⟩,⟨b'⟩,?_⟩
  intro hs
  let c : I'.toRepresentation.Equiv J'.toRepresentation :=
    .mk hs.choose (fun k => LinearMap.ext (hs.choose_spec k))
  let e := ei.trans (c.trans ej.symm)
  exact hne ⟨e.toLinearEquiv,fun k v => LinearMap.congr_fun (e.isIntertwining' k) v⟩


/-- The quotient exclusion keeps the same actor and its injective inner
lift, using the two genuine component copies disjoint from the kernel. -/
theorem not_offender_quotient_of_inner_two_natural_types
    (ρ : Representation (ZMod 2) H E) [Finite E]
    (K : Subgroup H) [K.Normal] (A : Subgroup H) (hA : IsElementaryTwo A)
    (f : A →* K) (hf : Function.Injective f)
    (he : ∀ (a : A) (k : K), a.val*k.val*a.val⁻¹ = (f a : H)*k.val*(f a : H)⁻¹)
    (S : Subrepresentation ρ) (I J : Subrepresentation (ρ.comp K.subtype))
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (hIS : Disjoint I.toSubmodule S.toSubmodule) (hJS : Disjoint J.toSubmodule S.toSubmodule)
    (F : BinaryField)
    (a : ActionEquiv I.toRepresentation (linearNatural F 3))
    (b : ActionEquiv J.toRepresentation (linearNatural F 3))
    (hne : ¬ SameModule I J) : ¬ IsOffender S.quotientRepresentation A := by
  let : Finite (E ⧸ S.toSubmodule) := Finite.of_surjective _ S.toSubmodule.mkQ_surjective
  obtain ⟨I',J',hi',hj',⟨a'⟩,⟨b'⟩,hne'⟩ :=
    quotient_natural_type_pair ρ K S I J hi hj hIS hJS F a b hne
  exact not_offender_of_inner_two_natural_types S.quotientRepresentation K A hA f hf he
    I' J' hi' hj' F a' b' hne'

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
