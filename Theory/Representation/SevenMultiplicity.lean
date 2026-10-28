module
public import Theory.Representation.ScalarMultiplicity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.Representation.EndFieldRep
public import Theory.Representation.BinaryOffender.Homogeneous.Dimension
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.InvolutionFixed

/-!
# An order-seven central action forces three simple copies

Over a Schur field of order two or four, GL₂ has order prime to seven.
The scalar multiplicity representation therefore makes an element of
order dividing seven trivial on one or two copies of a simple module.
A nontrivial commuting action forces at least three copies in a binary
homogeneous module. Three independent copies then add their displacement
ranks whenever the displacement preserves each copy.

This is the multiplicity step in Aschbacher–Smith 5.1.17, printed p.641
(refs/quasithin.pdf), specialized to the remaining degree-three Cartan.
The literal quotient application is in Chapter6's LinearParity extension.
-/

public noncomputable section

open Module
open scoped MonoidAlgebra
namespace Representation.ScalarMultiplicity
variable {k F D C E : Type*} [Field k] [Field F] [Finite F]
  [Group D] [Group C] [AddCommGroup E] [Module F E] [Module k E]
  [Nontrivial E]

private theorem order_seven_eq_one (μ : Representation F C (Fin 2 → F))
    (hF : Nat.card F = 2 ∨ Nat.card F = 4) (a : C) (ha : a ^ 7 = 1) :
    μ a = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let b := Pi.basisFun F (Fin 2)
  let f := (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp μ.asGroupHom
  have hp : f a ^ 7 = 1 := by rw [← map_pow, ha, map_one]
  have hc := orderOf_dvd_natCard (f a)
  have ho := orderOf_dvd_of_pow_eq_one hp
  rw [Matrix.card_GL_field] at hc
  rcases hF with hF | hF
  all_goals
    rw [Nat.card_eq_fintype_card] at hF
    norm_num [Fintype.card_fin, hF, Fin.prod_univ_succ] at hc
    have hdiv := Nat.dvd_gcd hc ho
    norm_num at hdiv
    have he : f a = 1 := hdiv
    have he' : μ.asGroupHom a = 1 :=
      (Matrix.GeneralLinearGroup.toLin' b).symm.injective (he.trans (map_one _).symm)
    exact congrArg Units.val he'

end Representation.ScalarMultiplicity



namespace Representation.ScalarMultiplicity
variable {k F D C E : Type*} [Field k] [Field F] [Finite F]
  [Group D] [Group C] [AddCommGroup E] [Module F E] [Module k E]
  [Nontrivial E]

private theorem double_order_seven_eq_one (σ : Representation k D E)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (hF : Nat.card F = 2 ∨ Nat.card F = 4)
    (ρ : Representation k C (Fin 2 → E))
    (hc : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ d (ρ a x i))
    (a : C) (ha : a ^ 7 = 1) : ρ a = 1 := by
  classical
  obtain ⟨μ,he⟩ := exists_multiplicity σ hs ρ hc
  have hm := order_seven_eq_one μ hF a ha
  apply LinearMap.ext
  intro x
  change ρ a x = x
  have hex : x = ∑ i : Fin 2, Pi.single i (x i) := by ext i; simp
  apply (show ρ a x = ∑ i : Fin 2, ρ a (Pi.single i (x i)) by
    rw [← map_sum, ← hex]).trans
  apply Eq.trans _ hex.symm
  apply Finset.sum_congr rfl
  intro i _
  have hsng : (fun j => (Pi.single i (1 : F) : Fin 2 → F) j • x i) =
      Pi.single i (x i) := by
    ext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]
  rw [← hsng,he,hm]
  rfl

end Representation.ScalarMultiplicity


namespace Representation.SevenMultiplicity
set_option backward.isDefEq.respectTransparency false
variable {k D C E : Type*} [Field k] [Finite k]
  [Group D] [Group C] [AddCommGroup E] [Module k E] [FiniteDimensional k E]

private theorem schur_double_order_seven_eq_one (σ : Representation k D E) [IsIrreducible σ]
    (hF : Nat.card (Module.End k[D] σ.asModule) = 2 ∨
      Nat.card (Module.End k[D] σ.asModule) = 4)
    (ρ : Representation k C (E × E))
    (hc : ∀ a d x, ρ a (σ d x.1, σ d x.2) =
      (σ d (ρ a x).1, σ d (ρ a x).2))
    (a : C) (ha : a ^ 7 = 1) : ρ a = 1 := by
  classical
  let F := Module.End k[D] σ.asModule
  let : Nontrivial σ.asModule := Subrepresentation.irreducible_module_nontrivial σ
  let σ' : Representation k D σ.asModule :=
    (σ.asModuleEquiv.symm.conjAlgEquiv k).toAlgHom.toMonoidHom.comp σ
  have hs (f : σ.asModule →ₗ[k] σ.asModule)
      (hf : ∀ d v, f (σ' d v) = σ' d (f v)) :
      ∃ c : F, ∀ v, f v = c • v := by
    let q := σ.asModuleEquiv.toLinearMap.comp (f.comp σ.asModuleEquiv.symm.toLinearMap)
    have hq : ∀ d v, q (σ d v) = σ d (q v) := by
      intro d v
      exact congrArg σ.asModuleEquiv (hf d (σ.asModuleEquiv.symm v))
    exact ⟨IntertwiningMap.equivAlgEnd σ
      (q.intertwiningMap_of_isIntertwiningMap σ σ hq), fun v => rfl⟩
  let e : (E × E) ≃ₗ[k] (Fin 2 → σ.asModule) :=
    (LinearEquiv.finTwoArrow k E).symm.trans
      (LinearEquiv.piCongrRight fun _ => σ.asModuleEquiv.symm)
  let τ : Representation k C (Fin 2 → σ.asModule) :=
    (e.conjAlgEquiv k).toAlgHom.toMonoidHom.comp ρ
  have he (d : D) (x : E × E) :
      e (σ d x.1, σ d x.2) = fun i => σ' d (e x i) := by
    funext i
    fin_cases i <;> rfl
  have ht : ∀ a d x, τ a (fun i => σ' d (x i)) =
      fun i => σ' d (τ a x i) := by
    intro a d x
    change e (ρ a (e.symm (fun i => σ' d (x i)))) = _
    have hh : e.symm (fun i => σ' d (x i)) =
        (σ d (e.symm x).1, σ d (e.symm x).2) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    rw [hh,hc,he]
    rfl
  have hh := ScalarMultiplicity.double_order_seven_eq_one σ' hs hF τ ht a ha
  apply LinearMap.ext
  intro x
  apply e.injective
  have hv := LinearMap.congr_fun hh (e x)
  change e (ρ a (e.symm (e x))) = e x at hv
  simpa only [e.symm_apply_apply,Module.End.one_apply] using hv

end Representation.SevenMultiplicity

namespace Representation.SevenMultiplicity
set_option backward.isDefEq.respectTransparency false
open Representation.BinaryOffender.Homogeneous
variable {D C E V : Type*} [Group D] [Group C]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem single_order_seven_eq_one (σ : Representation (ZMod 2) D E) [IsIrreducible σ]
    (hF : Nat.card (Module.End (ZMod 2)[D] σ.asModule) = 2 ∨
      Nat.card (Module.End (ZMod 2)[D] σ.asModule) = 4)
    (ρ : Representation (ZMod 2) C E)
    (hc : ∀ a d x, ρ a (σ d x) = σ d (ρ a x))
    (a : C) (ha : a ^ 7 = 1) : ρ a = 1 := by
  have hh := schur_double_order_seven_eq_one σ hF (ρ.prod ρ)
    (fun a d x => Prod.ext (hc a d x.1) (hc a d x.2)) a ha
  ext x
  exact congrArg Prod.fst (LinearMap.congr_fun hh (x,0))

omit [FiniteDimensional (ZMod 2) V] in
private theorem coordinates_order_seven_eq_one (σ : Representation (ZMod 2) D E) [IsIrreducible σ]
    (hF : Nat.card (Module.End (ZMod 2)[D] σ.asModule) = 2 ∨
      Nat.card (Module.End (ZMod 2)[D] σ.asModule) = 4)
    (α : Representation (ZMod 2) D V) (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (α d x) = α d (ρ a x))
    (e : α.Equiv (σ.prod σ)) (a : C) (ha : a ^ 7 = 1) : ρ a = 1 := by
  let τ : Representation (ZMod 2) C (E × E) :=
    (e.toLinearEquiv.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp ρ
  have he (d : D) (x : V) : e (α d x) = (σ d (e x).1, σ d (e x).2) :=
    LinearMap.congr_fun (e.isIntertwining' d) x
  have hh := schur_double_order_seven_eq_one σ hF τ (by
    intro a d x
    change e (ρ a (e.symm (σ d x.1,σ d x.2))) = _
    have hsym : e.symm (σ d x.1,σ d x.2) = α d (e.symm x) := by
      apply e.injective
      change e (e.symm (σ d x.1,σ d x.2)) = e (α d (e.symm x))
      rw [e.apply_symm_apply,he,e.apply_symm_apply]
    rw [hsym,hc,he]
    rfl) a ha
  ext x
  apply e.injective
  change e (ρ a x) = e x
  have hv := LinearMap.congr_fun hh (e x)
  change e (ρ a (e.symm (e x))) = e x at hv
  simpa only [e.symm_apply_apply,Module.End.one_apply] using hv

/-- An order-seven commuting actor is trivial on at most two copies. -/
theorem eq_one_of_order_seven_of_degree_le_double (σ : Representation (ZMod 2) D V)
    (I : Subrepresentation σ) (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤)
    (hF : Nat.card (Module.End (ZMod 2)[D] I.toRepresentation.asModule) = 2 ∨
      Nat.card (Module.End (ZMod 2)[D] I.toRepresentation.asModule) = 4)
    (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (σ d x) = σ d (ρ a x))
    (hd : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) I.toSubmodule)
    (a : C) (ha : a ^ 7 = 1) : ρ a = 1 := by
  let := hi
  by_cases ht : I.toSubmodule = ⊤
  · let e : I.toSubmodule ≃ₗ[ZMod 2] V :=
      LinearEquiv.ofBijective I.toSubmodule.subtype ⟨Subtype.val_injective,
        fun v => ⟨⟨v,ht ▸ Submodule.mem_top⟩,rfl⟩⟩
    let τ : Representation (ZMod 2) C I.toSubmodule :=
      (e.symm.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp ρ
    have he (d : D) (v : I.toSubmodule) : e (I.toRepresentation d v) = σ d (e v) := rfl
    have hτ := single_order_seven_eq_one I.toRepresentation hF τ (by
      intro a d v
      apply e.injective
      change e (e.symm (ρ a (e (I.toRepresentation d v)))) = _
      rw [e.apply_symm_apply,he,hc,he]
      change σ d (ρ a (e v)) = σ d (e (e.symm (ρ a (e v))))
      rw [e.apply_symm_apply]) a ha
    ext v
    have hv := congrArg e (LinearMap.congr_fun hτ (e.symm v))
    change e (e.symm (ρ a (e (e.symm v)))) = e (e.symm v) at hv
    simpa only [e.apply_symm_apply,Module.End.one_apply] using hv
  · obtain ⟨e⟩ := double_coordinates_of_degree_le I hi hh ht hd
    exact coordinates_order_seven_eq_one I.toRepresentation hF σ ρ hc e a ha

/-- A nontrivial commuting order-seven actor forces at least three copies. -/
theorem triple_degree_le_of_order_seven (σ : Representation (ZMod 2) D V)
    (I : Subrepresentation σ) (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤)
    (hF : Nat.card (Module.End (ZMod 2)[D] I.toRepresentation.asModule) = 2 ∨
      Nat.card (Module.End (ZMod 2)[D] I.toRepresentation.asModule) = 4)
    (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (σ d x) = σ d (ρ a x))
    (a : C) (ha : a ^ 7 = 1) (hne : ρ a ≠ 1) :
    3 * finrank (ZMod 2) I.toSubmodule ≤ finrank (ZMod 2) V := by
  by_contra h
  have hd : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) I.toSubmodule := by
    by_cases ht : I.toSubmodule = ⊤
    · rw [ht,finrank_top]; omega
    · exact degree_le_double_of_lt_triple I hi hh ht (by omega)
  exact hne (eq_one_of_order_seven_of_degree_le_double σ I hi hh hF ρ hc hd a ha)

end Representation.SevenMultiplicity

namespace Representation.SevenMultiplicity
open Representation.BinaryOffender.Homogeneous
variable {D C V : Type*} [Group D] [Group C]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

set_option backward.isDefEq.respectTransparency false in
/-- Three independent simple copies add their contributions to a stable linear map. -/
theorem triple_rank_le_of_order_seven (σ : Representation (ZMod 2) D V)
    (I : Subrepresentation σ) (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤)
    (hF : Nat.card (Module.End (ZMod 2)[D] I.toRepresentation.asModule) = 2 ∨
      Nat.card (Module.End (ZMod 2)[D] I.toRepresentation.asModule) = 4)
    (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (σ d x) = σ d (ρ a x))
    (a : C) (ha : a ^ 7 = 1) (hne : ρ a ≠ 1)
    (δ : V →ₗ[ZMod 2] V) (b : ℕ)
    (hs : ∀ J : Subrepresentation σ, SameModule I J → J.toSubmodule.map δ ≤ J.toSubmodule)
    (hb : ∀ J : Subrepresentation σ, SameModule I J →
      b ≤ finrank (ZMod 2) (J.toSubmodule.map δ)) :
    3 * b ≤ finrank (ZMod 2) (LinearMap.range δ) := by
  classical
  have hdim := triple_degree_le_of_order_seven σ I hi hh hF ρ hc a ha hne
  let := hi
  have hp : 0 < finrank (ZMod 2) I.toSubmodule := by
    let : Nontrivial I.toSubmodule :=
      Subrepresentation.irreducible_module_nontrivial I.toRepresentation
    exact Module.finrank_pos
  have hex (N : Subrepresentation σ) (hN : N.toSubmodule ≠ ⊤) :
      ∃ J : Subrepresentation σ, SameModule I J ∧ ¬ J ≤ N := by
    by_contra! h
    apply hN
    apply top_unique
    rw [← hh]
    exact iSup_le fun J => iSup_le fun hJ => h J hJ.2
  have ht : I.toSubmodule ≠ ⊤ := by
    intro ht
    rw [ht,finrank_top] at hdim hp
    omega
  obtain ⟨J,hJ,hJI⟩ := hex I ht
  have hj := hJ.irreducible hi
  have hdis : Disjoint J.toSubmodule I.toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      ((((Subrepresentation.irreducible_iff_isAtom J).mp hj).not_le_iff_disjoint.mp hJI).eq_bot)
  have hdimJ := hJ.choose.finrank_eq
  have hdimIJ := Submodule.finrank_sup_add_finrank_inf_eq I.toSubmodule J.toSubmodule
  rw [hdis.symm.eq_bot,finrank_bot,add_zero] at hdimIJ
  have htop : (I ⊔ J).toSubmodule ≠ ⊤ := by
    intro ht
    change finrank (ZMod 2) (I ⊔ J).toSubmodule = _ at hdimIJ
    rw [ht,finrank_top] at hdimIJ
    omega
  obtain ⟨K,hK,hKIJ⟩ := hex (I ⊔ J) htop
  have hk := hK.irreducible hi
  have hdisK : Disjoint K.toSubmodule (I ⊔ J).toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      ((((Subrepresentation.irreducible_iff_isAtom K).mp hk).not_le_iff_disjoint.mp hKIJ).eq_bot)
  have hδI := hs I (SameModule.refl I)
  have hδJ := hs J hJ
  have hδK := hs K hK
  have hδIJ : (I ⊔ J).toSubmodule.map δ ≤ (I ⊔ J).toSubmodule := by
    change (I.toSubmodule ⊔ J.toSubmodule).map δ ≤ _
    rw [Submodule.map_sup]
    exact sup_le (hδI.trans le_sup_left) (hδJ.trans le_sup_right)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (I.toSubmodule.map δ) (J.toSubmodule.map δ)
  rw [(hdis.symm.mono hδI hδJ).eq_bot,finrank_bot,add_zero,
    ← Submodule.map_sup] at hsum
  have hsumK := Submodule.finrank_sup_add_finrank_inf_eq
    (K.toSubmodule.map δ) ((I ⊔ J).toSubmodule.map δ)
  rw [(hdisK.mono hδK hδIJ).eq_bot,finrank_bot,add_zero,
    ← Submodule.map_sup] at hsumK
  have hle := Submodule.finrank_mono
    (show (K.toSubmodule ⊔ (I ⊔ J).toSubmodule).map δ ≤ LinearMap.range δ from by
      rintro _ ⟨u,_,rfl⟩
      exact ⟨u,rfl⟩)
  have hI := hb I (SameModule.refl I)
  have hJ' := hb J hJ
  have hK' := hb K hK
  change finrank (ZMod 2) ((I ⊔ J).toSubmodule.map δ) = _ at hsum
  omega
end Representation.SevenMultiplicity

namespace Representation.SevenMultiplicity
open Module BinaryOffender BinaryOffender.Homogeneous
open scoped MonoidAlgebra
variable {D C V : Type*} [Group D] [Group C]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem subrepresentation_displacement_rank (σ : Representation (ZMod 2) D V)
    (J : Subrepresentation σ) (y : D) :
    finrank (ZMod 2) (J.toSubmodule.map (σ y - 1)) =
      fixedCodim J.toRepresentation (Subgroup.zpowers y) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have he : (LinearMap.range (J.toRepresentation y - 1)).map J.toSubmodule.subtype =
      J.toSubmodule.map (σ y - 1) := by
    ext v
    constructor
    · rintro ⟨w,⟨u,rfl⟩,rfl⟩
      exact ⟨u,u.property,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨(J.toRepresentation y - 1) ⟨u,hu⟩,⟨⟨u,hu⟩,rfl⟩,rfl⟩
  rw [← he,Submodule.finrank_map_subtype_eq]
  rfl

/-- Every constituent displacement occurs at least three times under a nontrivial
commuting order-seven action. -/
theorem triple_fixedCodim_le_of_order_seven (σ : Representation (ZMod 2) D V)
    (I : Subrepresentation σ) (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤)
    (hF : Nat.card (Module.End (ZMod 2)[D] I.toRepresentation.asModule) = 2 ∨
      Nat.card (Module.End (ZMod 2)[D] I.toRepresentation.asModule) = 4)
    (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (σ d x) = σ d (ρ a x))
    (a : C) (ha : a ^ 7 = 1) (hne : ρ a ≠ 1) (y : D) :
    3 * fixedCodim I.toRepresentation (Subgroup.zpowers y) ≤
      fixedCodim σ (Subgroup.zpowers y) := by
  conv_rhs => rw [fixedCodim_zpowers_eq_displacement_rank]
  change 3 * fixedCodim I.toRepresentation (Subgroup.zpowers y) ≤
    finrank (ZMod 2) (LinearMap.range (σ y - 1))
  apply triple_rank_le_of_order_seven σ I hi hh hF ρ hc a ha hne (σ y - 1)
  · intro J _
    rintro _ ⟨u,hu,rfl⟩
    exact J.toSubmodule.sub_mem (J.apply_mem_toSubmodule y hu) hu
  · intro J hJ
    rw [subrepresentation_displacement_rank]
    obtain ⟨e,he⟩ := hJ
    have hh := fixedCodim_map_equivariant I.toRepresentation J.toRepresentation
      (MonoidHom.id D) e he (Subgroup.zpowers y)
    simpa only [Subgroup.map_id] using hh.le
end Representation.SevenMultiplicity
