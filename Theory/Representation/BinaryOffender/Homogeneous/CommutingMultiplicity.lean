module
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.EndFieldRep
public import Theory.Representation.BinaryOffender.Homogeneous.Dimension
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.ThreeCopies
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.RepEquiv
public import Theory.Representation.BinaryOffender.Homogeneous.Embedding
public import Theory.Representation.BinaryOffender.HomogeneousOrbitKernel
public import Theory.Representation.BinaryOffender.RatioInheritance
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Multiplicity in a commuting binary orbit

An order-four operator with nontrivial square requires at least three copies
of an irreducible binary constituent in a homogeneous module: on two copies,
Schur's finite endomorphism field reduces the operator to a two-dimensional
unipotent matrix, whose square is one. Conversely, a positive fixed-codimension
cost and a budget of twice that cost permit at most two copies.

Both bounds apply to the literal orbit under a commuting group. The pointwise
actor kernel is unchanged on that orbit. The Suzuki support application uses
these bounds with the same starred actor, including its kernel.
The order-four calculation adapts the private argument in
CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportMultiplicity;
this independent formulation has no classification-layer dependencies.
Source: Aschbacher--Smith A.1.41--42 and D.3.9, printed pp.31--32,200--201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MonoidAlgebra
namespace Representation.BinaryOffender.Homogeneous.CommutingMultiplicity
set_option backward.isDefEq.respectTransparency false

private theorem square_of_fourth {F : Type*} [Field F] [CharP F 2]
    (u : Module.End F (Fin 2 → F)) (hu : u^4=1) : u^2=1 := by
  let : CharP (Module.End F (Fin 2 → F)) 2 := charP_of_injective_algebraMap' F 2
  have h4 : (u-1)^4=0 := by
    have h := sub_pow_char_pow_of_commute (R := Module.End F (Fin 2 → F)) 2 2
      (Commute.one_right u)
    simpa only [show 2^2=4 from rfl,hu,one_pow,sub_self] using h
  have hker := Module.End.ker_pow_le_ker_pow_finrank (u-1) 4
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,h4,LinearMap.ker_zero] at hker
  have h2 : (u-1)^2=0 := LinearMap.ker_eq_top.mp (top_le_iff.mp hker)
  have h := sub_pow_char_of_commute (R := Module.End F (Fin 2 → F)) 2 (Commute.one_right u)
  rw [h2,one_pow] at h
  exact sub_eq_zero.mp h.symm

private theorem double_fourth_square
    {F D C E : Type*} [Field F] [CharP F 2]
    [Group D] [Group C] [AddCommGroup E] [Module F E] [Module (ZMod 2) E] [Nontrivial E]
    (σ : Representation (ZMod 2) D E)
    (hs : ∀ (f : E →ₗ[ZMod 2] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (ρ : Representation (ZMod 2) C (Fin 2 → E))
    (hc : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ d (ρ a x i))
    (a : C) (ha : a^4=1) : ρ (a^2)=1 := by
  classical
  obtain ⟨μ,he⟩ := ScalarMultiplicity.exists_multiplicity σ hs ρ hc
  have hm : μ (a^2) = 1 := by
    rw [map_pow]
    exact square_of_fourth (μ a) (by rw [←map_pow,ha,map_one])
  apply LinearMap.ext
  intro x
  change ρ (a^2) x = x
  have hex : x = ∑ i : Fin 2, Pi.single i (x i) := by ext i; simp
  conv_lhs => rw [hex,map_sum]
  apply Eq.trans _ hex.symm
  apply Finset.sum_congr rfl
  intro i _
  have hsng : (fun j => (Pi.single i (1 : F) : Fin 2 → F) j • x i) =
      Pi.single i (x i) := by
    ext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]
  rw [←hsng,he,hm]
  rfl

variable {D C E V : Type*} [Group D] [Group C]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
private theorem schur_double_fourth_square (σ : Representation (ZMod 2) D E) [IsIrreducible σ]
    (ρ : Representation (ZMod 2) C (E × E))
    (hc : ∀ a d x, ρ a (σ d x.1, σ d x.2) =
      (σ d (ρ a x).1, σ d (ρ a x).2))
    (a : C) (ha : a ^ 4 = 1) : ρ (a^2) = 1 := by
  classical
  let F := Module.End (ZMod 2)[D] σ.asModule
  let : Nontrivial σ.asModule := Subrepresentation.irreducible_module_nontrivial σ
  let : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  let σ' : Representation (ZMod 2) D σ.asModule :=
    (σ.asModuleEquiv.symm.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp σ
  have hs (f : σ.asModule →ₗ[ZMod 2] σ.asModule)
      (hf : ∀ d v, f (σ' d v) = σ' d (f v)) :
      ∃ c : F, ∀ v, f v = c • v := by
    let q := σ.asModuleEquiv.toLinearMap.comp (f.comp σ.asModuleEquiv.symm.toLinearMap)
    have hq : ∀ d v, q (σ d v) = σ d (q v) := by
      intro d v
      exact congrArg σ.asModuleEquiv (hf d (σ.asModuleEquiv.symm v))
    exact ⟨IntertwiningMap.equivAlgEnd σ
      (q.intertwiningMap_of_isIntertwiningMap σ σ hq), fun v => rfl⟩
  let e : (E × E) ≃ₗ[ZMod 2] (Fin 2 → σ.asModule) :=
    (LinearEquiv.finTwoArrow (ZMod 2) E).symm.trans
      (LinearEquiv.piCongrRight fun _ => σ.asModuleEquiv.symm)
  let τ : Representation (ZMod 2) C (Fin 2 → σ.asModule) :=
    (e.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp ρ
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
  have hh := double_fourth_square σ' hs τ ht a ha
  apply LinearMap.ext
  intro x
  apply e.injective
  have hv := LinearMap.congr_fun hh (e x)
  change e (ρ (a^2) (e.symm (e x))) = e x at hv
  simpa only [e.symm_apply_apply,Module.End.one_apply] using hv

omit [FiniteDimensional (ZMod 2) V] in
private theorem coordinates_fourth_square (σ : Representation (ZMod 2) D E) [IsIrreducible σ]
    (α : Representation (ZMod 2) D V) (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (α d x) = α d (ρ a x))
    (e : α.Equiv (σ.prod σ)) (a : C) (ha : a ^ 4 = 1) : ρ (a^2) = 1 := by
  let τ : Representation (ZMod 2) C (E × E) :=
    (e.toLinearEquiv.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp ρ
  have he (d : D) (x : V) : e (α d x) = (σ d (e x).1, σ d (e x).2) :=
    LinearMap.congr_fun (e.isIntertwining' d) x
  have hh := schur_double_fourth_square σ τ (by
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
  change e (ρ (a^2) x) = e x
  have hv := LinearMap.congr_fun hh (e x)
  change e (ρ (a^2) (e.symm (e x))) = e x at hv
  simpa only [e.symm_apply_apply,Module.End.one_apply] using hv

theorem triple_degree_le_of_commuting_order_four
    (σ : Representation (ZMod 2) D V) (I : Subrepresentation σ)
    (hi : IsIrreducible I.toRepresentation) (hh : homogeneousPart I ⊤ = ⊤)
    (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (σ d x) = σ d (ρ a x))
    (a : C) (ha : a^4=1) (hne : ρ (a^2) ≠ 1) :
    3 * Module.finrank (ZMod 2) I.toSubmodule ≤ Module.finrank (ZMod 2) V := by
  by_contra! hd
  let := hi
  by_cases hp : I.toSubmodule = ⊤
  · have ht : I = ⊤ := Subrepresentation.toSubmodule_injective hp
    let : IsIrreducible σ := isSimpleOrder_iff_isAtom_top.mpr
      (ht ▸ (Subrepresentation.irreducible_iff_isAtom I).mp hi)
    have he := schur_double_fourth_square σ (ρ.prod ρ)
      (by intro a d x; exact Prod.ext (hc a d x.1) (hc a d x.2)) a ha
    apply hne
    ext v
    exact congrArg Prod.fst (LinearMap.congr_fun he (v,0))
  obtain ⟨e⟩ := double_coordinates_of_degree_le I hi hh hp
    (degree_le_double_of_lt_triple I hi hh hp hd)
  exact hne (coordinates_fourth_square I.toRepresentation σ ρ hc e a ha)

omit [FiniteDimensional (ZMod 2) V] in
theorem homogeneous_of_commuting_orbit
    (σ : Representation (ZMod 2) D V) (τ : Representation (ZMod 2) C V)
    (hc : ∀ a d v, τ a (σ d v) = σ d (τ a v))
    (I : Subrepresentation σ) (hg : orbitSpan τ ⊤ I.toSubmodule = ⊤) :
    homogeneousPart I ⊤ = ⊤ := by
  apply top_unique
  conv_lhs => rw [←hg]
  apply iSup_le
  intro a
  let J : Subrepresentation σ := {
    toSubmodule := I.toSubmodule.map (τ a.val)
    apply_mem_toSubmodule := by
      intro d v hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact ⟨σ d w,I.apply_mem_toSubmodule d hw,hc a.val d w⟩ }
  have he : SameModule I J := by
    refine ⟨I.toSubmodule.equivMapOfInjective (τ a.val) (apply_bijective τ a.val).injective,?_⟩
    intro d v
    exact Subtype.ext (hc a.val d v)
  exact le_iSup_of_le J (le_iSup_of_le ⟨le_top,he⟩ le_rfl)

universe w
variable {G : Type*} {W : Type w} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite G] in
/-- A homogeneous module can contain at most two copies of its type when
one copy pays the actor rank and the whole module has budget twice that rank. -/
theorem degree_le_two_of_homogeneous_budget
    (ρ : Representation (ZMod 2) G W)
    (I : Subrepresentation ρ) (hi : I.toRepresentation.IsIrreducible)
    (hh : homogeneousPart I ⊤ = ⊤)
    (A : Subgroup G) (hpos : 0 < fixedCodim I.toRepresentation A)
    (hb : fixedCodim ρ A ≤ 2 * fixedCodim I.toRepresentation A) :
    Module.finrank (ZMod 2) W ≤ 2 * Module.finrank (ZMod 2) I.toSubmodule := by
  let := simple_asSubmodule I hi
  have htop : isotypicComponent (ZMod 2)[G] ρ.asModule I.asSubmodule = ⊤ := by
    have hle : homogeneousPart I ⊤ ≤
        (isotypicComponent (ZMod 2)[G] ρ.asModule I.asSubmodule).restrictScalars (ZMod 2) := by
      apply iSup_le
      intro J
      apply iSup_le
      intro h v hv
      exact (show J.asSubmodule ≤ isotypicComponent (ZMod 2)[G] ρ.asModule I.asSubmodule from
        le_sSup ((sameModule_iff_linearEquiv J I).mp h.2.symm)) hv
    rw [hh] at hle
    exact top_unique hle
  let C := isotypicComponent (ZMod 2)[G] ρ.asModule I.asSubmodule
  let : IsSemisimpleModule (ZMod 2)[G] ρ.asModule :=
    IsSemisimpleModule.congr ((LinearEquiv.ofEq C ⊤ htop).trans (Submodule.topEquiv)).symm
  have ht := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  let N : Subgroup G := ⊤
  let e : N ≃* G := Subgroup.topEquiv
  let I' := I.compActors e.toMonoidHom
  let : IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) :=
    comp_semisimple_of_surjective ρ e.toMonoidHom e.surjective
  have ht' := isotypic_comp_equiv ρ e I ht
  let : Finite W := Module.finite_of_finite (ZMod 2)
  have hIn : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  let : Nontrivial W := I.toSubmodule.subtype_injective.nontrivial
  have heq (V : Type w) [AddCommGroup V] [Module (ZMod 2) V]
      (σ : Representation (ZMod 2) G V) (X : Subrepresentation σ)
      (hX : Nonempty ((X.compActors N.subtype).asSubmodule ≃ₗ[(ZMod 2)[N]] I'.asSubmodule)) :
      fixedCodim X.toRepresentation A = fixedCodim I.toRepresentation A := by
    let er := equiv_of_asSubmodule_equiv (σ.comp N.subtype) (ρ.comp N.subtype)
      (X.compActors N.subtype) I' hX.some
    let er' : X.toRepresentation.Equiv I.toRepresentation := {
      __ := er.toLinearEquiv
      isIntertwining' g := er.isIntertwining' (e.symm g) }
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
      X.toRepresentation I.toRepresentation (MonoidHom.id G) er'.toLinearEquiv
      (fun g v => LinearMap.congr_fun (er'.isIntertwining' g) v) A
  by_contra! hd
  obtain ⟨U,V,X,hU,hV,hX⟩ := exists_three_simple_sections_of_degree_gt
    ρ N ht' ⊥ (IsPGroup.of_subsingleton 2 _) (by simp [N]) hd
  have hu := heq _ ρ U hU
  have hv := heq _ U.quotientRepresentation V hV
  have hx := heq _ V.quotientRepresentation X hX
  have h₁ := fixedCodim_quotient_add_subrepresentation_le ρ U A
  have h₃ := fixedCodim_quotient_add_subrepresentation_le U.quotientRepresentation V A
  have h₄ := fixedCodim_subrepresentation_le V.quotientRepresentation X A
  omega

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
theorem orbit_invariant_of_commuting
    (ρ : Representation (ZMod 2) G W) (X K : Subgroup G)
    (hc : K ≤ centralizer (X : Set G))
    (R : Submodule (ZMod 2) W) (hR : X ≤ subspaceStabilizer ρ R) :
    X ≤ subspaceStabilizer ρ (orbitSpan ρ K R) := by
  apply le_subspaceStabilizer
  intro x hx v hv
  refine Submodule.iSup_induction (fun k : K => R.map (ρ k.val))
    (motive := fun v => ρ x v ∈ orbitSpan ρ K R) hv ?_ ?_ ?_
  · rintro k v ⟨w,hw,rfl⟩
    have hh : ρ x (ρ k w) = ρ k (ρ x w) := by
      rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
      exact LinearMap.congr_fun (congrArg ρ (hc k.property x hx)) w
    rw [hh]
    exact le_iSup (fun k : K => R.map (ρ k.val)) k ⟨ρ x w,(hR hx w).2 hw,rfl⟩
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy
    simpa only [map_add] using (orbitSpan ρ K R).add_mem hx hy

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
/-- Kernel equality holds on the literal orbit of a commuting actor. -/
theorem kernel_commuting_orbit
    (ρ : Representation (ZMod 2) G W) (A K : Subgroup G)
    (hc : K ≤ centralizer (A : Set G)) (R : Submodule (ZMod 2) W) :
    subspaceKernel ρ (orbitSpan ρ K R) A = subspaceKernel ρ R A := by
  apply le_antisymm
  · intro a ha
    exact ⟨ha.1,fun v hv => ha.2 v (le_orbitSpan ρ K R hv)⟩
  · have ho : orbitSpan ρ K R ≤ fixedSpace ρ (subspaceKernel ρ R A) :=
      orbitSpan_le_fixedSpace_of_normalizes ρ
        ((hc.trans (centralizer_le (subspaceKernel_le ρ R A))).trans
          (Subgroup.centralizer_le_normalizer _))
        (le_fixedSpace_subspaceKernel ρ R A)
    intro a ha
    exact ⟨ha.1,fun v hv => ho hv ⟨a,ha⟩⟩

omit [Finite G] in
/-- The two-copy bound applies to the actual commuting orbit and preserves
its pointwise actor kernel. -/
theorem commuting_orbit_degree_le_two
    (ρ : Representation (ZMod 2) G W) (X K A : Subgroup G)
    (hc : K ≤ centralizer (X : Set G)) (hAX : A ≤ X)
    (R : Submodule (ZMod 2) W) (hR : X ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation)
    (hmove : ¬ R ≤ fixedSpace ρ A)
    (hb : fixedCodim (subspaceImageRepresentation ρ (orbitSpan ρ K R))
      (restrictedSubgroup ρ (orbitSpan ρ K R) A) ≤
      2 * fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A)) :
    Module.finrank (ZMod 2) (orbitSpan ρ K R) ≤ 2 * Module.finrank (ZMod 2) R := by
  let O := orbitSpan ρ K R
  have hRO : R ≤ O := le_orbitSpan ρ K R
  have hXO := orbit_invariant_of_commuting ρ X K hc R hR
  let U := invariantSubspace ρ X O hXO
  let I₀ := invariantSubspace ρ X R hR
  let I := sectionLower (ρ.comp X.subtype) I₀ U
  let σ := U.toRepresentation
  let τ := (invariantSubspace ρ K O (orbitSpan_invariant ρ K R)).toRepresentation
  let e : I.toRepresentation.Equiv I₀.toRepresentation :=
    .mk (sectionLowerEquiv (ρ.comp X.subtype) hRO) (by intro x; rfl)
  have hi' : IsIrreducible I.toRepresentation :=
    (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv hi
  have hh : ∀ a x v, τ a (σ x v) = σ x (τ a v) := by
    intro a x v
    apply Subtype.ext
    change ρ a.val (ρ x.val v.val) = ρ x.val (ρ a.val v.val)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun g => ρ g v.val) ((hc a.property x.val x.property).symm)
  have hg : orbitSpan τ ⊤ I.toSubmodule = ⊤ := by
    apply Submodule.map_injective_of_injective (f := O.subtype) Subtype.val_injective
    rw [orbitSpan_map_equivariant τ ρ K.subtype O.subtype (fun _ _ => rfl)]
    have hiO : I.toSubmodule.map O.subtype = R := by
      change (R.comap O.subtype).map O.subtype = R
      rw [Submodule.map_comap_subtype,inf_eq_right.mpr hRO]
    rw [hiO,←MonoidHom.range_eq_map,Subgroup.range_subtype,Submodule.map_top,Submodule.range_subtype]
  let A' := A.subgroupOf X
  have heR : fixedCodim I.toRepresentation A' =
      fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) := by
    have he := fixedCodim_map_equivariant I.toRepresentation I₀.toRepresentation
      (MonoidHom.id X) e.toLinearEquiv
      (fun x v => LinearMap.congr_fun (e.isIntertwining' x) v) A'
    rw [Subgroup.map_id] at he
    rw [he]
    apply congrArg (fun Q : Submodule (ZMod 2) R => Module.finrank (ZMod 2) (R ⧸ Q))
    rw [fixedSpace_restrictedSubgroup ρ R A (hAX.trans hR)]
    ext v
    constructor
    · intro hv a
      exact congrArg Subtype.val (hv ⟨⟨a,hAX a.property⟩,a.property⟩)
    · intro hv a
      exact Subtype.ext (hv ⟨a,a.property⟩)
  have heO : fixedCodim σ A' =
      fixedCodim (subspaceImageRepresentation ρ O) (restrictedSubgroup ρ O A) := by
    apply congrArg (fun Q : Submodule (ZMod 2) O => Module.finrank (ZMod 2) (O ⧸ Q))
    rw [fixedSpace_restrictedSubgroup ρ O A (hAX.trans hXO)]
    ext v
    constructor
    · intro hv a
      exact congrArg Subtype.val (hv ⟨⟨a,hAX a.property⟩,a.property⟩)
    · intro hv a
      exact Subtype.ext (hv ⟨a,a.property⟩)
  have hp : 0 < fixedCodim I.toRepresentation A' := by
    rw [heR]
    apply Nat.pos_of_ne_zero
    intro hz
    have he : fixedSpace (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        have hd := (fixedSpace (subspaceImageRepresentation ρ R)
          (restrictedSubgroup ρ R A)).finrank_quotient_add_finrank
        change fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) + _ = _ at hd
        rw [hz] at hd
        simpa only [zero_add] using hd)
    rw [fixedSpace_restrictedSubgroup ρ R A (hAX.trans hR)] at he
    exact hmove (fun v hv a => (show (⟨v,hv⟩ : R) ∈ (fixedSpace ρ A).comap R.subtype from
      he.symm ▸ Submodule.mem_top) a)
  have hd := degree_le_two_of_homogeneous_budget σ I hi'
    (homogeneous_of_commuting_orbit σ τ hh I hg) A' hp
    (by rw [heO,heR]; exact hb)
  rw [e.toLinearEquiv.finrank_eq] at hd
  exact hd

omit [Finite G] in
/-- An order-four operator commuting with the support forces at least three
copies on its literal orbit, including when properness was not known initially. -/
theorem commuting_orbit_triple_degree
    (ρ : Representation (ZMod 2) G W) (X K : Subgroup G)
    (hc : K ≤ centralizer (X : Set G))
    (R : Submodule (ZMod 2) W) (hR : X ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation)
    (a : K) (ha : a^4=1)
    (hne : ∃ v ∈ orbitSpan ρ K R, ρ (a.val^2) v ≠ v) :
    3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R) := by
  let O := orbitSpan ρ K R
  have hRO : R ≤ O := le_orbitSpan ρ K R
  have hXO := orbit_invariant_of_commuting ρ X K hc R hR
  let U := invariantSubspace ρ X O hXO
  let I₀ := invariantSubspace ρ X R hR
  let I := sectionLower (ρ.comp X.subtype) I₀ U
  let σ := U.toRepresentation
  let τ := (invariantSubspace ρ K O (orbitSpan_invariant ρ K R)).toRepresentation
  let e : I.toRepresentation.Equiv I₀.toRepresentation :=
    .mk (sectionLowerEquiv (ρ.comp X.subtype) hRO) (by intro x; rfl)
  have hi' : IsIrreducible I.toRepresentation :=
    (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv hi
  have hh : ∀ a x v, τ a (σ x v) = σ x (τ a v) := by
    intro a x v
    apply Subtype.ext
    change ρ a.val (ρ x.val v.val) = ρ x.val (ρ a.val v.val)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun g => ρ g v.val) ((hc a.property x.val x.property).symm)
  have hg : orbitSpan τ ⊤ I.toSubmodule = ⊤ := by
    apply Submodule.map_injective_of_injective (f := O.subtype) Subtype.val_injective
    rw [orbitSpan_map_equivariant τ ρ K.subtype O.subtype (fun _ _ => rfl)]
    have hiO : I.toSubmodule.map O.subtype = R := by
      change (R.comap O.subtype).map O.subtype = R
      rw [Submodule.map_comap_subtype,inf_eq_right.mpr hRO]
    rw [hiO,←MonoidHom.range_eq_map,Subgroup.range_subtype,Submodule.map_top,Submodule.range_subtype]
  have hn : τ (a^2) ≠ 1 := by
    intro he
    obtain ⟨v,hv,hn⟩ := hne
    exact hn (congrArg Subtype.val (LinearMap.congr_fun he (⟨v,hv⟩ : O)))
  have hd := triple_degree_le_of_commuting_order_four σ I hi'
    (homogeneous_of_commuting_orbit σ τ hh I hg) τ hh a ha hn
  rw [e.toLinearEquiv.finrank_eq] at hd
  exact hd

end Representation.BinaryOffender.Homogeneous.CommutingMultiplicity
