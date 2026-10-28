module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportMultiplicity
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.ThreeCopies

/-!
# Complementary displacement in the two original isotypic halves

A faithful commuting natural SL₃ component forces at least three copies of
the original simple type in its full isotypic component. For an elementary
actor inducing inner automorphisms, invariant simple sections retain exactly
the same inner action: the centralizing difference is a square-zero Schur
endomorphism and vanishes. Three invariant sections therefore contribute
three times the cost of the original type, even when the actor mixes copies.

Adding the estimates on the two complementary halves gives three times the
cost on the original seed pair. The literal Chapter12 application supplies
the support faithfulness, multiplicity and inner lift and obtains 9m, then
excludes the normal natural-support branch. The exchanged Suzuki branch,
other FF exclusions, U = W and Source325 assembly remain with qt-baumann-fsu.

Source: Aschbacher--Smith, D.3.10 final argument, printed p.204;
refs/quasithin.pdf. The inner-section calculation follows the checked
`MovedExhaustionInnerSections` proof, retaining its private boundary.
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MonoidAlgebra IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325.ComplementaryDisplacement
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


private def subrepModuleEquiv (ρ : Representation (ZMod 2) H E)
    (S : Subrepresentation ρ) :
    S.toRepresentation.asModule ≃ₗ[(ZMod 2)[H]] S.asSubmodule := by
  let f : S.toRepresentation.IntertwiningMap ρ :=
    ⟨S.toSubmodule.subtype,fun _ => rfl⟩
  let g := (IntertwiningMap.equivLinearMapAsModule _ _ f).codRestrict
    S.asSubmodule (fun v => v.property)
  exact LinearEquiv.ofBijective g
    ⟨fun _ _ he => Subtype.ext (congrArg Subtype.val he),fun v => ⟨⟨v.val,v.property⟩,rfl⟩⟩

private theorem typePart_semisimple (ρ : Representation (ZMod 2) H E)
    (S : Subrepresentation ρ) (hi : IsIrreducible S.toRepresentation) :
    IsSemisimpleModule (ZMod 2)[H] (typePart S).toRepresentation.asModule := by
  let := simple_asSubmodule S hi
  have hh : IsSemisimpleModule (ZMod 2)[H] (typePart S).asSubmodule := by
    rw [typePart_asSubmodule]
    infer_instance
  let := hh
  exact IsSemisimpleModule.congr (subrepModuleEquiv ρ (typePart S))

private theorem typePart_isotypic (ρ : Representation (ZMod 2) H E)
    (S : Subrepresentation ρ) (hi : IsIrreducible S.toRepresentation) :
    IsIsotypicOfType (ZMod 2)[H] (typePart S).toRepresentation.asModule S.asSubmodule := by
  let := simple_asSubmodule S hi
  have hh : IsIsotypicOfType (ZMod 2)[H] (typePart S).asSubmodule S.asSubmodule := by
    rw [typePart_asSubmodule]
    exact IsIsotypicOfType.isotypicComponent _ _ _
  exact (subrepModuleEquiv ρ (typePart S)).isIsotypicOfType_iff.mpr hh

theorem typePart_comp_surjective {J : Type*} [Group J]
    (ρ : Representation (ZMod 2) H E) (f : J →* H) (hf : Function.Surjective f)
    (S : Subrepresentation ρ) :
    (typePart (S.compActors f)).toSubmodule = (typePart S).toSubmodule := by
  let q := inflationSubrepresentationOrderIso f hf ρ
  have he : q (typePart (S.compActors f)) = typePart S := by
    change q (⨆ B : {B : Subrepresentation (ρ.comp f) // SameModule (S.compActors f) B}, B.val) = _
    rw [q.map_iSup]
    apply le_antisymm
    · refine iSup_le fun B => le_iSup_of_le ⟨q B.val,?_⟩ le_rfl
      obtain ⟨e,he⟩ := B.property
      exact ⟨e,fun h v => by obtain ⟨j,rfl⟩ := hf h; exact he j v⟩
    · refine iSup_le fun B => le_iSup_of_le ⟨B.val.compActors f,?_⟩ le_rfl
      obtain ⟨e,he⟩ := B.property
      exact ⟨e,fun j v => he (f j) v⟩
  exact congrArg Subrepresentation.toSubmodule he

private theorem homogeneous_of_isotypic (ρ : Representation (ZMod 2) H E)
    [IsSemisimpleModule (ZMod 2)[H] ρ.asModule]
    (S : Subrepresentation ρ) (hi : IsIrreducible S.toRepresentation)
    (ht : IsIsotypicOfType (ZMod 2)[H] ρ.asModule S.asSubmodule) :
    homogeneousPart S ⊤ = ⊤ := by
  let := simple_asSubmodule S hi
  have he : typePart S = ⊤ := by
    apply Subrepresentation.subrepresentationSubmoduleOrderIso.injective
    change (typePart S).asSubmodule = ⊤
    rw [typePart_asSubmodule]
    exact isotypicComponent_eq_top_iff.mpr ht
  apply top_unique
  conv_lhs => rw [←show (typePart S).toSubmodule = ⊤ from congrArg Subrepresentation.toSubmodule he]
  change (⨆ B : {B : Subrepresentation ρ // SameModule S B}, B.val).toSubmodule ≤ _
  rw [toSubmodule_iSup]
  exact iSup_le fun B => le_iSup_of_le B.val (le_iSup_of_le ⟨le_top,B.property⟩ le_rfl)

private theorem section_cost
    (ρ : Representation (ZMod 2) H E) (K A : Subgroup H)
    (hA : IsElementaryAbelian 2 A) (f : A →* K)
    (he : ∀ (a : A) (k : K), a.val*k.val*a.val⁻¹ = (f a : H)*k.val*(f a : H)⁻¹)
    (I : Subrepresentation (ρ.comp K.subtype)) (hi : IsIrreducible I.toRepresentation)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) H W) (J : Subrepresentation σ)
    (hJ : Nonempty ((J.compActors K.subtype).asSubmodule ≃ₗ[(ZMod 2)[K]] I.asSubmodule)) :
    fixedCodim J.toRepresentation A = fixedCodim I.toRepresentation f.range := by
  let e := equiv_of_asSubmodule_equiv _ _ (J.compActors K.subtype) I hJ.some
  have hj : IsIrreducible (J.compActors K.subtype).toRepresentation :=
    ChapterB.QuasisimpleSource.ExtensionConsequences.irreducible_of_equiv
      ⟨MulEquiv.refl _,e.toLinearEquiv,fun k v => LinearMap.congr_fun (e.isIntertwining' k) v⟩ hi
  have hs : A ≤ subspaceStabilizer σ (J.compActors K.subtype).toSubmodule := by
    apply le_subspaceStabilizer
    exact fun a _ v hv => J.apply_mem_toSubmodule a hv
  have hagree := inner_lift_agrees_on_irreducible σ K A hA f he (J.compActors K.subtype) hj hs
  have hc := fixedCodim_map_equivariant (J.toRepresentation.comp A.subtype)
    I.toRepresentation f e.toLinearEquiv (by
      intro a v
      have hv : J.toRepresentation a.val v =
          (J.compActors K.subtype).toRepresentation (f a) v := Subtype.ext (hagree a v)
      rw [show (J.toRepresentation.comp A.subtype) a v = J.toRepresentation a.val v from rfl,hv]
      exact LinearMap.congr_fun (e.isIntertwining' (f a)) v) ⊤
  rw [←MonoidHom.range_eq_map] at hc
  have ht := fixedCodim_map_equivariant (J.toRepresentation.comp A.subtype)
    J.toRepresentation A.subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) ⊤
  rw [←MonoidHom.range_eq_map,Subgroup.range_subtype] at ht
  exact ht.symm.trans hc

/-- Three invariant sections retain the original inner actor's cost. -/
private theorem three_sections_inner_cost [Finite E] [Nontrivial E]
    (ρ : Representation (ZMod 2) H E) (K A : Subgroup H) [K.Normal]
    [IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype))]
    (I : Subrepresentation (ρ.comp K.subtype)) (hi : IsIrreducible I.toRepresentation)
    (htype : IsIsotypicOfType (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) I.asSubmodule)
    (hA : IsElementaryAbelian 2 A) (hgen : K ⊔ A = ⊤)
    (f : A →* K)
    (he : ∀ (a : A) (k : K), a.val*k.val*a.val⁻¹ = (f a : H)*k.val*(f a : H)⁻¹)
    (hd : 2 * Module.finrank (ZMod 2) I.toSubmodule < Module.finrank (ZMod 2) E) :
    3 * fixedCodim I.toRepresentation f.range ≤ fixedCodim ρ A := by
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  obtain ⟨U,W,X,hU,hW,hX⟩ := exists_three_simple_sections_of_degree_gt ρ K htype A
    (hA.isPGroup 2 A) hgen hd
  have hu := section_cost ρ K A hA f he I hi ρ U hU
  have hw := section_cost ρ K A hA f he I hi U.quotientRepresentation W hW
  have hx := section_cost ρ K A hA f he I hi W.quotientRepresentation X hX
  have hb := fixedCodim_quotient_add_subrepresentation_le ρ U A
  have hc := fixedCodim_quotient_add_subrepresentation_le U.quotientRepresentation W A
  have he := fixedCodim_subrepresentation_le W.quotientRepresentation X A
  omega


private def lowerTypeModuleEquiv (ρ : Representation (ZMod 2) H E)
    (S : Subrepresentation ρ) :
    (sectionLower ρ S (typePart S)).asSubmodule ≃ₗ[(ZMod 2)[H]] S.asSubmodule := by
  let I := sectionLower ρ S (typePart S)
  let e : I.toRepresentation.Equiv S.toRepresentation :=
    .mk (sectionLowerEquiv ρ (le_typePart S)) (by intro g; rfl)
  let f := IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap
  let q := LinearEquiv.ofBijective f e.toLinearEquiv.bijective
  exact (subrepModuleEquiv (typePart S).toRepresentation I).symm.trans
    (q.trans (subrepModuleEquiv ρ S))

private theorem lowerType_irreducible (ρ : Representation (ZMod 2) H E)
    (S : Subrepresentation ρ) (hi : IsIrreducible S.toRepresentation) :
    IsIrreducible (sectionLower ρ S (typePart S)).toRepresentation := by
  apply ChapterB.QuasisimpleSource.ExtensionConsequences.irreducible_of_equiv
    (show ChapterB.QuasisimpleSource.ActionEquiv
      (sectionLower ρ S (typePart S)).toRepresentation S.toRepresentation from
      ⟨MulEquiv.refl _,sectionLowerEquiv ρ (le_typePart S),fun _ _ => rfl⟩) hi

/-- Faithfulness of a commuting natural SL₃ component forces three copies
of the original type inside its entire isotypic half. -/
theorem typePart_triple_degree_of_commuting_linearThree [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (K C : Subgroup H)
    (S : Subrepresentation (ρ.comp K.subtype)) (hi : IsIrreducible S.toRepresentation)
    (hp : S < typePart S) (hC : C ≤ subspaceStabilizer ρ (typePart S).toSubmodule)
    (hf : Function.Injective
      (invariantSubspace ρ C (typePart S).toSubmodule hC).toRepresentation)
    (hc : C ≤ centralizer (K : Set H))
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : C ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    3 * Module.finrank (ZMod 2) S.toSubmodule ≤ Module.finrank (ZMod 2) (typePart S).toSubmodule := by
  let R := typePart S
  let I := sectionLower (ρ.comp K.subtype) S R
  let σ := R.toRepresentation
  let τ := (invariantSubspace ρ C R.toSubmodule hC).toRepresentation
  let := typePart_semisimple (ρ.comp K.subtype) S hi
  have ht : IsIsotypicOfType (ZMod 2)[K] σ.asModule I.asSubmodule :=
    (typePart_isotypic (ρ.comp K.subtype) S hi).of_linearEquiv_type
    (lowerTypeModuleEquiv (ρ.comp K.subtype) S).symm
  have hh := homogeneous_of_isotypic σ I (lowerType_irreducible _ S hi) ht
  have hip : I.toSubmodule ≠ ⊤ := by
    intro he
    apply hp.ne
    apply Subrepresentation.toSubmodule_injective
    have hh := congrArg (Submodule.map R.toSubmodule.subtype) he
    change (S.toSubmodule.comap R.toSubmodule.subtype).map R.toSubmodule.subtype =
      (⊤ : Submodule (ZMod 2) R.toSubmodule).map R.toSubmodule.subtype at hh
    have hSR : S.toSubmodule ≤ R.toSubmodule := hp.le
    simpa only [Submodule.map_comap_subtype,inf_eq_right.mpr hSR,
      Submodule.map_top,Submodule.range_subtype] using hh
  have hd := homogeneous_triple_degree_of_commuting_linearThree σ I
    (lowerType_irreducible _ S hi) hh hip τ hf (by
      intro a k v
      apply Subtype.ext
      change ρ a.val (ρ k.val v.val) = ρ k.val (ρ a.val v.val)
      rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,hc a.property k.val k.property]) F e
  rwa [(sectionLowerEquiv (ρ.comp K.subtype) (le_typePart S)).finrank_eq] at hd

/-- Three copies in a stable isotypic half contribute three copies of the
same original inner actor cost, even if the actor mixes those copies. -/
private theorem typePart_triple_cost [Finite E]
    (ρ : Representation (ZMod 2) H E) (K A : Subgroup H) [K.Normal]
    (S : Subrepresentation (ρ.comp K.subtype)) (hi : IsIrreducible S.toRepresentation)
    (hAR : A ≤ subspaceStabilizer ρ (typePart S).toSubmodule)
    (hA : IsElementaryAbelian 2 A) (f : A →* K)
    (he : ∀ (a : A) (k : K), a.val*k.val*a.val⁻¹ = (f a : H)*k.val*(f a : H)⁻¹)
    (hd : 2 * Module.finrank (ZMod 2) S.toSubmodule <
      Module.finrank (ZMod 2) (typePart S).toSubmodule) :
    3 * fixedCodim S.toRepresentation f.range ≤
      fixedCodim (invariantSubspace ρ A (typePart S).toSubmodule hAR).toRepresentation ⊤ := by
  let R := typePart S
  let I := sectionLower (ρ.comp K.subtype) S R
  let σ := R.toRepresentation
  let J := K ⊔ A
  have hJR : J ≤ subspaceStabilizer ρ R.toSubmodule :=
    sup_le (le_subspaceStabilizer ρ R.toSubmodule
      (fun k hk v hv => R.apply_mem_toSubmodule ⟨k,hk⟩ hv)) hAR
  let α : Representation (ZMod 2) J R.toSubmodule :=
    (invariantSubspace ρ J R.toSubmodule hJR).toRepresentation
  let N := K.subgroupOf J
  let P := A.subgroupOf J
  let q := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let b := subgroupOfEquivOfLe (show A ≤ J from le_sup_right)
  let I' := I.compActors q.toMonoidHom
  let := typePart_semisimple (ρ.comp K.subtype) S hi
  let : IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (α.comp N.subtype)) :=
    (semisimple_comp_iff_of_surjective σ q.toMonoidHom q.surjective).mpr inferInstance
  have ht : IsIsotypicOfType (ZMod 2)[K] σ.asModule I.asSubmodule :=
    (typePart_isotypic (ρ.comp K.subtype) S hi).of_linearEquiv_type
    (lowerTypeModuleEquiv (ρ.comp K.subtype) S).symm
  have ht' := isotypic_comp_equiv σ q I ht
  have hi' : IsIrreducible I'.toRepresentation :=
    (irreducible_comp_surjective_iff q.toMonoidHom q.surjective I.toRepresentation).mpr
      (lowerType_irreducible _ S hi)
  change 2 * Module.finrank (ZMod 2) S.toSubmodule < Module.finrank (ZMod 2) R.toSubmodule at hd
  let : Nontrivial R.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr (by
    intro hz
    have hdim : Module.finrank (ZMod 2) R.toSubmodule = 0 := by rw [hz,finrank_bot]
    omega)
  have hP : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective b.toMonoidHom b.injective
  let f' : P →* N := q.symm.toMonoidHom.comp (f.comp b.toMonoidHom)
  have he' (a : P) (k : N) : a.val*k.val*a.val⁻¹ =
      (f' a : J)*k.val*(f' a : J)⁻¹ := by
    apply Subtype.ext
    exact he (b a) (q k)
  have hd' : 2 * Module.finrank (ZMod 2) I'.toSubmodule < Module.finrank (ZMod 2) R.toSubmodule := by
    change 2 * Module.finrank (ZMod 2) I.toSubmodule < _
    rwa [(sectionLowerEquiv (ρ.comp K.subtype) (le_typePart S)).finrank_eq]
  have hcost := three_sections_inner_cost α N P I' hi' ht' hP
    (codisjoint_subgroupOf_sup K A).eq_top f' he' hd'
  have hm : f'.range.map q.toMonoidHom = f.range := by
    ext k
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨b a,q.apply_symm_apply _⟩
    · rintro ⟨a,rfl⟩
      refine ⟨f' (b.symm a),⟨b.symm a,rfl⟩,?_⟩
      change q (q.symm (f (b (b.symm a)))) = f a
      rw [q.apply_symm_apply,b.apply_symm_apply]
  have hleft := fixedCodim_map_equivariant I'.toRepresentation S.toRepresentation
    q.toMonoidHom (sectionLowerEquiv (ρ.comp K.subtype) (le_typePart S)) (fun _ _ => rfl) f'.range
  rw [hm] at hleft
  let β := (invariantSubspace ρ A R.toSubmodule hAR).toRepresentation
  have hright := fixedCodim_map_equivariant (α.comp P.subtype) β b.toMonoidHom
    (LinearEquiv.refl _ _) (fun _ _ => rfl) ⊤
  rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr b.surjective] at hright
  have hcomp := fixedCodim_map_equivariant (α.comp P.subtype) α P.subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) ⊤
  rw [←MonoidHom.range_eq_map,Subgroup.range_subtype] at hcomp
  rw [hleft,←hcomp,hright] at hcost
  exact hcost

private theorem invariant_cost_eq (ρ : Representation (ZMod 2) H E)
    (A : Subgroup H) (R : Submodule (ZMod 2) E)
    (hR : A ≤ subspaceStabilizer ρ R) :
    fixedCodim (invariantSubspace ρ A R hR).toRepresentation ⊤ =
      fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) := by
  have hh := fixedCodim_map_equivariant
    (invariantSubspace ρ A R hR).toRepresentation (subspaceImageRepresentation ρ R)
    (subgroupActionHom ρ R A hR) (LinearEquiv.refl _ _) (fun _ _ => rfl) ⊤
  rwa [←MonoidHom.range_eq_map,subgroupActionHom_range] at hh

/-- Add the three-copy costs on the two literal complementary isotypic halves. -/
theorem isotypic_pair_triple_cost [Finite E]
    (ρ : Representation (ZMod 2) H E) (K A : Subgroup H) [K.Normal]
    (S Q : Subrepresentation (ρ.comp K.subtype))
    (hi : IsIrreducible S.toRepresentation) (hj : IsIrreducible Q.toRepresentation)
    (hAR : A ≤ subspaceStabilizer ρ (typePart S).toSubmodule)
    (hAT : A ≤ subspaceStabilizer ρ (typePart Q).toSubmodule)
    (hcompl : IsCompl (typePart S).toSubmodule (typePart Q).toSubmodule)
    (hA : IsElementaryAbelian 2 A) (f : A →* K)
    (he : ∀ (a : A) (k : K), a.val*k.val*a.val⁻¹ = (f a : H)*k.val*(f a : H)⁻¹)
    (hdS : 2 * Module.finrank (ZMod 2) S.toSubmodule <
      Module.finrank (ZMod 2) (typePart S).toSubmodule)
    (hdQ : 2 * Module.finrank (ZMod 2) Q.toSubmodule <
      Module.finrank (ZMod 2) (typePart Q).toSubmodule) :
    3 * (fixedCodim S.toRepresentation f.range + fixedCodim Q.toRepresentation f.range) ≤
      fixedCodim ρ A := by
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  have hs := typePart_triple_cost ρ K A S hi hAR hA f he hdS
  have ht := typePart_triple_cost ρ K A Q hj hAT hA f he hdQ
  rw [invariant_cost_eq] at hs ht
  have hh := common_actor_fixedCodim_sup ρ (typePart S).toSubmodule
    (typePart Q).toSubmodule A hAR hAT hcompl.disjoint
  rw [hcompl.sup_eq_top] at hh
  have hz := fixedCodim_restrictedSubgroup ρ ⊤ A
    (le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => Submodule.mem_top))
  rw [finrank_top,top_inf_eq] at hz
  have ha := fixedCodim_add_finrank ρ A
  omega


/-- The sum of the two original constituent costs is the cost on their
literal span whenever the inner lift agrees there. -/
theorem spanning_inner_pair_cost [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (K A : Subgroup H)
    (S Q : Subrepresentation (ρ.comp K.subtype)) (W : Submodule (ZMod 2) E)
    (hspan : S.toSubmodule ⊔ Q.toSubmodule = W)
    (hd : Disjoint S.toSubmodule Q.toSubmodule)
    (hAW : A ≤ subspaceStabilizer ρ W) (f : A →* K)
    (he : ∀ (a : A) (v : W), ρ (f a : H) v.val = ρ a.val v.val) :
    fixedCodim S.toRepresentation f.range + fixedCodim Q.toRepresentation f.range =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  let α : Representation (ZMod 2) A W := (invariantSubspace ρ A W hAW).toRepresentation
  let β := S.toRepresentation.prod Q.toRepresentation
  let c : (S.toSubmodule × Q.toSubmodule) →ₗ[ZMod 2] W :=
    (S.toSubmodule.subtype.coprod Q.toSubmodule.subtype).codRestrict W (fun v =>
      hspan ▸ Submodule.mem_sup.mpr ⟨v.1,v.1.property,v.2,v.2.property,rfl⟩)
  have hc : Function.Bijective c := by
    constructor
    · apply (injective_iff_map_eq_zero c).mpr
      intro v hv
      have hh : v.1.val + v.2.val = 0 := congrArg Subtype.val hv
      have hx : v.1.val = 0 := Submodule.disjoint_def.mp hd _ v.1.property (by
        rw [eq_neg_of_add_eq_zero_left hh]
        exact Q.toSubmodule.neg_mem v.2.property)
      have hy : v.2.val = 0 := by simpa only [hx,zero_add] using hh
      exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
    · intro v
      have hv : v.val ∈ S.toSubmodule ⊔ Q.toSubmodule := hspan.symm ▸ v.property
      obtain ⟨s,hs,q,hq,heq⟩ := Submodule.mem_sup.mp hv
      exact ⟨(⟨s,hs⟩,⟨q,hq⟩),Subtype.ext heq⟩
  let e := LinearEquiv.ofBijective c hc
  have hi (a : A) (v : S.toSubmodule × Q.toSubmodule) :
      e (β (f a) v) = α a (e v) := by
    apply Subtype.ext
    change ρ (f a : H) v.1.val + ρ (f a : H) v.2.val = ρ a.val (v.1.val+v.2.val)
    rw [←map_add]
    exact he a (e v)
  have hm := fixedCodim_map_equivariant α β f e.symm (by
    intro a v
    apply e.injective
    rw [e.apply_symm_apply,hi,e.apply_symm_apply]) ⊤
  rw [←MonoidHom.range_eq_map,fixedCodim_prod] at hm
  rw [←hm]
  exact invariant_cost_eq ρ A W hAW
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325.ComplementaryDisplacement
