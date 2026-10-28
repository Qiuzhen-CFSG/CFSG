module
public import Theory.Representation.RankOne.QuadraticRecognition.SmallCentralizer
public import Mathlib.FieldTheory.Finite.Basic
public import Theory.Representation.RepEquiv

/-!
# Commuting operators on small binary SL₂ modules

In a module without global fixed vectors and dimension below 4n, two
simple submodules would each have dimension at least 2n and could not be
disjoint. There is therefore a unique simple submodule, invariant under
every commuting automorphism. Its actual Schur endomorphism field has
binary degree dividing n, by the proved highest-weight field theorem.
Every nonzero Schur scalar has (2^n−1)-st power one. Hence this power of
a commuting automorphism fixes a nonzero vector in the original module.

The final theorem uses the actual central quotient of a quadratic actor's
fixed-generated local block. Perfectness and actor normal generation prove
that this quotient is nonzero and has no new global fixed vectors.
The fixed vector is lifted only as a representative modulo its exact center.

This supplies an alternative to the Zsigmondy exceptional-case calculation
in DGS85, Groups and Graphs, (5.10)(b), p.112. The highest-weight Schur-field
input is documented in SL2.PrimeFieldParameters.Unsigned. UnitaryElementBounds
uses the result with the actual norm-one torus, including q=8.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups MonoidAlgebra
namespace Representation.RankOne.QuadraticRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem atom_degree_lower
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (hfix : fixedSpace ρ ⊤=⊥) (A : Subrepresentation ρ) (hA : IsAtom A)
    {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n) :
    2*n≤Module.finrank (ZMod 2) A.toSubmodule := by
  let : A.toRepresentation.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom A).mpr hA
  have hnt : ∃ g, A.toRepresentation g≠1 := by
    by_contra! hh
    apply hA.ne_bot
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    apply hfix.le
    intro g
    exact congrArg Subtype.val (LinearMap.congr_fun (hh g) ⟨v,hv⟩)
  exact SL2.Unsigned.irreducible_finrank_bound 2 A.toRepresentation hnt n hn hF

/-- Below twice the minimum nontrivial degree, the simple submodule is unique. -/
theorem sl2_small_atom_unique
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (hfix : fixedSpace ρ ⊤=⊥) {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n)
    (hd : Module.finrank (ZMod 2) V<4*n)
    (A B : Subrepresentation ρ) (hA : IsAtom A) (hB : IsAtom B) : A=B := by
  by_contra hab
  have hi : A ⊓ B=⊥ := by
    rcases hA.le_iff.mp (show A ⊓ B≤A from inf_le_left) with hh|hh
    · exact hh
    · have hAB : A≤B := hh ▸ inf_le_right
      exact (hab ((hB.le_iff_eq hA.ne_bot).mp hAB)).elim
  have hid : A.toSubmodule ⊓ B.toSubmodule=⊥ := congrArg Subrepresentation.toSubmodule hi
  have hAl := atom_degree_lower ρ hfix A hA hn hF
  have hBl := atom_degree_lower ρ hfix B hB hn hF
  have he := A.toSubmodule.finrank_sup_add_finrank_inf_eq B.toSubmodule
  rw [hid,finrank_bot,add_zero] at he
  have hu := (A.toSubmodule ⊔ B.toSubmodule).finrank_le
  omega

/-- Every commuting injective operator preserves that simple submodule. -/
theorem sl2_small_atom_stable
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (hfix : fixedSpace ρ ⊤=⊥) {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n)
    (hd : Module.finrank (ZMod 2) V<4*n)
    (A : Subrepresentation ρ) (hA : IsAtom A)
    (T : Module.End (ZMod 2) V) (hT : Function.Injective T)
    (hc : ∀ g v, T (ρ g v)=ρ g (T v)) : A.toSubmodule.map T≤A.toSubmodule := by
  let B : Subrepresentation ρ := {
    toSubmodule := A.toSubmodule.map T
    apply_mem_toSubmodule g v hv := by
      obtain ⟨w,hw,rfl⟩ := hv
      exact ⟨ρ g w,A.apply_mem_toSubmodule g hw,hc g w⟩ }
  let E := Submodule.equivMapOfInjective T hT A.toSubmodule
  let e : RepEquiv A.toRepresentation B.toRepresentation := {
    toLinearEquiv := E
    isIntertwining' g := by
      ext v
      exact hc g v }
  let : A.toRepresentation.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom A).mpr hA
  have hb : B.toRepresentation.IsIrreducible := by
    exact (RepEquiv.irreducible_euqiv e).mp inferInstance
  have hB : IsAtom B := (Subrepresentation.irreducible_iff_isAtom B).mp hb
  exact (congrArg Subrepresentation.toSubmodule
    (sl2_small_atom_unique ρ hfix hn hF hd B A hB hA)).le

/-- A commuting operator has a nonzero vector fixed by its field-order-minus-one power. -/
theorem sl2_small_commuting_power_has_fixed_vector [Nontrivial V]
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (hfix : fixedSpace ρ ⊤=⊥) {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n)
    (hd : Module.finrank (ZMod 2) V<4*n)
    (T : Module.End (ZMod 2) V) (hT : Function.Injective T)
    (hc : ∀ g v, T (ρ g v)=ρ g (T v)) :
    ∃ v : V, v≠0 ∧ (T^(2^n-1)) v=v := by
  obtain ⟨A,hA,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
  let σ := A.toRepresentation
  let : σ.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom A).mpr hA
  have hnt : ∃ g, σ g≠1 := by
    by_contra! hh
    apply hA.ne_bot
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    apply hfix.le
    intro g
    exact congrArg Subtype.val (LinearMap.congr_fun (hh g) ⟨v,hv⟩)
  have hstable := sl2_small_atom_stable ρ hfix hn hF hd A hA T hT hc
  let U : Module.End (ZMod 2) A.toSubmodule := T.restrict (fun v hv => hstable ⟨v,hv,rfl⟩)
  let f : IntertwiningMap σ σ := {
    toLinearMap := U
    isIntertwining' g := by
      ext v
      exact hc g v }
  let E := Module.End (ZMod 2)[SL(2,F)] σ.asModule
  let : Finite σ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let c : E := IntertwiningMap.equivAlgEnd σ f
  have hc0 : c≠0 := by
    intro hz
    have hf : f=0 := (IntertwiningMap.equivAlgEnd σ).injective (hz.trans (map_zero _).symm)
    let : Nontrivial A.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
      (fun he => hA.ne_bot (Subrepresentation.toSubmodule_injective he))
    obtain ⟨v,hv⟩ := exists_ne (0 : A.toSubmodule)
    have he : T v=0 := congrArg Subtype.val (congrArg (fun f : IntertwiningMap σ σ => f v) hf)
    exact hv (Subtype.ext (hT (he.trans (map_zero T).symm)))
  obtain ⟨_,w,_,hs,_,_⟩ := SL2.Unsigned.exists_primeField_highestWeight_parameters 2 σ hnt n hF
  let : Fintype E := Fintype.ofFinite E
  have hcorder : c^(2^n-1)=1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    apply (orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one c hc0)).trans
    rw [←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_sub_one_dvd_pow_sub_one 2 hs
  have hfpower : f^(2^n-1)=1 := by
    apply (IntertwiningMap.equivAlgEnd σ).injective
    rw [map_pow,map_one]
    exact hcorder
  let : Nontrivial A.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
    (fun he => hA.ne_bot (Subrepresentation.toSubmodule_injective he))
  obtain ⟨v,hv⟩ := exists_ne (0 : A.toSubmodule)
  refine ⟨v,fun he => hv (Subtype.ext he),?_⟩
  have he (i : ℕ) : ((f^i) v : V)=(T^i) v := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ',pow_succ',IntertwiningMap.mul_apply,Module.End.mul_apply]
      change T ((f^i) v : V)=T ((T^i) v)
      exact congrArg T ih
  rw [←he,hfpower]
  rfl
variable {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]

private theorem local_displacements_mem
    (ρ : Representation (ZMod 2) G X) (A : Subgroup G) (hq : IsQuadratic ρ A)
    (hgen : normalClosure (A : Set G)=⊤) (g : G) (v : X) :
    ρ g v-v∈(fixedGeneratedSubrepresentation ρ A).toSubmodule := by
  let W := fixedGeneratedSubrepresentation ρ A
  have hAk : A≤W.quotientRepresentation.ker := by
    intro a ha
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      apply (Submodule.Quotient.eq W.toSubmodule).mpr
      exact fixedSpace_le_fixedGenerated ρ A (fun b => hq b b.property a ha v)
  have htop : (⊤ : Subgroup G)≤W.quotientRepresentation.ker := by
    rw [←hgen]
    exact normalClosure_le_normal hAk
  exact (Submodule.Quotient.eq W.toSubmodule).mp (LinearMap.congr_fun (htop (mem_top g))
    (W.toSubmodule.mkQ v))

/-- The local central quotient of a nontrivial perfect action is nonzero. -/
theorem fixedGenerated_central_quotient_nontrivial [Group.IsPerfect G]
    (ρ : Representation (ZMod 2) G X) (hnt : ∃ g, ρ g≠1)
    (A : Subgroup G) (hq : IsQuadratic ρ A) (hgen : normalClosure (A : Set G)=⊤) :
    let W := fixedGeneratedSubrepresentation ρ A
    Nontrivial (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) := by
  let W := fixedGeneratedSubrepresentation ρ A
  let C := fixedSpace W.toRepresentation ⊤
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  let := hs
  have hWC : W.toSubmodule≤fixedSpace ρ ⊤ := by
    intro v hv
    have hc : (⟨v,hv⟩ : W.toSubmodule)∈C :=
      (Submodule.Quotient.mk_eq_zero C).mp (Subsingleton.elim (C.mkQ ⟨v,hv⟩) 0)
    exact fun g => congrArg Subtype.val (hc g)
  have hmove : subspaceCommutator ρ ⊤ ⊤≤fixedSpace ρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    exact hWC (local_displacements_mem ρ A hq hgen g v)
  have hfix := le_fixedSpace_of_commutator_le_fixedSpace ρ (⊤ : Subgroup G) ⊤
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hmove
  obtain ⟨g,hg⟩ := hnt
  apply hg
  ext v
  exact hfix Submodule.mem_top ⟨g,mem_top g⟩

/-- The Schur-field power calculation on the literal local central quotient,
written with unchanged ambient representatives and denominator. -/
theorem sl2_fixedGenerated_power_has_fixed_vector [Group.IsPerfect SL(2,F)]
    (ρ : Representation (ZMod 2) SL(2,F) V) (hnt : ∃ g, ρ g≠1)
    (A : Subgroup SL(2,F)) (hq : IsQuadratic ρ A)
    (hgen : normalClosure (A : Set SL(2,F))=⊤)
    {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n)
    (hd : let W := fixedGeneratedSubrepresentation ρ A
      Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤)<4*n)
    (T : Module.End (ZMod 2) V) (hc : ∀ g v, T (ρ g v)=ρ g (T v))
    {m : ℕ} (hm : 0<m) (hT : T^m=1) :
    ∃ v∈(fixedGeneratedSubrepresentation ρ A).toSubmodule,
      v∉fixedSpace ρ ⊤ ∧ (T^(2^n-1)) v-v∈fixedSpace ρ ⊤ := by
  let W := fixedGeneratedSubrepresentation ρ A
  let C := fixedSpace W.toRepresentation ⊤
  let U : Module.End (ZMod 2) W.toSubmodule := T.restrict
    (fun v hv => fixedGenerated_map_le_of_commutes ρ A T hc ⟨v,hv,rfl⟩)
  have hUc (g : SL(2,F)) (v : W.toSubmodule) :
      U (W.toRepresentation g v)=W.toRepresentation g (U v) := Subtype.ext (hc g v)
  have hUp (i : ℕ) (v : W.toSubmodule) : ((U^i) v : V)=(T^i) v := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [pow_succ',Module.End.mul_apply]
      change T ((U^i) v : V)=T ((T^i) v)
      exact congrArg T ih
  have hUC : C≤C.comap U := by
    intro v hv g
    change W.toRepresentation g (U v)=U v
    rw [←hUc,show W.toRepresentation g v=v from hv g]
  let D := C.mapQ C U hUC
  have hD (v : W.toSubmodule) : D (C.mkQ v)=C.mkQ (U v) := rfl
  have hDc (g : SL(2,F)) (v : W.toSubmodule ⧸ C) :
      D (globalFixedQuotient W.toRepresentation g v)=globalFixedQuotient W.toRepresentation g (D v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact congrArg C.mkQ (hUc g v)
  have hDp (i : ℕ) (v : W.toSubmodule) : (D^i) (C.mkQ v)=C.mkQ ((U^i) v) := by
    induction i with
    | zero => rfl
    | succ i ih => simp only [pow_succ',Module.End.mul_apply,ih,hD]
  have hDm : D^m=1 := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change (D^m) (C.mkQ v)=C.mkQ v
      rw [hDp]
      apply congrArg C.mkQ
      apply Subtype.ext
      rw [hUp,hT]
      rfl
  have hDi : Function.Injective D := by
    have hleft : D^(m-1)*D=1 := by rw [←pow_succ,Nat.sub_add_cancel hm,hDm]
    intro v w hvw
    have hh := congrArg (D^(m-1)) hvw
    simpa only [←Module.End.mul_apply,hleft,Module.End.one_apply] using hh
  let : Nontrivial (W.toSubmodule ⧸ (globalFixedSubrepresentation W.toRepresentation).toSubmodule) :=
    fixedGenerated_central_quotient_nontrivial ρ hnt A hq hgen
  obtain ⟨v,hv,he⟩ := sl2_small_commuting_power_has_fixed_vector (globalFixedQuotient W.toRepresentation)
    (globalFixedQuotient_fixed_eq_bot W.toRepresentation) hn hF hd D hDi hDc
  obtain ⟨w,rfl⟩ := C.mkQ_surjective v
  refine ⟨w,w.property,?_,?_⟩
  · intro hw
    exact hv ((Submodule.Quotient.mk_eq_zero C).mpr (fun g => Subtype.ext (hw g)))
  · have he' : C.mkQ ((U^(2^n-1)) w)=C.mkQ w := (hDp (2^n-1) w).symm.trans he
    have hh := (Submodule.Quotient.eq C).mp he'
    have hval : ((U^(2^n-1)) w-w : W.toSubmodule).val=(T^(2^n-1)) w-w := by
      change ((U^(2^n-1)) w : V)-w=(T^(2^n-1)) w-w
      rw [hUp]
    intro g
    have hg := congrArg Subtype.val (hh g)
    change ρ g (((U^(2^n-1)) w-w : W.toSubmodule).val)=
      ((U^(2^n-1)) w-w : W.toSubmodule).val at hg
    change ρ g ((T^(2^n-1)) w-w)=(T^(2^n-1)) w-w
    simpa only [hval] using hg

end Representation.RankOne.QuadraticRecognition
