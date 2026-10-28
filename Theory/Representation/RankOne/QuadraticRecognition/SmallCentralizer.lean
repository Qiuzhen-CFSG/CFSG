module
public import Theory.Representation.RankOne.QuadraticRecognition.QuadraticPairs
public import Theory.Representation.RankOne.QuadraticRecognition.FixedGeneratedReduction
public import Theory.Representation.SL2.MinimalBinaryDegree
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Odd centralizers of small local SL₂ central quotients

An odd commuting operator splits a binary module into its fixed space and
its cyclic-norm kernel. If the global fixed space is zero, each nonzero
summand has dimension at least twice the defining-field degree. Below
four times that degree, the operator is therefore trivial or fixed-free.
The quotient version uses the literal quotient by the local fixed space;
perfectness excludes new fixed vectors there.

For a quadratic actor whose normal closure is a perfect local group,
trivial operator action on the central quotient of its fixed-generated
block forces trivial action on every ambient local displacement. This
connects the quotient dichotomy to the original displacement branch,
without assuming that movement of the whole block survives its center.

Source: DGS85, Groups and Graphs, proof of (5.10)(b), pp.111–112.
UnitaryMovingTorus applies these facts to the actual Hermitian block.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]

/-- If the fixed-generated block has trivial central-quotient action under
an operator commuting with the perfect local group, that operator fixes
every ambient local displacement. -/
theorem fixes_displacements_of_trivial_on_fixedGenerated_central_quotient
    [Group.IsPerfect G]
    (ρ : Representation (ZMod 2) G X) (A : Subgroup G) (hq : IsQuadratic ρ A)
    (hgen : normalClosure (A : Set G)=⊤)
    (T : Module.End (ZMod 2) X) (hc : ∀ g v, T (ρ g v)=ρ g (T v))
    (ht : ∀ v∈(fixedGeneratedSubrepresentation ρ A).toSubmodule,
      T v-v∈fixedSpace ρ ⊤) : ∀ a v, T (ρ a v-v)=ρ a v-v := by
  let W := fixedGeneratedSubrepresentation ρ A
  let σ := W.quotientRepresentation
  have hAk : A≤σ.ker := by
    intro a ha
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      apply (Submodule.Quotient.eq W.toSubmodule).mpr
      exact fixedSpace_le_fixedGenerated ρ A (fun b => hq b b.property a ha v)
  have htop : (⊤ : Subgroup G)≤σ.ker := by
    rw [←hgen]
    exact normalClosure_le_normal hAk
  have hd (a : G) (v : X) : ρ a v-v∈W.toSubmodule :=
    (Submodule.Quotient.eq W.toSubmodule).mp (LinearMap.congr_fun (htop (mem_top a))
      (W.toSubmodule.mkQ v))
  let f := T-1
  have hfc (a : G) (v : X) : f (ρ a v)=ρ a (f v) := by
    change T (ρ a v)-ρ a v=ρ a (T v-v)
    rw [map_sub,hc]
  have hs : (⊤ : Subgroup G)≤subspaceStabilizer ρ f.range := by
    apply le_subspaceStabilizer
    rintro a _ _ ⟨v,rfl⟩
    exact ⟨ρ a v,hfc a v⟩
  have hfC : subspaceCommutator ρ f.range ⊤≤fixedSpace ρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,_,_,⟨v,rfl⟩,rfl⟩
    rw [←hfc,←map_sub]
    exact ht _ (hd a v)
  have hfF := le_fixedSpace_of_commutator_le_fixedSpace ρ (⊤ : Subgroup G) f.range hs hfC
  intro a v
  have he : f (ρ a v-v)=0 := by
    rw [map_sub,hfc,show ρ a (f v)=f v from hfF ⟨v,rfl⟩ ⟨a,mem_top a⟩,sub_self]
  exact sub_eq_zero.mp he

/-- A central odd-order element cannot fix all displacements of a normally
generating actor in a faithful binary action. The conclusion is proved
before using faithfulness, as equality of the original operator to one. -/
theorem odd_central_trivial_of_fixes_displacements
    (ρ : Representation (ZMod 2) G X) (A : Subgroup G)
    (hgen : normalClosure (A : Set G)=⊤) (k : G) (hk : k∈center G)
    {m : ℕ} (hm : Odd m) (hkp : k^m=1)
    (hfix : ∀ a∈A, ∀ v, ρ k (ρ a v-v)=ρ a v-v) : ρ k=1 := by
  let T := ρ k
  let f : Module.End (ZMod 2) X := T-1
  have hc (a : G) (v : X) : f (ρ a v)=ρ a (f v) := by
    change ρ k (ρ a v)-ρ a v=ρ a (ρ k v-v)
    rw [map_sub,←Module.End.mul_apply,←map_mul,
      ←Module.End.mul_apply,←map_mul,(mem_center_iff.mp hk a).symm]
  let U : Subrepresentation ρ := {
    toSubmodule := f.range
    apply_mem_toSubmodule a v hv := by
      obtain ⟨w,rfl⟩ := hv
      exact ⟨ρ a w,hc a w⟩ }
  have hAk : A≤U.toRepresentation.ker := by
    intro a ha
    apply LinearMap.ext
    rintro ⟨_,v,rfl⟩
    apply Subtype.ext
    change ρ a (f v)=f v
    apply sub_eq_zero.mp
    rw [←hc,←map_sub]
    exact sub_eq_zero.mpr (hfix a ha v)
  have htop : (⊤ : Subgroup G)≤U.toRepresentation.ker := by
    rw [←hgen]
    exact normalClosure_le_normal hAk
  have hsq : T^2=1 := by
    apply LinearMap.ext
    intro v
    have he := congrArg Subtype.val
      (LinearMap.congr_fun (htop (mem_top k)) (⟨f v,v,rfl⟩ : U.toSubmodule))
    change T (T v-v)=T v-v at he
    rw [map_sub] at he
    have htwo (w : X) : w+w=0 := by
      calc
        w+w=((1:ZMod 2)+1) • w := by rw [add_smul,one_smul]
        _=0 := by rw [show (1:ZMod 2)+1=0 by decide,zero_smul]
    have hh := sub_eq_sub_iff_add_eq_add.mp he
    rw [htwo] at hh
    have hv := (add_right_cancel_iff (a := v)).mp (hh.trans (htwo v).symm)
    simpa only [pow_two,Module.End.mul_apply,Module.End.one_apply] using hv
  have hp : T^m=1 := by change (ρ k)^m=1; rw [←map_pow,hkp,map_one]
  obtain ⟨r,hr⟩ := hm
  rw [hr,pow_add,pow_mul,hsq,one_pow,pow_one,one_mul] at hp
  exact hp

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem fixed_free_degree_lower
    (ρ : Representation (ZMod 2) SL(2,F) V) [Nontrivial V]
    (hfix : fixedSpace ρ ⊤=⊥) {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n) :
    2*n≤Module.finrank (ZMod 2) V := by
  obtain ⟨A,hA,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
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
  exact (SL2.Unsigned.irreducible_finrank_bound 2 A.toRepresentation hnt n hn hF).trans
    A.toSubmodule.finrank_le

/-- Below twice the minimum nontrivial degree, an odd commuting operator
on a module without global fixed vectors is either trivial or fixed-free. -/
theorem sl2_small_odd_centralizer_dichotomy
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (hfix : fixedSpace ρ ⊤=⊥) {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n)
    (hd : Module.finrank (ZMod 2) V<4*n)
    (T : Module.End (ZMod 2) V) (hc : ∀ g v, T (ρ g v)=ρ g (T v))
    {m : ℕ} (hm : Odd m) (hT : T^m=1) :
    T=1 ∨ ∀ v, T v=v → v=0 := by
  let N : Module.End (ZMod 2) V := ∑ i ∈ Finset.range m, T^i
  have hNc : ∀ g v, N (ρ g v)=ρ g (N v) := by
    intro g v
    have hi (i : ℕ) (v : V) : (T^i) (ρ g v)=ρ g ((T^i) v) := by
      induction i with
      | zero => rfl
      | succ i ih => simp only [pow_succ',Module.End.mul_apply,hc,ih]
    simp only [N,LinearMap.sum_apply,map_sum,hi]
  have hNfix (v : V) : T (N v)=N v := by
    have he : (T-1)*N=0 := by
      dsimp only [N]
      rw [mul_geom_sum,hT,sub_self]
    exact sub_eq_zero.mp (LinearMap.congr_fun he v)
  have hNid (v : V) (hv : T v=v) : N v=v := by
    have hi (i : ℕ) : (T^i) v=v := by
      induction i with
      | zero => rfl
      | succ i ih => simp only [pow_succ',Module.End.mul_apply,ih,hv]
    simp only [N,LinearMap.sum_apply,hi,Finset.sum_const,Finset.card_range]
    rw [←Nat.cast_smul_eq_nsmul (ZMod 2)]
    have hm' : (m : ZMod 2)=1 := by
      obtain ⟨r,rfl⟩ := hm
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,ZMod.natCast_self,zero_mul,zero_add]
    rw [hm',one_smul]
  let C : Subrepresentation ρ := {
    toSubmodule := (T-1).ker
    apply_mem_toSubmodule g v hv := by
      change T (ρ g v)-ρ g v=0
      rw [hc,show T v=v from sub_eq_zero.mp hv,sub_self] }
  let D : Subrepresentation ρ := {
    toSubmodule := N.ker
    apply_mem_toSubmodule g v hv := by
      change N (ρ g v)=0
      rw [hNc,show N v=0 from hv,map_zero] }
  have hCf : fixedSpace C.toRepresentation ⊤=⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfix.le (fun g => congrArg Subtype.val (hv g))
  have hDf : fixedSpace D.toRepresentation ⊤=⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfix.le (fun g => congrArg Subtype.val (hv g))
  have hdis : Disjoint C.toSubmodule D.toSubmodule := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro v hv
    have hcv : T v=v := sub_eq_zero.mp hv.1
    exact (hNid v hcv).symm.trans hv.2
  by_cases hC : C.toSubmodule=⊥
  · right
    intro v hv
    exact hC.le (show v∈C.toSubmodule from sub_eq_zero.mpr hv)
  · let : Nontrivial C.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hC
    have hCl := fixed_free_degree_lower C.toRepresentation hCf hn hF
    have hD : D.toSubmodule=⊥ := by
      by_contra hD
      let : Nontrivial D.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hD
      have hDl := fixed_free_degree_lower D.toRepresentation hDf hn hF
      have he := Submodule.finrank_sup_add_finrank_inf_eq C.toSubmodule D.toSubmodule
      rw [hdis.eq_bot,finrank_bot,add_zero] at he
      have hu := (C.toSubmodule ⊔ D.toSubmodule).finrank_le
      omega
    left
    ext v
    have hNv : N (T v-v)=0 := by
      have he : N*(T-1)=0 := by
        dsimp only [N]
        rw [geom_sum_mul,hT,sub_self]
      exact LinearMap.congr_fun he v
    exact sub_eq_zero.mp (hD.le hNv)

/-- The dichotomy is on the literal quotient by all local fixed vectors.
It is expressed using the original representatives and their denominator. -/
theorem sl2_small_central_quotient_dichotomy [Group.IsPerfect SL(2,F)]
    (ρ : Representation (ZMod 2) SL(2,F) V)
    {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n)
    (hd : Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ ⊤)<4*n)
    (T : Module.End (ZMod 2) V) (hc : ∀ g v, T (ρ g v)=ρ g (T v))
    {m : ℕ} (hm : Odd m) (hT : T^m=1) :
    (∀ v, T v-v∈fixedSpace ρ ⊤) ∨
    (∀ v, T v-v∈fixedSpace ρ ⊤ → v∈fixedSpace ρ ⊤) := by
  let C := fixedSpace ρ ⊤
  have hTC : C≤C.comap T := by
    intro v hv g
    change ρ g (T v)=T v
    rw [←hc,show ρ g v=v from hv g]
  let U := C.mapQ C T hTC
  have hU (v : V) : U (C.mkQ v)=C.mkQ (T v) := rfl
  have hUc (g : SL(2,F)) (v : V ⧸ C) :
      U (globalFixedQuotient ρ g v)=globalFixedQuotient ρ g (U v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact congrArg C.mkQ (hc g v)
  have hUp : U^m=1 := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      have he (i : ℕ) (v : V) : (U^i) (C.mkQ v)=C.mkQ ((T^i) v) := by
        induction i with
        | zero => rfl
        | succ i ih => simp only [pow_succ',Module.End.mul_apply,ih,hU]
      change (U^m) (C.mkQ v)=C.mkQ v
      rw [he,hT]
      rfl
  rcases sl2_small_odd_centralizer_dichotomy (globalFixedQuotient ρ)
      (globalFixedQuotient_fixed_eq_bot ρ) hn hF hd U hUc hm hUp with ht|hf
  · left
    intro v
    exact (Submodule.Quotient.eq C).mp (LinearMap.congr_fun ht (C.mkQ v))
  · right
    intro v hv
    exact (Submodule.Quotient.mk_eq_zero C).mp
      (hf (C.mkQ v) ((Submodule.Quotient.eq C).mpr hv))
/-- On the fixed-generated local block, the trivial branch fixes all
original displacements; the other branch is fixed-free modulo its center. -/
theorem sl2_fixedGenerated_odd_centralizer_dichotomy [Group.IsPerfect SL(2,F)]
    (ρ : Representation (ZMod 2) SL(2,F) V) (A : Subgroup SL(2,F))
    (hq : IsQuadratic ρ A) (hgen : normalClosure (A : Set SL(2,F))=⊤)
    {n : ℕ} (hn : n≠0) (hF : Nat.card F=2^n)
    (hd : let W := fixedGeneratedSubrepresentation ρ A
      Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤)<4*n)
    (T : Module.End (ZMod 2) V) (hc : ∀ g v, T (ρ g v)=ρ g (T v))
    {m : ℕ} (hm : Odd m) (hT : T^m=1) :
    (∀ a v, T (ρ a v-v)=ρ a v-v) ∨
    (∀ v∈(fixedGeneratedSubrepresentation ρ A).toSubmodule,
      T v-v∈fixedSpace ρ ⊤ → v∈fixedSpace ρ ⊤) := by
  let W := fixedGeneratedSubrepresentation ρ A
  let U : Module.End (ZMod 2) W.toSubmodule := T.restrict
    (fun v hv => fixedGenerated_map_le_of_commutes ρ A T hc ⟨v,hv,rfl⟩)
  have hUc (g : SL(2,F)) (v : W.toSubmodule) :
      U (W.toRepresentation g v)=W.toRepresentation g (U v) :=
    Subtype.ext (hc g v)
  have hUp : U^m=1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have he (i : ℕ) (v : W.toSubmodule) : ((U^i) v : V)=(T^i) v := by
      induction i with
      | zero => rfl
      | succ i ih =>
        simp only [pow_succ',Module.End.mul_apply]
        change T ((U^i) v : V)=T ((T^i) v)
        exact congrArg T ih
    rw [he,hT]
    rfl
  rcases sl2_small_central_quotient_dichotomy W.toRepresentation hn hF hd U hUc hm hUp with ht|hf
  · left
    apply fixes_displacements_of_trivial_on_fixedGenerated_central_quotient ρ A hq hgen T hc
    intro v hv g
    exact congrArg Subtype.val (ht ⟨v,hv⟩ g)
  · right
    intro v hv hh g
    exact congrArg Subtype.val (hf ⟨v,hv⟩ (fun g => Subtype.ext (hh g)) g)

end Representation.RankOne.QuadraticRecognition

