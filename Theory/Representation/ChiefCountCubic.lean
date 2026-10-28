module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.NaturalQuotient.CubicExactness
public import Theory.Representation.SimpleHeadQuotient
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
/-!
# Binary chief counts and a marked cubic fixed index

Suppose a finite actor maps onto A₄ with two-group kernel. For any actual
subgroup of order three, each noncentral binary chief factor contributes
fixed codimension two, while a central factor contributes zero. Cubic
fixed-space exactness makes these contributions telescope along the supplied
invariant flag. The resulting fixed index is therefore `4^n`, where `n` is
the noncentral chief count.

The proof descends the simple factors through the preimage of the normal
Klein four-group, retaining the original cubic subgroup and representation.
It uses the existing cubic fixed-space exactness theorem; no semisimplicity
of the full actor action or splitting of the chief flag is assumed.

Source application: Aschbacher--Smith 13.7.10(8), printed p.942, comparing
actual cubic fixed indices with the two noncentral factors of the six-letter
binary section.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open Representation.BinaryOffender
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
namespace Representation.ChiefCountCubic
variable {H K V : Type*} [Group H] [Finite H] [Group K] [Finite K]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite H] [Finite V] in
private theorem section_irreducible (ρ : Representation (ZMod 2) H V)
    (U W : Subrepresentation ρ) (h : U ⋖ W) :
    IsIrreducible (sectionRepresentation U W) := by
  apply SimpleHeadQuotient.irreducible_quotient_of_isCoatom
  refine ⟨?_, ?_⟩
  · intro he
    apply h.ne
    apply le_antisymm h.le
    intro v hv
    have hh : (⟨v,hv⟩:W)∈sectionKernel U W := he.symm ▸ (by trivial)
    exact hh
  · intro D hD
    let P : Subrepresentation ρ := {
      toSubmodule := D.toSubmodule.map W.toSubmodule.subtype
      apply_mem_toSubmodule g v hv := by
        obtain ⟨w,hw,rfl⟩ := hv
        exact ⟨W.toRepresentation g w,D.apply_mem_toSubmodule g hw,rfl⟩ }
    have hUP : U≤P := by
      intro u hu
      exact ⟨⟨u,h.le hu⟩,hD.le hu,rfl⟩
    have hPW : P≤W := by rintro _ ⟨w,hw,rfl⟩; exact w.property
    have hne : U≠P := by
      intro he
      apply hD.ne
      apply le_antisymm hD.le
      intro w hw
      have hh : (w:V)∈P := ⟨w,hw,rfl⟩
      rw [←he] at hh
      exact hh
    have he : P=W := (h.eq_or_eq hUP hPW).resolve_left (Ne.symm hne)
    apply top_unique
    intro w _
    have hh : (w:V)∈P := he.symm ▸ w.property
    obtain ⟨z,hz,hzw⟩ := hh
    have : z=w := Subtype.ext hzw
    exact this ▸ hz

omit [Finite H] in
private theorem section_codim_add (ρ : Representation (ZMod 2) H V)
    (U W : Subrepresentation ρ) (h : U≤W) (a : H) (ha : a^3=1) :
    fixedCodim W.toRepresentation (zpowers a) =
      fixedCodim U.toRepresentation (zpowers a) +
      fixedCodim (sectionRepresentation U W) (zpowers a) := by
  let N := sectionKernel U W
  let e : N.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule := {
    toFun := fun v=>⟨v.val.val,v.property⟩
    invFun := fun v=>⟨⟨v.val,h v.property⟩,v.property⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl
    map_add' := fun _ _=>rfl
    map_smul' := fun _ _=>rfl }
  let ef : fixedSpace N.toRepresentation (zpowers a) ≃ₗ[ZMod 2]
      fixedSpace U.toRepresentation (zpowers a) := {
    toFun := fun v=>⟨e v,fun g=>Subtype.ext (congrArg (fun z:N.toSubmodule =>z.val.val) (v.property g))⟩
    invFun := fun v=> by
      refine ⟨e.symm v, ?_⟩
      intro g
      apply Subtype.ext
      apply Subtype.ext
      change ρ g (v.val.val) = v.val.val
      exact congrArg (fun z:U.toSubmodule => (z:V)) (v.property g)
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl
    map_add' := fun _ _=>rfl
    map_smul' := fun _ _=>rfl }
  have hf := BinaryPermutation.PointedSix.cubic_fixed_finrank_add W.toRepresentation N a ha
  have hd := N.toSubmodule.finrank_quotient_add_finrank
  have hW := fixedCodim_add_finrank W.toRepresentation (zpowers a)
  have hU := fixedCodim_add_finrank U.toRepresentation (zpowers a)
  have hQ := fixedCodim_add_finrank N.quotientRepresentation (zpowers a)
  rw [e.finrank_eq] at hd
  rw [ef.finrank_eq] at hf
  change fixedCodim W.toRepresentation (zpowers a) =
    fixedCodim U.toRepresentation (zpowers a) + fixedCodim N.quotientRepresentation (zpowers a)
  omega

private theorem fixed_codim_count
    (f : H →* K) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X=3) (hq : IsPGroup 2 (K⧸X))
    (A : Subgroup H) (hAX : A.map f=X) (a:H) (ha:a^3=1) (hgen:zpowers a=A)
    (ρ : Representation (ZMod 2) H V) {n : ℕ} (hc : HasCount ρ n) :
    fixedCodim ρ A=2*n := by
  classical
  obtain ⟨s,h0,h1,rfl⟩ := hc
  let w (j:Fin (s.length+1)) := fixedCodim (s j).toRepresentation A
  have hi (i:Fin s.length) : w i.succ=w i.castSucc+
      2*(if ¬Central (s i.castSucc) (s i.succ) then 1 else 0) := by
    have hd := section_codim_add ρ (s i.castSucc) (s i.succ) (s.step i).le a ha
    rw [hgen] at hd
    change w i.succ=w i.castSucc+_ at hd
    rw [hd]
    congr 1
    by_cases hz : Central (s i.castSucc) (s i.succ)
    · rw [if_neg (not_not.mpr hz),mul_zero]
      apply (fixedCodim_eq_zero_iff _ _).mpr
      apply top_unique
      intro v _ g
      exact (central_iff_quotient_action _ _).mp hz g v
    · rw [if_pos hz,mul_one]
      let σ := sectionRepresentation (s i.castSucc) (s i.succ)
      let : IsIrreducible σ := section_irreducible ρ _ _ (s.step i)
      have hn : σ≠1 := by
        intro he
        apply hz
        apply (central_iff_quotient_action _ _).mpr
        intro g v
        have hh := congrArg (fun r:Representation (ZMod 2) H _=>r g v) he
        exact hh
      obtain ⟨hD,hF⟩ := NoncentralChiefRefinement.CubicComparison.simple_above_two_kernel
        f hf hp X hX hq A hAX σ hn
      have he := fixedCodim_add_finrank σ A
      change fixedCodim σ A + Module.finrank (ZMod 2) (invariants (σ.comp A.subtype)) = _ at he
      rw [hD,hF,finrank_bot,add_zero] at he
      exact he
  have hz : w 0=0 := by
    change fixedCodim s.head.toRepresentation A=0
    rw [h0]
    have h := fixedCodim_add_finrank (⊥:Subrepresentation ρ).toRepresentation A
    have hz : Module.finrank (ZMod 2) (⊥:Subrepresentation ρ).toSubmodule=0 := finrank_bot (ZMod 2) V
    rw [hz] at h
    omega
  have hl : w (Fin.last s.length)=fixedCodim ρ A := by
    change fixedCodim s.last.toRepresentation A=_
    rw [h1]
    have htop := fixedCodim_add_finrank (⊤:Subrepresentation ρ).toRepresentation A
    have h := fixedCodim_add_finrank ρ A
    rw [(subrepresentationFixedEquiv ρ ⊤ A).finrank_eq] at htop
    change fixedCodim (⊤:Subrepresentation ρ).toRepresentation A +
      Module.finrank (ZMod 2) (⊤ ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) =
      Module.finrank (ZMod 2) (⊤:Submodule (ZMod 2) V) at htop
    rw [top_inf_eq,finrank_top] at htop
    omega
  have hs := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun i _=>hi i)
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have ht : (∑i:Fin s.length,w i.succ)+w 0=
      (∑i:Fin s.length,w i.castSucc)+w (Fin.last s.length) := by
    rw [add_comm _ (w 0),←Fin.sum_univ_succ,←Fin.sum_univ_castSucc]
  have hc : s.count = ∑i:Fin s.length,if ¬Central (s i.castSucc) (s i.succ) then 1 else 0 := by
    rw [Series.count,Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp only [Finset.sum_boole, Nat.cast_id]
  rw [hc]
  omega

omit [Finite H] in
private theorem fixedIndex_eq_pow_codim (ρ : Representation (ZMod 2) H V) (A:Subgroup H) :
    BinaryFixedPoints.fixedIndex (ρ.comp A.subtype)=2^fixedCodim ρ A := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α:=invariants (ρ.comp A.subtype)))
  rw [BinaryFixedPoints.fixedIndex_mul_card]
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=V),
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=invariants (ρ.comp A.subtype)),
    Nat.card_zmod,←pow_add]
  congr 1
  exact (fixedCodim_add_finrank ρ A).symm

/-- Binary noncentral chief factors above a two-kernel and an A₄ quotient each
contribute fixed index four for the actual cubic subgroup. -/
theorem fixedIndex_eq_four_pow_count
    (f : H →* alternatingGroup (Fin 4)) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (A : Subgroup H) (hA : Nat.card A=3)
    (ρ : Representation (ZMod 2) H V) {n : ℕ} (hc : HasCount ρ n) :
    BinaryFixedPoints.fixedIndex (ρ.comp A.subtype)=4^n := by
  let K := alternatingGroup (Fin 4) ⧸ GLS3.Chapter5.alternatingFourKlein
  let q : H →* K := (QuotientGroup.mk' GLS3.Chapter5.alternatingFourKlein).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have hk : q.ker=GLS3.Chapter5.alternatingFourKlein.comap f := by
    ext x
    exact QuotientGroup.eq_one_iff (f x)
  have hpq : IsPGroup 2 q.ker := by
    rw [hk]
    exact (IsPGroup.of_card (p:=2) (n:=2) GLS3.Chapter5.alternatingFourKlein_card).comap_of_ker_isPGroup f hp
  have hK : Nat.card K=3 := by
    have h := GLS3.Chapter5.alternatingFourKlein.card_mul_index
    rw [GLS3.Chapter5.alternatingFourKlein_card,index_eq_card,nat_card_alternatingGroup] at h
    norm_num at h
    change Nat.card (alternatingGroup (Fin 4) ⧸ GLS3.Chapter5.alternatingFourKlein)=3
    omega
  have hX : Nat.card (⊤:Subgroup K)=3 := by rw [card_top,hK]
  have hAX : A.map q=⊤ := eq_of_le_of_card_ge le_top (by
    rw [GLS3.Chapter5.cubic_image_card_of_two_kernel q hpq A hA,hX])
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α:=A)
  have hgen : zpowers (a:H)=A := by
    apply le_antisymm (zpowers_le.mpr a.property)
    intro x hx
    obtain ⟨z,hz⟩ := (mem_zpowers_iff.mp (ha ⟨x,hx⟩))
    exact mem_zpowers_iff.mpr ⟨z,congrArg Subtype.val hz⟩
  have ha3 : (a:H)^3=1 := by
    have h := pow_card_eq_one' (x:=a)
    rw [hA] at h
    exact congrArg Subtype.val h
  rw [fixedIndex_eq_pow_codim,fixed_codim_count q hq hpq ⊤ hX
    (IsPGroup.of_card (n:=0) (by simp)) A hAX a ha3 hgen ρ hc,pow_mul]
  rfl

/-- The logarithm of the literal cubic fixed index equals the supplied chief count. -/
theorem log_fixedIndex_eq_count
    (f : H →* alternatingGroup (Fin 4)) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (A : Subgroup H) (hA : Nat.card A=3)
    (ρ : Representation (ZMod 2) H V) {n : ℕ} (hc : HasCount ρ n) :
    Nat.log 4 (BinaryFixedPoints.fixedIndex (ρ.comp A.subtype))=n := by
  rw [fixedIndex_eq_four_pow_count f hf hp A hA ρ hc,Nat.log_pow (by decide : 1<4)]
end Representation.ChiefCountCubic
