module
public import Theory.SpecificGroups.SymmetricFive.WreathElementaryRank
public import Theory.Alternating.Aut
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.ElementaryAbelian.Quotient

/-!
# Marked automorphisms and elementary actors of the A₅ square

The actual conjugation isomorphism S₅ → Aut(A₅) identifies the regular
symmetric-five wreath product with Aut(A₅ × A₅). The formula on inner
conjugations preserves the two specified factors. Transferring the elementary
wreath estimates then bounds the two-rank by four, supplies a nontrivial inner
involution in rank three, and supplies independently supported inner
involutions in rank four.

The final faithful-actor versions return witnesses in the original actor
and the literal conjugation identities. They are the group-theoretic inputs
for the moved A₅-pair module estimates in Aschbacher–Smith D.3.5, pp.195–196.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
open WreathTwoElementaryRank
abbrev Alt := alternatingGroup (Fin 5)
abbrev Sym := Equiv.Perm (Fin 5)
abbrev Pair := Alt × Alt
abbrev Wreath := W Sym
@[expose] def factorEquiv : Sym ≃* MulAut Alt :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
local notation "α" => factorEquiv

@[expose] def wreathMap (w : Wreath) : MulAut Pair :=
  if w.right = 1 then (α (w.left 1)).prodCongr (α (w.left turn))
  else (α (w.left 1)).prodCongr (α (w.left turn)) * MulEquiv.prodComm

theorem wreathMap_apply (w : Wreath) (x : Pair) :
    wreathMap w x = if w.right=1 then (α (w.left 1) x.1, α (w.left turn) x.2)
      else (α (w.left 1) x.2, α (w.left turn) x.1) := by
  by_cases h : w.right=1 <;> simp only [wreathMap,h,ite_true,ite_false] <;> rfl

@[expose] def wreathHom : Wreath →* MulAut Pair where
  toFun := wreathMap
  map_one' := by ext x <;> simp [wreathMap_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    change wreathMap (a*b) x = wreathMap a (wreathMap b x)
    rcases index_cases a.right with ha | ha <;>
      rcases index_cases b.right with hb | hb <;>
      simp [wreathMap_apply,ha,hb,turn_ne_one]

theorem wreathHom_injective : Function.Injective wreathHom := by
  apply (injective_iff_map_eq_one wreathHom).mpr
  intro w hw
  have hh (x : Pair) : wreathMap w x = x := MulEquiv.congr_fun hw x
  rcases index_cases w.right with hr | hr
  · have ha : α (w.left 1) = 1 := by
      apply MulEquiv.ext
      intro x
      simpa [wreathMap_apply,hr] using congrArg Prod.fst (hh (x,1))
    have hb : α (w.left turn) = 1 := by
      apply MulEquiv.ext
      intro x
      simpa [wreathMap_apply,hr] using congrArg Prod.snd (hh (1,x))
    have h1 : w.left 1 = 1 := (α).injective (ha.trans (α).map_one.symm)
    have h2 : w.left turn = 1 := (α).injective (hb.trans (α).map_one.symm)
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · exact h1
      · exact h2
    · exact hr
  · obtain ⟨x,hx⟩ := exists_ne (1 : Alt)
    have hf := congrArg Prod.fst (hh (x,1))
    have he : x = 1 := by simpa [wreathMap_apply,hr,turn_ne_one] using hf.symm
    exact (hx he).elim

private instance : IsQuasisimple Alt where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup Alt := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

theorem wreathHom_surjective : Function.Surjective wreathHom := by
  intro f
  rcases AutomorphismSquare.normal_form (alternatingGroup.center_eq_bot (by simp)) f with
    ⟨a,b,h⟩ | ⟨a,b,h⟩
  · refine ⟨baseHom ((α).symm a,(α).symm b),?_⟩
    apply MulEquiv.ext
    intro x
    simp [wreathHom,wreathMap,baseHom,h,turn_ne_one]
  · let w : Wreath := ⟨fun i => if i=1 then (α).symm a else (α).symm b,turn⟩
    refine ⟨w,?_⟩
    apply MulEquiv.ext
    intro x
    simp [wreathHom,wreathMap,w,h,turn_ne_one]

def wreathEquiv : Wreath ≃* MulAut Pair :=
  MulEquiv.ofBijective wreathHom ⟨wreathHom_injective,wreathHom_surjective⟩

theorem wreathHom_inner (a b : Alt) : wreathHom (baseHom (a.val,b.val)) = MulAut.conj (a,b) := by
  apply MulEquiv.ext
  intro x
  change (wreathMap (baseHom (a.val,b.val))) x = _
  rw [wreathMap_apply]
  simp [baseHom,turn_ne_one,factorEquiv]
  rfl

theorem wreathEquiv_apply (w : Wreath) : wreathEquiv w = wreathHom w := by rfl

theorem rank_le_four : primeRank 2 (MulAut Pair) ≤ 4 := by
  rw [← primeRank_equiv 2 wreathEquiv]
  exact SymmetricFive.WreathElementaryRank.rank_le_four

private theorem inner_injective : Function.Injective (MulAut.conj : Pair →* MulAut Pair) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have h (a : Alt) : a ∈ center Alt → a=1 := by
    intro ha
    exact (alternatingGroup.center_eq_bot (by simp) : center Alt=⊥).le ha
  apply Prod.ext
  · apply h
    apply mem_center_iff.mpr
    intro y
    have he := congrArg Prod.fst (MulEquiv.congr_fun hx (y,1))
    change x.1*y*x.1⁻¹=y at he
    have hh := congrArg (fun z => z*x.1) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm
  · apply h
    apply mem_center_iff.mpr
    intro y
    have he := congrArg Prod.snd (MulEquiv.congr_fun hx (1,y))
    change x.2*y*x.2⁻¹=y at he
    have hh := congrArg (fun z => z*x.2) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm

/-- A rank-three elementary subgroup contains an actual nonidentity inner
involution of the marked A₅ product. -/
theorem exists_nontrivial_inner (E : Subgroup (MulAut Pair))
    (hE : IsElementaryAbelian 2 E) (hc : 4 < Nat.card E) :
    ∃ r : Pair, r≠1 ∧ r^2=1 ∧ MulAut.conj r ∈ E := by
  let F := E.map wreathEquiv.symm.toMonoidHom
  have hF : IsElementaryAbelian 2 F := hE.map _
  have hFc : Nat.card F=Nat.card E := card_map_of_injective wreathEquiv.symm.injective
  obtain ⟨x,hx,hne,hr,ha,hb⟩ := SymmetricFive.WreathElementaryRank.exists_nontrivial_inner
    F hF (hFc ▸ hc)
  let a : Alt := ⟨x.left 1,ha⟩
  let b : Alt := ⟨x.left turn,hb⟩
  have hxbase : baseHom (a.val,b.val)=x := by
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · simp [baseHom,a]
      · simp [baseHom,b,turn_ne_one]
    · exact hr.symm
  have hxE : wreathHom x ∈ E := by
    rw [←wreathEquiv_apply]
    exact mem_map_equiv.mp hx
  have he : wreathHom x = MulAut.conj (a,b) := hxbase ▸ wreathHom_inner a b
  have hn : (a,b)≠(1 : Pair) := by
    intro hab
    apply hne
    rw [←hxbase]
    have heq := congrArg (fun p : Pair => (p.1.val,p.2.val)) hab
    rw [heq]
    exact map_one baseHom
  refine ⟨(a,b),hn,?_,he ▸ hxE⟩
  apply inner_injective
  rw [map_pow,←he,map_one]
  let := hE
  exact elemPow_eq_one_of_isElementaryAbelian _ hxE

/-- Maximum-rank elementary subgroups contain inner involutions in each
literal factor, independently. -/
theorem exists_independent_inner (E : Subgroup (MulAut Pair))
    (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E) :
    ∃ a b : Alt, a≠1 ∧ b≠1 ∧ a^2=1 ∧ b^2=1 ∧
      MulAut.conj (a,1) ∈ E ∧ MulAut.conj (1,b) ∈ E := by
  let F := E.map wreathEquiv.symm.toMonoidHom
  have hF : IsElementaryAbelian 2 F := hE.map _
  have hFc : Nat.card F=Nat.card E := card_map_of_injective wreathEquiv.symm.injective
  obtain ⟨a,b,ha,hb,ha2,hb2,haF,hbF⟩ :=
    SymmetricFive.WreathElementaryRank.exists_independent_inner F hF (hFc ▸ hc)
  refine ⟨a,b,ha,hb,ha2,hb2,?_,?_⟩
  · rw [←wreathHom_inner,←wreathEquiv_apply]
    exact mem_map_equiv.mp haF
  · rw [←wreathHom_inner,←wreathEquiv_apply]
    exact mem_map_equiv.mp hbF

theorem exists_nontrivial_inner_of_rank_ge_three (E : Subgroup (MulAut Pair))
    (hE : IsElementaryAbelian 2 E) (hr : 3 ≤ primeRank 2 E) :
    ∃ r : Pair, r≠1 ∧ r^2=1 ∧ MulAut.conj r ∈ E := by
  apply exists_nontrivial_inner E hE
  by_contra hn
  let := hE
  have hb := IsElementaryAbelian.primeRank_le_of_card_le (p:=2) (n:=2) E
    (Nat.le_of_not_gt hn)
  omega

theorem exists_independent_inner_of_rank_ge_four (E : Subgroup (MulAut Pair))
    (hE : IsElementaryAbelian 2 E) (hr : 4 ≤ primeRank 2 E) :
    ∃ a b : Alt, a≠1 ∧ b≠1 ∧ a^2=1 ∧ b^2=1 ∧
      MulAut.conj (a,1) ∈ E ∧ MulAut.conj (1,b) ∈ E := by
  apply exists_independent_inner E hE
  obtain ⟨A,_,hA⟩ := exists_elementaryAbelian_card_primeRank (G:=E) (p:=2)
  have hc := card_le_card_group A
  rw [hA] at hc
  exact (Nat.pow_le_pow_right (by decide : 0<2) hr).trans hc

section FaithfulActor
variable {A : Type*} [Group A] [Finite A]

theorem faithful_actor_rank_le_four (ρ : A →* MulAut Pair) (hρ : Function.Injective ρ) :
    primeRank 2 A ≤ 4 := (primeRank_le_of_injective 2 ρ hρ).trans rank_le_four

variable [IsElementaryAbelian 2 A]

/-- The rank-three inner element is supplied in the original faithful actor,
with its actual action identified as conjugation by an involution. -/
theorem faithful_actor_inner (ρ : A →* MulAut Pair) (hρ : Function.Injective ρ)
    (hr : 3 ≤ primeRank 2 A) :
    ∃ a : A, a≠1 ∧ ∃ r : Pair, r≠1 ∧ r^2=1 ∧ ρ a=MulAut.conj r := by
  have he : IsElementaryAbelian 2 ρ.range :=
    IsElementaryAbelian.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hh : 3 ≤ primeRank 2 ρ.range := hr.trans_eq
    (primeRank_equiv 2 (MonoidHom.ofInjective hρ))
  obtain ⟨r,hr1,hr2,a,ha⟩ := exists_nontrivial_inner_of_rank_ge_three ρ.range he hh
  refine ⟨a,?_,r,hr1,hr2,ha⟩
  intro ha1
  have hi : MulAut.conj r = MulAut.conj (1 : Pair) := by rw [←ha,ha1,map_one,map_one]
  exact hr1 (inner_injective hi)

/-- The maximum-rank witnesses are two actual elements of the original
faithful actor with independently supported inner actions. -/
theorem faithful_actor_independent_inner (ρ : A →* MulAut Pair) (hρ : Function.Injective ρ)
    (hr : 4 ≤ primeRank 2 A) :
    ∃ a b : A, ∃ r s : Alt, r≠1 ∧ s≠1 ∧ r^2=1 ∧ s^2=1 ∧
      ρ a=MulAut.conj (r,1) ∧ ρ b=MulAut.conj (1,s) := by
  have he : IsElementaryAbelian 2 ρ.range :=
    IsElementaryAbelian.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hh : 4 ≤ primeRank 2 ρ.range := hr.trans_eq
    (primeRank_equiv 2 (MonoidHom.ofInjective hρ))
  obtain ⟨r,s,hr1,hs1,hr2,hs2,⟨a,ha⟩,⟨b,hb⟩⟩ :=
    exists_independent_inner_of_rank_ge_four ρ.range he hh
  exact ⟨a,b,r,s,hr1,hs1,hr2,hs2,ha,hb⟩
end FaithfulActor

end Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
