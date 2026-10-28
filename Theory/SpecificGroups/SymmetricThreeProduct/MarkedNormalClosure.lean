module
public import Theory.SpecificGroups.SymmetricThreeProduct.NormalThreeSubgroups
public import Theory.GroupTheory.PlaneCoreNormalClosure
public import Theory.GroupTheory.PResidual.AbelianQuotient
public import Theory.ElementaryAbelian.Basic

/-!
# Marked normal closures in S₃ × S₃

Let N be a normal two-perfect subgroup of order three. A nontrivial
elementary two-subgroup A centralizing N lies in the complementary S₃
factor. Its order is two and its normal closure is that entire factor.
The normal closure, N and any Sylow two-subgroup generate the whole group.

Normal order-three subgroups are the two coordinate axes. Orient the
coordinates so N is the first axis; a cubic centralizer calculation puts
A in the second factor. Transport the resulting group equivalence and
Sylow supplement through the original model isomorphism.

Source application: Aschbacher--Smith, 14.3.23(2)(i), printed p.1000,
used by the original HS seed exclusion in Centerless.SolvableRow.
-/

public noncomputable section
open Subgroup
namespace SymmetricThreeProduct

private theorem two_subgroup_order (A : Subgroup S3) (hA : IsPGroup 2 A)
    (hne : A ≠ ⊥) : Nat.card A = 2 := by
  have hd : Nat.card A ∣ 6 := by
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using A.card_subgroup_dvd_card
  obtain ⟨n,hn⟩ := hA.exists_card_eq
  have hc : Nat.Coprime (Nat.card A) 3 := hn ▸ (by decide : Nat.Coprime 2 3).pow_left n
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ (hc.dvd_mul_right.mp hd) with h | h
  · exact (hne (Subgroup.card_eq_one.mp h)).elim
  · exact h

private def c : S3 := Equiv.swap 0 1 * Equiv.swap 1 2

private theorem cubic_centralizing_involution : ∀ x : S3, x^2=1 → c*x=x*c → x=1 := by
  decide +kernel

private theorem left_centralizing_involution (x : G) (hx : x ^ 2 = 1)
    (hc : ∀ y ∈ leftThree, y * x = x * y) : x.1 = 1 := by
  exact cubic_centralizing_involution x.1 (congrArg Prod.fst hx)
    (congrArg Prod.fst (hc (c,1) (by decide +kernel)))

private theorem left_marked_normalClosure (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hne : A ≠ ⊥) (hC : A ≤ centralizer (leftThree : Set G)) (S : Sylow 2 G) :
    Nat.card A = 2 ∧
    Nonempty ((conjugateSpanBy A ⊤) ≃* S3) ∧
    conjugateSpanBy A ⊤ ⊔ leftThree ⊔ (S : Subgroup G) = ⊤ := by
  let R : Subgroup G := (⊥ : Subgroup S3).prod ⊤
  have hAR : A ≤ R := by
    intro a ha
    exact ⟨left_centralizing_involution a
      (elemPow_eq_one_of_isElementaryAbelian a ha) (hC ha),mem_top _⟩
  let f : G →* S3 := MonoidHom.snd _ _
  have hfi : Function.Injective (f.comp A.subtype) := by
    intro a b he
    apply Subtype.ext
    exact Prod.ext ((hAR a.property).1.trans (hAR b.property).1.symm) he
  have hne' : A.map f ≠ ⊥ := by
    intro he
    apply hne
    apply le_bot_iff.mp
    intro a ha
    exact Prod.ext (hAR ha).1 (show a.2 = 1 from (Subgroup.map_eq_bot_iff A).mp he ha)
  have hc := two_subgroup_order (A.map f) ((IsElementaryAbelian.isPGroup 2 A).map f) hne'
  have hcard : Nat.card A = 2 := by
    have hh := card_map_of_injective (K := (⊤ : Subgroup A)) hfi
    have hh' : Nat.card (A.map f) = Nat.card A := by
      simpa only [←map_map,←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype,card_top] using hh
    exact hh'.symm.trans hc
  let K := conjugateSpanBy A ⊤
  have hKR : K ≤ R := conjugateSpanBy_le hAR (by rw [normalizer_eq_top])
  have hKm : K.map f = ⊤ := by
    rw [map_conjugateSpanBy,map_top_of_surjective f (fun a => ⟨(1,a),rfl⟩)]
    exact permThree_conjugateSpan_eq_top _ hc
  have hKe : K = R := by
    apply le_antisymm hKR
    intro x hx
    obtain ⟨k,hk,he⟩ := (show x.2 ∈ K.map f from hKm ▸ mem_top _)
    have hkx : k = x := Prod.ext ((hKR hk).1.trans hx.1.symm) he
    exact hkx ▸ hk
  let kf := f.comp K.subtype
  have hki : Function.Injective kf := by
    intro a b he
    exact Subtype.ext (Prod.ext ((hKR a.property).1.trans (hKR b.property).1.symm) he)
  have hks : Function.Surjective kf := by
    intro a
    obtain ⟨k,hk,he⟩ := (show a ∈ K.map f from hKm ▸ mem_top _)
    exact ⟨⟨k,hk⟩,he⟩
  refine ⟨hcard,⟨MulEquiv.ofBijective kf ⟨hki,hks⟩⟩,?_⟩
  apply top_unique
  conv_lhs => rw [←pResidual_sup_sylow_eq_top S]
  apply sup_le _ le_sup_right
  apply le_trans _ le_sup_left
  change pResidual 2 G ≤ K ⊔ leftThree
  rw [hKe,SymmetricThreeProductResidual.residual_eq]
  intro x hx
  have hcube : x.1 ^ 3 = 1 := by
    have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]; rfl
    exact congrArg Subtype.val (h3 ▸ pow_card_eq_one' (x := (⟨x.1,hx.1⟩ : alternatingGroup (Fin 3))))
  have hleft : (x.1,1) ∈ leftThree := ⟨hcube,rfl⟩
  have hright : (1,x.2) ∈ R := ⟨rfl,mem_top _⟩
  simpa only [Prod.mk_mul_mk,one_mul,mul_one] using
    (R ⊔ leftThree).mul_mem (mem_sup_right hleft) (mem_sup_left hright)

end SymmetricThreeProduct

namespace SymmetricThreeProduct
variable {D : Type*} [Group D] [Finite D]

/-- The literal marked actor normally generates the complementary symmetric-three factor. -/
theorem marked_normalClosure
    (model : Nonempty (D ≃* G)) (N A : Subgroup D) [N.Normal]
    (hp : IsPPerfect 2 N) (hN : Nat.card N = 3)
    [IsElementaryAbelian 2 A] (hne : A ≠ ⊥)
    (hC : A ≤ centralizer (N : Set D)) (S : Sylow 2 D) :
    Nat.card A = 2 ∧ Nonempty ((conjugateSpanBy A ⊤) ≃* S3) ∧
      conjugateSpanBy A ⊤ ⊔ N ⊔ (S : Subgroup D) = ⊤ := by
  obtain ⟨e₀⟩ := model
  have horient : ∃ e : D ≃* G, N.map e.toMonoidHom = leftThree := by
    let N₀ := N.map e₀.toMonoidHom
    let : N₀.Normal := (inferInstance : N.Normal).map e₀.toMonoidHom e₀.surjective
    have hp₀ := hp.of_surjective (e₀.toMonoidHom.subgroupMap N)
      (e₀.toMonoidHom.subgroupMap_surjective N)
    have hc₀ : Nat.card N₀ = 3 := (card_map_of_injective e₀.injective).trans hN
    rcases normal_twoPerfect_threePart N₀ hp₀ (by rw [hc₀,Nat.Prime.factorization_self Nat.prime_three,pow_one]) with hl | hr
    · exact ⟨e₀,hl⟩
    · refine ⟨e₀.trans (MulEquiv.prodComm : G ≃* G),?_⟩
      change N.map ((MulEquiv.prodComm : G ≃* G).toMonoidHom.comp e₀.toMonoidHom) = _
      rw [←map_map,show N.map e₀.toMonoidHom = rightThree from hr]
      ext x
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact ⟨ha.2,ha.1⟩
      · intro hx
        exact ⟨(x.2,x.1),⟨hx.2,hx.1⟩,rfl⟩
  obtain ⟨e,he⟩ := horient
  let A₀ := A.map e.toMonoidHom
  let := IsElementaryAbelian.map (p := 2) (A := A) e.toMonoidHom
  have hn₀ : A₀ ≠ ⊥ := by
    intro hh
    apply hne
    exact (map_injective e.injective) (hh.trans (map_bot e.toMonoidHom).symm)
  have hC₀ : A₀ ≤ centralizer (leftThree : Set G) := by
    rw [←he]
    rintro x ⟨a,ha,rfl⟩ y ⟨n,hn,rfl⟩
    exact (map_mul e.toMonoidHom n a).symm.trans
      ((congrArg e (hC ha n hn)).trans (map_mul e.toMonoidHom a n))
  let S₀ := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hc,hm,hgen⟩ := left_marked_normalClosure A₀ hn₀ hC₀ S₀
  have hK : (conjugateSpanBy A ⊤).map e.toMonoidHom = conjugateSpanBy A₀ ⊤ := by
    rw [map_conjugateSpanBy,map_top_of_surjective _ e.surjective]
  refine ⟨(card_map_of_injective e.injective).symm.trans hc,?_,?_⟩
  · obtain ⟨em⟩ := hm
    exact ⟨((conjugateSpanBy A ⊤).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hK).trans em)⟩
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup,Subgroup.map_sup,hK,he,map_top_of_surjective _ e.surjective]
    exact hgen

end SymmetricThreeProduct
