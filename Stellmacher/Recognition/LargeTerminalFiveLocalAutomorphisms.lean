module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.SemidirectProductNormalizerAction

/-!
# The full local automizer of an order-five subgroup

The second local group maps onto the faithful Frobenius group `C5 ⋊ C4`
with a two-group kernel. An order-five subgroup maps isomorphically onto
the normal `C5`; the complement induces all four automorphisms. The coprime
normalizer lifting theorem brings this action back to the second local group.

Source: Stellmacher (10.1), the first Frobenius quotient, and Thompson VI,
pp. 628–630. All normalizer lifting takes place in the second local group.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

universe u

private theorem five_full_action_of_frobenius_quotient
    {H : Type*} [Group H] [Finite H]
    (φ : C4 →* MulAut C5) (hφ : Function.Injective φ)
    (f : H →* SemidirectProduct C5 C4 φ) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (A : Subgroup H) (hA : Nat.card A = 5) :
    Function.Surjective A.normalizerMonoidHom := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  let _ : Fact (IsPGroup 5 A) := ⟨hAp⟩
  have hd : Disjoint A f.ker := hAp.disjoint_of_coprime hker (by decide)
  have hi : Function.Injective (f.subgroupMap A) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro x hx
    have hx' : f.subgroupMap A x = 1 := hx
    have hfx : f (x : H) = 1 := congrArg Subtype.val hx'
    exact Subtype.ext (hd.le_bot ⟨x.property, hfx⟩)
  let B := A.map f
  let e : A ≃* B := MulEquiv.ofBijective (f.subgroupMap A)
    ⟨hi, f.subgroupMap_surjective A⟩
  have hB : Nat.card B = 5 := (Nat.card_congr e.toEquiv).symm.trans hA
  let L := (SemidirectProduct.inl : C5 →* SemidirectProduct C5 C4 φ).range
  have hL : Nat.card L = 5 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    simp [C5]
  have hBL : B ≤ L := by
    let r : B →* C4 := SemidirectProduct.rightHom.comp B.subtype
    have hc : Nat.card r.range = 1 := by
      apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 5 4 by decide)
      · simpa only [hB] using card_range_dvd r
      · simpa [C4] using r.range.card_subgroup_dvd_card
    have hr : r.range = ⊥ := r.range.eq_bot_of_card_eq hc
    intro b hb
    change b ∈ (SemidirectProduct.inl : C5 →* SemidirectProduct C5 C4 φ).range
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    have hm : r ⟨b, hb⟩ ∈ r.range := ⟨⟨b, hb⟩, rfl⟩
    rw [hr] at hm
    exact hm
  have hBeq : B = L := eq_of_le_of_card_ge hBL (by omega)
  have hφs : Function.Surjective φ := by
    apply ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hφ, ?_⟩).2
    rw [IsCyclic.card_mulAut]
    simp [C4, C5]
    decide
  have hfull : Function.Surjective B.normalizerMonoidHom := by
    rw [hBeq]
    exact SemidirectProduct.normalizerMonoidHom_inl_surjective φ hφs
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card f.ker) := by
    rw [hn]
    exact (show Nat.Coprime 5 2 by decide).pow_right n
  exact normalizerMonoidHom_surjective_of_lift A B f e (fun _ => rfl)
    (le_of_eq (normalizer_map_eq_of_coprime_kernel 5 A f hf hcop)) hfull

/-- The second local group realizes every automorphism of each of its
order-five subgroups at the upper Sylow endpoint. -/
public theorem LargeTerminalContext.five_local_automorphisms_surjective
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAsecond : A ≤ ctx.second) :
    Function.Surjective (A.normalizerMonoidHom.comp
      (ctx.second.subgroupOf (normalizer (A : Set G))).subtype) := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  let P := GAt ctx.terminal.Γ cp.firstStep
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  let e : P ≃* ctx.second :=
    (P.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨φ, hφ, projection, hsurj, _⟩ :=
    SectionTen.ten_one_large_first_frobenius tenCtx middle hpath ctx.noTransvections
  let f := projection.comp e.symm.toMonoidHom
  have hf : Function.Surjective f := hsurj.comp e.symm.surjective
  have hmodel : Nat.card (SemidirectProduct C5 C4 φ) = 20 := by
    rw [SemidirectProduct.card]
    simp [C5, C4]
  have hi : f.ker.index = 20 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top, hmodel]
  have hk : Nat.card f.ker = 1024 := by
    have hc := f.ker.card_mul_index
    rw [hi, ctx.second_card_of_large_card hS] at hc
    omega
  have hker : IsPGroup 2 f.ker :=
    IsPGroup.of_card (n := 10) (by simpa using hk)
  apply normalizerMonoidHom_restrict_surjective A ctx.second hAsecond
  apply five_full_action_of_frobenius_quotient φ hφ f hf hker
  exact (Nat.card_congr (subgroupOfEquivOfLe hAsecond).toEquiv).trans hA

/-- The full local automizer supplies an actual squaring element. Its
order and its action on the fixed four-group require further arguments. -/
public theorem LargeTerminalContext.exists_five_squaring_element
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second) :
    ∃ b : G, b ∈ ctx.second ∧ b ∈ normalizer (A : Set G) ∧
      ∀ c ∈ A, b * c * b⁻¹ = c ^ 2 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  let _ : CommGroup A := IsCyclic.commGroup
  have hcop : (Nat.card A).Coprime 2 := by rw [hA]; decide
  let square : MulAut A := { powCoprime hcop with
    map_mul' := fun x y => mul_pow x y 2 }
  obtain ⟨b, hb⟩ := ctx.five_local_automorphisms_surjective hS A hA hAP square
  refine ⟨b, b.property, b.val.property, ?_⟩
  intro c hc
  exact congrArg (fun f : MulAut A => (f ⟨c, hc⟩ : G)) hb

end Stellmacher.Recognition
