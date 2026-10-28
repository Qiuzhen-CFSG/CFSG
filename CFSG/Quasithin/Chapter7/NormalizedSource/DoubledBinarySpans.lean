module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFixed
public import Theory.Representation.PSL3Two.LowRankProfiles
public import Theory.Representation.PSL3Two.TransvectionFixed
public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Four-group fixed-space spans on the binary natural–dual pair

Two independent involutions of an inner four-group each fix a four-space;
their common fixed three-space forces their sum to have dimension five.
For an outer four-group, an outer involution fixes a diagonal three-space.
Projection to the natural coordinate embeds the common fixed space into the
fixed plane of its nonidentity inner involution. Thus the common fixed space
has dimension at most two, while the two element fixed spaces span at least
five dimensions. These bounds suffice for the weak-closure application.

The final theorem transports both calculations through the original component
and whole-automizer marking. Its actual orbit application and outer-offender
exclusion are in `NonFFSourceDoubledBinarySpans`.
Source: Aschbacher–Smith H.4.3 and 7.6.1, printed pp.380,702.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open BinaryLinearThree
namespace DoubledBinarySpans
open BinaryLinearThree.NaturalDual

private theorem finrank_of_card {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {n : ℕ} (hc : Nat.card U = 2 ^ n) : Module.finrank (ZMod 2) U = n := by
  let : Finite U := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero n (by decide))
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have hh := congrArg (Nat.log 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hh

private theorem inner_fixed_dimension (g : Group) (hg : g ≠ 1) (hg2 : g ^ 2 = 1) :
    Module.finrank (ZMod 2) (fixedSpace action (zpowers g)) = 4 := by
  apply finrank_of_card
  let e : fixedSpace action (zpowers g) ≃ TransvectionFixed.Fixed g :=
    Equiv.subtypeEquivRight (mem_fixedSpace_zpowers_iff action g)
  exact (Nat.card_congr e).trans (TransvectionFixed.card_fixed g hg (by simpa [pow_two] using hg2))

private theorem natural_fixed_dimension (g : Group) (hg : g ≠ 1) (hg2 : g ^ 2 = 1) :
    Module.finrank (ZMod 2) (fixedSpace W (zpowers g)) = 2 := by
  have hp := inner_fixed_dimension g hg hg2
  have hs := fixedCodim_add_finrank action (zpowers g)
  have hn := fixedCodim_add_finrank W (zpowers g)
  have hd : Module.finrank (ZMod 2) Space = 6 := by
    simp [Space, BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector, Module.finrank_prod]
  have hw : Module.finrank (ZMod 2) Vector = 3 := by
    simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]
  change fixedCodim (W.prod W.dual) (zpowers g) + _ = _ at hs
  rw [fixedCodim_prod, fixedCodim_zpowers_dual, hp, hd] at hs
  rw [hw] at hn
  omega

variable (τ : Representation (ZMod 2) (MulAut Group) Space)
  (hinner : ∀ g : Group, τ (MulAut.conj g) = action g)

private def operator (a : MulAut Group) : Space ≃ₗ[ZMod 2] Space :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom a)

include hinner

private theorem covariance (a : MulAut Group) (g : Group) (v : Space) :
    operator τ a (action g v) = action (a g) (operator τ a v) := by
  change τ a (action g v) = action (a g) (τ a v)
  rw [← hinner g, ← hinner (a g)]
  have he : a * MulAut.conj g = MulAut.conj (a g) * a := by
    ext k
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply]

private theorem swap_fst (a : MulAut Group) (ha : a ∉ MulAut.innerSubgroup Group)
    (v : Vector) : (τ a (v,0)).1 = 0 :=
  (outer_swaps a (operator τ a) (covariance τ hinner a) ha).1 v

private theorem swap_snd (a : MulAut Group) (ha : a ∉ MulAut.innerSubgroup Group)
    (v : Module.Dual (ZMod 2) Vector) : (τ a (0,v)).2 = 0 :=
  (outer_swaps a (operator τ a) (covariance τ hinner a) ha).2 v

private def diagonal (a : MulAut Group) : Vector →ₗ[ZMod 2] Space :=
  LinearMap.inl (ZMod 2) Vector _ + (τ a).comp (LinearMap.inl (ZMod 2) Vector _)

omit hinner in
private theorem diagonal_fixed (a : MulAut Group) (ha2 : a ^ 2 = 1) (v : Vector) :
    diagonal τ a v ∈ fixedSpace τ (zpowers a) := by
  rw [mem_fixedSpace_zpowers_iff]
  change τ a ((v,0) + τ a (v,0)) = (v,0) + τ a (v,0)
  rw [map_add, ← Module.End.mul_apply, ← map_mul, ← pow_two, ha2,
    map_one, Module.End.one_apply, add_comm]

private theorem diagonal_fst (a : MulAut Group) (ha : a ∉ MulAut.innerSubgroup Group)
    (v : Vector) : (diagonal τ a v).1 = v := by
  change v + (τ a (v,0)).1 = v
  rw [swap_fst τ hinner a ha, add_zero]

private theorem diagonal_recover (a : MulAut Group) (ha : a ∉ MulAut.innerSubgroup Group)
    (v : Space) (hv : τ a v = v) : diagonal τ a v.1 = v := by
  have he := congrArg Prod.snd hv
  have hadd : v = (v.1,0) + (0,v.2) := by simp
  rw [hadd, map_add, Prod.snd_add, swap_snd τ hinner a ha, add_zero] at he
  apply Prod.ext
  · exact diagonal_fst τ hinner a ha v.1
  · change 0 + (τ a (v.1,0)).2 = v.2
    simpa using he

private def diagonalEquiv (a : MulAut Group) (ha2 : a ^ 2 = 1)
    (ha : a ∉ MulAut.innerSubgroup Group) :
    Vector ≃ₗ[ZMod 2] fixedSpace τ (zpowers a) :=
  LinearEquiv.ofBijective
    ((diagonal τ a).codRestrict _ (diagonal_fixed τ a ha2)) ⟨by
      intro x y hxy
      have hh := congrArg (fun z : fixedSpace τ (zpowers a) => z.val.1) hxy
      simpa only [LinearMap.codRestrict_apply, diagonal_fst τ hinner a ha] using hh,
    by
      intro v
      exact ⟨v.val.1, Subtype.ext (diagonal_recover τ hinner a ha v.val
        ((mem_fixedSpace_zpowers_iff τ a _).mp v.property))⟩⟩

private theorem outer_fixed_dimension (a : MulAut Group) (ha2 : a ^ 2 = 1)
    (ha : a ∉ MulAut.innerSubgroup Group) :
    Module.finrank (ZMod 2) (fixedSpace τ (zpowers a)) = 3 := by
  rw [← (diagonalEquiv τ hinner a ha2 ha).finrank_eq]
  simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]

private theorem common_fixed_le_two (A : Subgroup (MulAut Group))
    (a : MulAut Group) (haA : a ∈ A) (ha : a ∉ MulAut.innerSubgroup Group)
    (g : Group) (hgA : MulAut.conj g ∈ A) (hg : g ≠ 1) (hg2 : g ^ 2 = 1) :
    Module.finrank (ZMod 2) (fixedSpace τ A) ≤ 2 := by
  let p : fixedSpace τ A →ₗ[ZMod 2] fixedSpace W (zpowers g) := {
    toFun v := ⟨v.val.1, by
      rw [mem_fixedSpace_zpowers_iff]
      have hh := v.property ⟨MulAut.conj g,hgA⟩
      change τ (MulAut.conj g) v.val = v.val at hh
      rw [hinner] at hh
      exact congrArg Prod.fst hh⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hi : Function.Injective p := by
    intro v w hvw
    apply Subtype.ext
    have hv := diagonal_recover τ hinner a ha v.val (v.property ⟨a,haA⟩)
    have hw := diagonal_recover τ hinner a ha w.val (w.property ⟨a,haA⟩)
    rw [← hv, ← hw]
    exact congrArg (diagonal τ a) (congrArg Subtype.val hvw)
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans_eq
    (natural_fixed_dimension g hg hg2)


omit hinner in
private theorem fixed_inf_of_four (A : Subgroup (MulAut Group))
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    fixedSpace τ (zpowers (a : MulAut Group)) ⊓
      fixedSpace τ (zpowers (b : MulAut Group)) = fixedSpace τ A := by
  let := hA
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour A := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  apply le_antisymm
  · intro v hv x
    have hva := (mem_fixedSpace_zpowers_iff τ _ v).mp hv.1
    have hvb := (mem_fixedSpace_zpowers_iff τ _ v).mp hv.2
    by_cases hx : x = 1
    · subst x
      exact (map_one τ ▸ rfl)
    by_cases hxa : x = a
    · subst x; exact hva
    by_cases hxb : x = b
    · subst x; exact hvb
    rw [IsKleinFour.eq_mul_of_ne_all ha hb hab hx hxa hxb]
    change τ ((a : MulAut Group) * b) v = v
    rw [map_mul, Module.End.mul_apply, hvb, hva]
  · exact le_inf (fixedSpace_antitone τ (zpowers_le.mpr a.property))
      (fixedSpace_antitone τ (zpowers_le.mpr b.property))

omit hinner τ in
private theorem exists_second (A : Subgroup (MulAut Group)) (hc : Nat.card A = 4) (a : A) :
    ∃ b : A, b ≠ 1 ∧ b ≠ a := by
  classical
  let := Fintype.ofFinite A
  have hh : ({1,a} : Finset A).card < (Finset.univ : Finset A).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hc]
    exact (Finset.card_insert_le _ _).trans_lt (by simp)
  obtain ⟨b,-,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hh
  exact ⟨b,by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb⟩

private theorem inner_element_dimension (a : MulAut Group)
    (ha : a ≠ 1) (ha2 : a ^ 2 = 1) (hai : a ∈ MulAut.innerSubgroup Group) :
    Module.finrank (ZMod 2) (fixedSpace τ (zpowers a)) = 4 := by
  obtain ⟨g,rfl⟩ := hai
  have hi := MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  have hg : g ≠ 1 := by intro h; exact ha (h ▸ map_one MulAut.conj)
  have hg2 : g ^ 2 = 1 := hi (by rw [map_pow,map_one]; exact ha2)
  have he : fixedSpace τ (zpowers (MulAut.conj g)) = fixedSpace action (zpowers g) := by
    ext v
    simp only [mem_fixedSpace_zpowers_iff, hinner]
  rw [he]
  exact inner_fixed_dimension g hg hg2

/-- H.4.3(2): the common fixed space has dimension three, while the span of
nonidentity element fixed spaces has dimension at least five. -/
theorem inner_four_dimensions (A : Subgroup (MulAut Group))
    (hAI : A ≤ MulAut.innerSubgroup Group)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) :
    Module.finrank (ZMod 2) (fixedSpace τ A) = 3 ∧
      5 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan τ A) := by
  let := hA
  have hfix : Module.finrank (ZMod 2) (fixedSpace τ A) = 3 := by
    apply finrank_of_card
    rw [LowRankProfiles.fixedSpace_eq_naturalDualFixed τ hinner A hAI]
    exact (FourGroupGeometry.FixedSpaces.naturalDualFixed_geometry A hAI hA hc).1
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩ := exists_ne (1 : A)
  obtain ⟨b,hb,hba⟩ := exists_second A hc a
  have ha' : (a : MulAut Group) ≠ 1 := fun h => ha (Subtype.ext h)
  have hb' : (b : MulAut Group) ≠ 1 := fun h => hb (Subtype.ext h)
  have hda := inner_element_dimension τ hinner a ha'
    (elemPow_eq_one_of_isElementaryAbelian _ a.property) (hAI a.property)
  have hdb := inner_element_dimension τ hinner b hb'
    (elemPow_eq_one_of_isElementaryAbelian _ b.property) (hAI b.property)
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace τ (zpowers (a : MulAut Group))) (fixedSpace τ (zpowers (b : MulAut Group)))
  rw [fixed_inf_of_four τ A hA hc a b ha hb hba.symm,hfix,hda,hdb] at hs
  have hle := Submodule.finrank_mono (sup_le
    (fixedSpace_le_fixedSpaceSpan τ a.property ha')
    (fixedSpace_le_fixedSpaceSpan τ b.property hb'))
  exact ⟨hfix,by omega⟩

omit hinner τ in
private theorem exists_inner_nonidentity (A : Subgroup (MulAut Group))
    (hc : Nat.card A = 4) : ∃ g : Group, g ≠ 1 ∧ MulAut.conj g ∈ A := by
  let I := MulAut.innerSubgroup Group
  have hne : A ⊓ I ≠ ⊥ := by
    intro he
    let q : A →* MulAut.Outer Group := (QuotientGroup.mk' I).comp A.subtype
    have hi : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff q).mp
      apply bot_unique
      intro a ha
      have hai : (a : MulAut Group) ∈ I := (QuotientGroup.eq_one_iff _).mp ha
      have ha1 : (a : MulAut Group) = 1 := by
        have hm : (a : MulAut Group) ∈ A ⊓ I := ⟨a.property,hai⟩
        rwa [he,mem_bot] at hm
      exact Subtype.ext ha1
    have hcard := Nat.card_le_card_of_injective q hi
    rw [Matrix.PSL3Two.Automorphisms.card_outer_sl,hc] at hcard
    omega
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨g,hg⟩ := a.property.2
  refine ⟨g,?_,hg.symm ▸ a.property.1⟩
  intro h
  apply ha
  apply Subtype.ext
  simp only [← hg,h,map_one,Subgroup.coe_one]

/-- H.4.3(1), in the form needed for the rank contradiction: an outer
four-group fixes at most a two-space and its element fixed spaces span at least five. -/
theorem outer_four_dimensions (A : Subgroup (MulAut Group))
    (hAI : ¬ A ≤ MulAut.innerSubgroup Group)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) :
    Module.finrank (ZMod 2) (fixedSpace τ A) ≤ 2 ∧
      5 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan τ A) := by
  let := hA
  obtain ⟨a,haA,hai⟩ := SetLike.not_le_iff_exists.mp hAI
  obtain ⟨g,hg,hgA⟩ := exists_inner_nonidentity A hc
  have hi := MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  have hg2 : g ^ 2 = 1 := hi (by
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ hgA)
  have ha : a ≠ 1 := by intro he; exact hai (he ▸ (MulAut.innerSubgroup Group).one_mem)
  have hb : MulAut.conj g ≠ 1 := fun he => hg (hi (he.trans (map_one _).symm))
  have hba : a ≠ MulAut.conj g := by intro he; exact hai (he ▸ ⟨g,rfl⟩)
  have hfix := common_fixed_le_two τ hinner A a haA hai g hgA hg hg2
  have hda := outer_fixed_dimension τ hinner a
    (elemPow_eq_one_of_isElementaryAbelian _ haA) hai
  have hdb := inner_element_dimension τ hinner (MulAut.conj g) hb
    (elemPow_eq_one_of_isElementaryAbelian _ hgA) ⟨g,rfl⟩
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace τ (zpowers a)) (fixedSpace τ (zpowers (MulAut.conj g)))
  rw [fixed_inf_of_four τ A hA hc ⟨a,haA⟩ ⟨MulAut.conj g,hgA⟩
    (fun h => ha (congrArg Subtype.val h)) (fun h => hb (congrArg Subtype.val h))
    (fun h => hba (congrArg Subtype.val h)),hda,hdb] at hs
  have hle := Submodule.finrank_mono (sup_le
    (fixedSpace_le_fixedSpaceSpan τ haA ha) (fixedSpace_le_fixedSpaceSpan τ hgA hb))
  exact ⟨hfix,by omega⟩

end DoubledBinarySpans

/-- Four-group fixed-space and span bounds through the original component and
whole-automizer marking. The map on actors is the same for both calculations. -/
theorem doubledBinary_four_dimensions
    {H J U : Type*} [_root_.Group H] [_root_.Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (i : J →* H)
    (q : J →* Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (hE : ∀ j v, E (ρ (i j) v) = BinaryLinearThree.NaturalDual.action (q j) (E v))
    (f : H ≃* MulAut Group) (hf : ∀ j, f (i j) = MulAut.conj (q j))
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) :
    5 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan ρ A) ∧
      ((∀ a ∈ A, f a ∈ MulAut.innerSubgroup Group) →
        Module.finrank (ZMod 2) (fixedSpace ρ A) = 3) ∧
      ((¬ ∀ a ∈ A, f a ∈ MulAut.innerSubgroup Group) →
        Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 2) := by
  let τ : Representation (ZMod 2) (MulAut Group) BinaryLinearThree.NaturalDual.Space :=
    E.conjRingEquiv.toMonoidHom.comp (ρ.comp f.symm.toMonoidHom)
  have hτ (a : H) (v : U) : E (ρ a v) = τ (f a) (E v) := by
    change E (ρ a v) = E (ρ (f.symm (f a)) (E.symm (E v)))
    rw [f.symm_apply_apply,E.symm_apply_apply]
  have hinner (g : Group) : τ (MulAut.conj g) = BinaryLinearThree.NaturalDual.action g := by
    obtain ⟨j,rfl⟩ := hq g
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    rw [← hf j, ← hτ]
    exact hE j w
  let B := A.map f.toMonoidHom
  let := hA
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBc : Nat.card B = 4 := (card_map_of_injective f.injective).trans hc
  have hBI : B ≤ MulAut.innerSubgroup Group ↔ ∀ a ∈ A, f a ∈ MulAut.innerSubgroup Group := by
    constructor
    · intro h a ha
      exact h (mem_map_of_mem f.toMonoidHom ha)
    · rintro h _ ⟨a,ha,rfl⟩
      exact h a ha
  have hfixed : Module.finrank (ZMod 2) (fixedSpace ρ A) =
      Module.finrank (ZMod 2) (fixedSpace τ B) := by
    have hm := fixedSpace_map_equivariant ρ τ f.toMonoidHom E hτ A
    rw [← hm]
    exact (Submodule.equivMapOfInjective _ E.injective _).finrank_eq
  have hspan : Module.finrank (ZMod 2) (fixedSpaceSpan ρ A) =
      Module.finrank (ZMod 2) (fixedSpaceSpan τ B) := by
    have hm := fixedSpaceSpan_map_equivariant ρ τ f.toMonoidHom f.injective E hτ A
    rw [← hm]
    exact (Submodule.equivMapOfInjective _ E.injective _).finrank_eq
  rw [hfixed,hspan]
  by_cases hi : B ≤ MulAut.innerSubgroup Group
  · obtain ⟨hd,hs⟩ := DoubledBinarySpans.inner_four_dimensions τ hinner B hi hB hBc
    exact ⟨hs,fun _ => hd,fun hn => (hn (hBI.mp hi)).elim⟩
  · obtain ⟨hd,hs⟩ := DoubledBinarySpans.outer_four_dimensions τ hinner B hi hB hBc
    exact ⟨hs,fun hh => (hi (hBI.mpr hh)).elim,fun _ => hd⟩
end CFSG.Quasithin.Chapter7.NormalizedSource
