module
public import Theory.SpecificGroups.ReeF4.PrimeFieldRepresentative
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Torus
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Split-prime field actors in the actual Ree group

A prime of an odd-degree binary split torus can divide the Ree order only
through its split factor. The two literal root characters give an elementary
subgroup of order p² in the actual diagonal torus. A prime-order field actor
acts on that torus by a common power; Fermat's congruence makes this action
trivial on its p-elements. Its faithful inner image together with the outer
field representative therefore forces rank three in the same automorphism
image. The inner-field decomposition retains that image throughout.

This includes the full binary Ree fixed group in the arithmetic and torus
calculations. Automorphism coverage is used only for m ≥ 1, with simplicity
and perfectness inherited from the source component. No order or simplicity
certification is assumed for a replacement carrier.

Source: Aschbacher--Smith, A.3.18, printed pp.51--53, and the odd-degree
Ree branch of 4.3.12(2), printed p.617. The actual torus and order imports
record the underlying GLS3 root constructions.
-/

public section
open Subgroup Theory.GroupTheory
noncomputable section

private theorem prime_power_actor_fixes {B : Type*} [Group B] {p k : ℕ} [Fact p.Prime]
    (a : MulAut B) (ha : a^p=1) (x : B) (hx : x^p=1) (he : a x=x^k) : a x=x := by
  have hi (j : ℕ) : (a^j) x=x^(k^j) := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', MulAut.mul_apply, ih, map_pow, he, ←pow_mul, pow_succ']
  have hc : k^p ≡ k [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow] using ZMod.pow_card (k : ZMod p)
  have hh := hi p
  rw [ha, MulAut.one_apply, pow_eq_pow_of_modEq hc hx] at hh
  exact he.trans hh.symm

namespace ReeF4.OddDegreeFieldActors

/-- A prime of an odd-degree binary split torus divides the actual Ree order
only through the split factor of its field size. -/
theorem split_of_odd_binary_prime {p n m : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (hn : Odd n) (hd : p ∣ 2^n-1)
    (hcard : p ∣ Nat.card (ReeF4.Model m)) : p ∣ 2^(2*m+1)-1 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hh : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hh)
  have hn1 : (2 : ZMod p)^n=1 := by
    have hz := (ZMod.natCast_eq_zero_iff (2^n-1) p).mpr hd
    rw [Nat.cast_sub (one_le_pow₀ (by decide : 1 ≤ (2:ℕ))), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  let q : ZMod p := 2^(2*m+1)
  have hneg (j : ℕ) : q^j ≠ -1 := by
    intro hh
    have hpow : (q^j)^n=1 := by
      rw [pow_right_comm, show q^n=1 by dsimp [q]; rw [pow_right_comm, hn1, one_pow], one_pow]
    rw [hh,hn.neg_one_pow] at hpow
    have h : (2 : ZMod p)=0 := by linear_combination -hpow
    exact htwo h
  have hq : q≠0 := pow_ne_zero _ htwo
  have h6 : q^6+1≠0 := by simpa only [ne_eq, add_eq_zero_iff_eq_neg] using hneg 6
  have h3 : q^3+1≠0 := by simpa only [ne_eq, add_eq_zero_iff_eq_neg] using hneg 3
  have hz := (ZMod.natCast_eq_zero_iff (Nat.card (ReeF4.Model m)) p).mpr hcard
  rw [ReeF4.CentralCovers.OddPrimary.Order.card_model] at hz
  have hqnat : 1 ≤ 2^(2*m+1) := one_le_pow₀ (by decide)
  push_cast [Nat.cast_sub hqnat, Nat.cast_sub (one_le_pow₀ hqnat)] at hz
  change q^12*(q^6+1)*(q^4-1)*(q^3+1)*(q-1)=0 at hz
  have hlast : (q^4-1)*(q-1)=0 := by
    have hf : q^12*(q^6+1)*(q^4-1)*(q^3+1)*(q-1) =
        (q^12*(q^6+1)*(q^3+1))*((q^4-1)*(q-1)) := by ring
    rw [hf] at hz
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) h6) h3)
  have hq1 : q=1 := by
    rcases mul_eq_zero.mp hlast with hh | hh
    · have hfac : (q^2+1)*(q+1)*(q-1)=q^4-1 := by ring
      rw [←hfac] at hh
      have h21 : q^2+1≠0 := by simpa only [ne_eq, add_eq_zero_iff_eq_neg] using hneg 2
      have h11 : q+1≠0 := by simpa only [pow_one, ne_eq, add_eq_zero_iff_eq_neg] using hneg 1
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero h21 h11))
    · exact sub_eq_zero.mp hh
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  rw [Nat.cast_sub hqnat, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  exact sub_eq_zero.mpr hq1

open ConverseParabolics.FullLeviRepresentation
variable {m p : ℕ} [Fact p.Prime]

/-- The two actual root characters supply a fixed elementary p-square. -/
theorem exists_fixed_elementary (d : LocalBlockInput m)
    (hd : p ∣ 2^(2*m+1)-1) (a : MulAut d.fixedGroup)
    (ha : orderOf a=p) (hfield : a ∈ zpowers d.fieldAutomorphism) :
    ∃ E : Subgroup d.fixedGroup, IsElementaryAbelian p E ∧ Nat.card E=p^2 ∧
      E ≤ a.fixedSubgroup := by
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := (CoefficientField m)ˣ) p (by
    rwa [Nat.card_units,field_card])
  let P := zpowers u
  let : IsElementaryAbelian p P := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hu ▸ pow_orderOf_eq_one u)
  let : IsElementaryAbelian p (P × P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.2) }
  let f : P × P →* d.fixedGroup := d.modelEquiv.symm.toMonoidHom.comp
    ((torusHom m).comp (P.subtype.prodMap P.subtype))
  have hf : Function.Injective f := by
    intro x y he
    have hh := torusHom_injective m (d.modelEquiv.symm.injective he)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range,inferInstance,?_,?_⟩
  · rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,Nat.card_prod,Nat.card_zpowers,hu,pow_two]
  · rintro _ ⟨bc,rfl⟩
    have ht : f bc ∈ Cartan.torus d := by
      change (f bc : SplitGroup m) ∈ Parabolics.diagonalTorus m
      have hh : (f bc : SplitGroup m) = toSplitGroup m (torusHom m (bc.1.val,bc.2.val)) := by
        have he := (d.modelEquiv_coe (f bc)).symm
        simpa [f, toSplitGroup_apply, MonoidHom.coe_prodMap, Prod.map_apply'] using he
      rw [hh]
      have he := torusElement_mem bc.1.val bc.2.val
      change toSplitGroup m (torusHom m (bc.1.val,bc.2.val)) ∈ Parabolics.splitTorus m at he
      rwa [Parabolics.splitTorus_eq_diagonalTorus] at he
    obtain ⟨k,hk⟩ := Cartan.field_subgroup_torus_power d a hfield
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    exact prime_power_actor_fixes a (ha ▸ pow_orderOf_eq_one a) (f bc)
      (elemPow_eq_one_of_isElementaryAbelian (p := p) (f bc) (show f bc ∈ f.range from ⟨bc,rfl⟩)) (hk _ ht)

/-- The actual field representative and its fixed torus square force rank three. -/
theorem field_actor_rank_three (d : LocalBlockInput m) (hz : center d.fixedGroup=⊥)
    (hd : p ∣ 2^(2*m+1)-1) (A : Subgroup (MulAut d.fixedGroup))
    (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A)
    (a : MulAut d.fixedGroup) (ha : orderOf a=p)
    (hfield : a ∈ zpowers d.fieldAutomorphism) (haA : a∈A)
    (hout : a ∉ MulAut.innerSubgroup d.fixedGroup) : 3 ≤ primeRank p A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary d hd a ha hfield
  let := hE
  let f : d.fixedGroup →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := fun _ _ hh =>
    MulAut.conj_injective_of_center_eq_bot hz (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨a,haA⟩
  have hx : orderOf x=p := (orderOf_injective A.subtype A.subtype_injective x).symm.trans ha
  have hxB : x∉B := by
    rintro ⟨g,_,hg⟩
    exact hout ⟨g,congrArg Subtype.val hg⟩
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * a y * g⁻¹ = a (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B=p^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- A prime actor in the original full-inner overgroup cannot be outer at a split prime. -/
theorem prime_actor_inner_of_split (hm : 1≤m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hd : p ∣ 2^(2*m+1)-1) (A : Subgroup (MulAut d.fixedGroup))
    (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A) (hrank : primeRank p A ≤ 2)
    (a : MulAut d.fixedGroup) (haA : a∈A) (ha : orderOf a=p) :
    a ∈ MulAut.innerSubgroup d.fixedGroup := by
  by_contra hout
  obtain ⟨_,g,σ,he,hσ,hσA,hoσ,hiσ⟩ :=
    LocalBlockInput.exists_prime_field_representative hm d A hinner a haA ha hout
  have hh := field_actor_rank_three d center_eq_bot_of_simple_perfect hd A hinner
    σ.val hoσ σ.property hσA hiσ
  omega
end ReeF4.OddDegreeFieldActors
