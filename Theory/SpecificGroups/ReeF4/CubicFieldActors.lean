module
public import Theory.SpecificGroups.ReeF4.CubicRank
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Cubic field actors of the concrete Ree groups

The actual embedding of the binary Ree group lies in the smaller exceptional
fixed subgroup. Its matrix entries are therefore fixed by squaring, so its
elementary subgroup of order nine is fixed by the canonical Frobenius.
This retains the literal subfield map and supplied `LocalBlockInput` matrices.

The proved trace separation makes the cyclic field subgroup inject into the
outer quotient. A cubic field actor, together with the faithful inner image
of the fixed elementary nine, forces three-rank at least three. The existing
inner–field coverage therefore makes every three-power actor inner in an
automorphism subgroup of three-rank at most two containing all inner actors.

The concrete model and original-action consumers inherit simplicity and
perfectness from the actual source component. They add no field-degree,
subfield-placement, fixed-group, or classification premise.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and the Ree branch of
14.2.15, printed pp.985–986; native subfield and field-separation sources are
recorded in the imported modules.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace ReeF4.CubicFieldActors
variable {m : ℕ}

private theorem binary_elementary_nine :
    ∃ E : Subgroup (Model 0), IsElementaryAbelian 3 E ∧ Nat.card E = 3^2 := by
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := Model 0) (p := 3)
  let := hE
  have hd : 3^2 ∣ Nat.card E := by
    rw [hcard]
    exact Nat.pow_dvd_pow 3 (CubicRank.model 0)
  obtain ⟨B,hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 hd
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.of_injective B.subtype B.subtype_injective
  refine ⟨B.map E.subtype,IsElementaryAbelian.map E.subtype,?_⟩
  rw [card_map_of_injective E.subtype_injective,hB]

/-- The binary subfield nine is fixed by the actual canonical Frobenius. -/
theorem exists_fixed_elementary_cubic (d : LocalBlockInput m) :
    ∃ E : Subgroup d.fixedGroup, IsElementaryAbelian 3 E ∧ Nat.card E = 3^2 ∧
      E ≤ d.fieldAutomorphism.fixedSubgroup := by
  obtain ⟨f⟩ := Subfield.nonempty_coefficientHom (k := 0) (m := m) (by simp)
  let hdiv : (2*0+1) ∣ (2*m+1) := by simp
  let j : Model 0 →* d.fixedGroup := d.modelEquiv.symm.toMonoidHom.comp (Subfield.reeMap hdiv f)
  have hj : Function.Injective j := d.modelEquiv.symm.injective.comp (Subfield.reeMap_injective hdiv f)
  have hfix (x : Model 0) : d.fieldAutomorphism (j x) = j x := by
    have hx : Subfield.reeMap hdiv f x ∈ Subfield.fixedSubfield m 0 :=
      Subfield.reeMap_range_le hdiv f ⟨x,rfl⟩
    have he : (j x : SplitGroup m) = toSplitGroup m (Subfield.reeMap hdiv f x) := by
      have hh := (d.modelEquiv_coe (j x)).symm
      simpa only [j,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply,toSplitGroup_apply] using hh
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i k
    rw [d.fieldAutomorphism_entry,he]
    simpa using Subfield.entry_pow_eq_of_mem_fixedSubfield hx i k
  obtain ⟨E,hE,hcard⟩ := binary_elementary_nine
  let := hE
  refine ⟨E.map j,IsElementaryAbelian.map j,?_,?_⟩
  · rw [card_map_of_injective hj,hcard]
  · rintro _ ⟨x,_,rfl⟩
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hfix x)

private theorem fieldOuter_injective (d : LocalBlockInput m) :
    Function.Injective d.fieldOuterHom := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  apply Subtype.ext
  apply Subgroup.disjoint_def.mp (Cartan.field_disjoint_innerDiagonal d) x.property
  apply Cartan.inner_le_innerDiagonal d
  exact (QuotientGroup.eq_one_iff _).mp hx

/-- A cubic element of the canonical field subgroup forces rank three. -/
theorem fixedGroup_cubic_field_actor_rank_three (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (A : Subgroup (MulAut d.fixedGroup))
    (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A)
    (b : MulAut d.fixedGroup) (hb : orderOf b = 3)
    (hbField : b ∈ zpowers d.fieldAutomorphism) (hbA : b ∈ A) :
    3 ≤ primeRank 3 A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary_cubic d
  let := hE
  let f : d.fixedGroup →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect)
      (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map f
  let x : A := ⟨b,hbA⟩
  have hx : orderOf x = 3 :=
    (orderOf_injective A.subtype A.subtype_injective x).symm.trans hb
  have hxB : x ∉ B := by
    rintro ⟨g,_,he⟩
    have hi : b ∈ MulAut.innerSubgroup d.fixedGroup := ⟨g,congrArg Subtype.val he⟩
    have hbone := Subgroup.disjoint_def.mp (Cartan.field_disjoint_innerDiagonal d)
      hbField (Cartan.inner_le_innerDiagonal d hi)
    rw [hbone,orderOf_one] at hb
    norm_num at hb
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    have hgfix : b g = g := by
      obtain ⟨n,hn⟩ := hbField
      rw [←hn]
      exact MulAction.mem_fixedBy_zpow
        (show g ∈ MulAction.fixedBy d.fixedGroup d.fieldAutomorphism from
          (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)) n
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    change g * b y * g⁻¹ = b (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B = 3^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

private theorem primePower_inner_of_cyclic_field
    {G : Type*} [Group G] [Finite G] (φ : MulAut G)
    (hfaithful : Function.Injective
      ((QuotientGroup.mk' (MulAut.innerSubgroup G)).comp (zpowers φ).subtype))
    (hcover : ∀ a : MulAut G, ∃ g : G, ∃ n : ℤ, a = MulAut.conj g * φ ^ n)
    (A : Subgroup (MulAut G)) (hinner : MulAut.innerSubgroup G ≤ A)
    (hfieldrank : ∀ b : MulAut G, orderOf b = 3 → b ∈ zpowers φ → b ∈ A →
      3 ≤ primeRank 3 A)
    (hrank : primeRank 3 A ≤ 2) (a : MulAut G) (haA : a ∈ A)
    (ha : ∃ k : ℕ, a ^ (3^k) = 1) : a ∈ MulAut.innerSubgroup G := by
  let fieldOuter := (QuotientGroup.mk' (MulAut.innerSubgroup G)).comp (zpowers φ).subtype

  obtain ⟨k,hak⟩ := ha
  obtain ⟨g,n,he⟩ := hcover a
  let b : zpowers φ := ⟨φ ^ n,zpow_mem_zpowers _ n⟩
  let q : MulAut G →* MulAut.Outer G := QuotientGroup.mk' (MulAut.innerSubgroup G)
  have hqb : fieldOuter b = q a := by
    change q (φ ^ n) = q a
    rw [he,map_mul]
    have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [hg,one_mul]
  have hbk : b ^ (3^k) = 1 := by
    apply hfaithful
    rw [map_pow,hqb,←map_pow,hak,map_one,map_one]
  have hbA : (b : MulAut G) ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) haA
    rwa [he,inv_mul_cancel_left] at hh
  have hb : b = 1 := by
    by_contra hn
    have hp : IsPGroup 3 (zpowers b) := IsPGroup.of_card_dvd_pow (n := k)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hbk)
    have hdP : 3 ∣ Nat.card (zpowers b) := hp.card_eq_or_dvd.resolve_left (by
      intro hc
      have hh := (card_eq_one.mp hc : zpowers b = ⊥)
      exact hn (mem_bot.mp (hh ▸ mem_zpowers b)))
    obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 3 hdP
    let τ : MulAut G := (t.val : MulAut G)
    have hτA : τ ∈ A := by
      obtain ⟨r,hr⟩ := t.property
      change (t.val : MulAut G) ∈ A
      rw [←hr]
      exact A.zpow_mem hbA r
    have hτp : orderOf τ = 3 := by
      let i : zpowers b →* MulAut G := (zpowers φ).subtype.comp (zpowers b).subtype
      have hi : Function.Injective i :=
        (zpowers φ).subtype_injective.comp (zpowers b).subtype_injective
      exact (orderOf_injective i hi t).trans ht
    have hh := hfieldrank τ hτp t.val.property hτA
    omega
  have hbone : φ ^ n = 1 := congrArg Subtype.val hb
  rw [he,hbone,mul_one]
  exact ⟨g,rfl⟩

/-- Every three-power actor in the given rank-two full-inner subgroup is inner. -/
theorem fixedGroup_cubic_primePower_actor_inner (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (A : Subgroup (MulAut d.fixedGroup))
    (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A) (hrank : primeRank 3 A ≤ 2)
    (a : MulAut d.fixedGroup) (haA : a ∈ A) (ha : ∃ k : ℕ, a ^ (3^k) = 1) :
    a ∈ MulAut.innerSubgroup d.fixedGroup :=
  primePower_inner_of_cyclic_field d.fieldAutomorphism (fieldOuter_injective d)
    (LocalBlockInput.inner_field hm d) A hinner
    (fixedGroup_cubic_field_actor_rank_three d A hinner) hrank a haA ha

/-- The statement for the concrete Ree carrier, with the source's inherited
simplicity and perfectness instances. -/
theorem cubic_primePower_actor_inner (hm : 1 ≤ m)
    [IsSimpleGroup (Model m)] [Group.IsPerfect (Model m)]
    (A : Subgroup (MulAut (Model m)))
    (hinner : MulAut.innerSubgroup (Model m) ≤ A) (hrank : primeRank 3 A ≤ 2)
    (a : MulAut (Model m)) (haA : a ∈ A) (ha : ∃ k : ℕ, a ^ (3^k) = 1) :
    a ∈ MulAut.innerSubgroup (Model m) := by
  let d := canonicalLocalBlockInput m
  let e := d.modelEquiv.symm
  let : IsSimpleGroup d.fixedGroup := d.modelEquiv.isSimpleGroup
  let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let c := MulAut.congr e
  let B := A.map c.toMonoidHom
  have hB : MulAut.innerSubgroup d.fixedGroup ≤ B := by
    rw [←MulAut.map_innerSubgroup_congr e]
    exact map_mono hinner
  have hrB : primeRank 3 B ≤ 2 := by
    rw [←primeRank_equiv 3 (A.equivMapOfInjective c.toMonoidHom c.injective)]
    exact hrank
  have hb := fixedGroup_cubic_primePower_actor_inner hm d B hB hrB (c a)
    (mem_map_of_mem _ haA) (by
      obtain ⟨k,hk⟩ := ha
      exact ⟨k,by rw [←map_pow,hk,map_one]⟩)
  rw [←MulAut.map_innerSubgroup_congr e] at hb
  obtain ⟨b,hb,he⟩ := hb
  exact c.injective he ▸ hb

/-- The original action-map consumer retains the literal action image. -/
theorem cubic_primePower_action_inner (hm : 1 ≤ m)
    [IsSimpleGroup (Model m)] [Group.IsPerfect (Model m)]
    {D : Type*} [Group D] (ρ : D →* MulAut (Model m))
    (hinner : MulAut.innerSubgroup (Model m) ≤ ρ.range)
    (hrank : primeRank 3 ρ.range ≤ 2) (d : D) (hd : ∃ k : ℕ, d ^ (3^k) = 1) :
    ρ d ∈ MulAut.innerSubgroup (Model m) := by
  apply cubic_primePower_actor_inner hm ρ.range hinner hrank (ρ d) ⟨d,rfl⟩
  obtain ⟨k,hk⟩ := hd
  exact ⟨k,by rw [←map_pow,hk,map_one]⟩

end ReeF4.CubicFieldActors
