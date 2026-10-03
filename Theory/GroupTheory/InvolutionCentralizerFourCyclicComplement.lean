module

public import Theory.GroupTheory.PGroup.CyclicAbelianization
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic

/-!
# A cyclic index-two subgroup omitting a noncentral involution

In a finite two-group, a noncentral involution with centralizer of order four
lies outside some cyclic subgroup of index two. This supplies the cyclic
subgroup needed for dihedral and semidihedral recognition, without assuming
either classification or a maximal-class theorem.

Noncentrality and the cyclic-abelianization theorem bound the derived index
below by four. Orbit-stabilizer gives the reverse bound and shows that every
derived element is a commutator with the involution. Consequently the
involution inverts the derived subgroup, which is abelian, and lies outside
it. The noncyclic quotient of order four has exponent two, so the Frattini
and derived subgroups coincide. In the derived subgroup, the square kernel
embeds properly in the four-element centralizer and therefore has order at
most two. The square image has the same index; lifting a generator of its
quotient and applying Frattini nongeneration proves derived cyclicity.

For a derived generator `d`, choose `g` with `[g,x] = d`. Writing `g² = d^s`
gives `(g*x)² = d^(1-s)`. One exponent is odd, so one square generates the
derived subgroup. Its square root generates a subgroup of index two, whose
unique involution lies in the nontrivial derived subgroup and hence is not
`x`.

Source motivation: Stellmacher, Section 11, case (I), and Gorenstein,
Finite Groups (1968), Section 5.4.5. The counting and square arguments here
spell out the structural reductions needed by that recognition step.
-/

universe u

open scoped commutatorElement
open scoped IsMulCommutative

private theorem four_le_commutator_index
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hxZ : x ∉ Subgroup.center G) :
    4 ≤ (commutator G).index := by
  obtain ⟨k, hk⟩ := (hG.to_quotient (commutator G)).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hdiv : Nat.card (G ⧸ commutator G) ∣ 2 := by
      rw [hk]
      interval_cases k <;> norm_num
    let : IsCyclic (G ⧸ commutator G) := isCyclic_of_card_dvd_prime hdiv
    let : IsCyclic G := hG.isCyclic_of_cyclic_abelianization
    exact hxZ (by simp [Subgroup.center_eq_top])
  change 4 ≤ Nat.card (G ⧸ commutator G)
  rw [hk]
  exact Nat.pow_le_pow_right (n := 2) (by decide) hk2

private theorem commutator_index_and_surjectivity_of_centralizer_card_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hxZ : x ∉ Subgroup.center G)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    (commutator G).index = 4 ∧
      ∀ z ∈ commutator G, ∃ g : G, ⁅g, x⁆ = z := by
  let orbit := MulAction.orbit (ConjAct G) x
  let comm : orbit → commutator G := fun y => ⟨y.val * x⁻¹, by
    obtain ⟨g, hg⟩ := y.property
    rw [← hg]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  have hinj : Function.Injective comm := by
    intro y z hyz
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val hyz)
  have hstab : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (MulAction.stabilizer (ConjAct G) x) := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    rfl
  have hcount : Nat.card orbit * 4 = Nat.card G := by
    have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) x)
    rw [Nat.card_prod, ← hstab, hC] at hc
    exact hc
  have hindex := four_le_commutator_index hG x hxZ
  have hproduct := (commutator G).index_mul_card
  have hbound : Nat.card (commutator G) ≤ Nat.card orbit := by
    nlinarith
  have horbit_le := Nat.card_le_card_of_injective comm hinj
  have hpos := Nat.card_pos (α := commutator G)
  refine ⟨by nlinarith, ?_⟩
  have hsurj := (hinj.bijective_of_nat_card_le hbound).surjective
  intro z hz
  obtain ⟨y, hy⟩ := hsurj ⟨z, hz⟩
  obtain ⟨g, hg⟩ := y.property
  refine ⟨ConjAct.ofConjAct g, ?_⟩
  have heq := congrArg Subtype.val hy
  change y.val * x⁻¹ = z at heq
  rw [← hg] at heq
  exact heq

private theorem involution_inverts_commutator_of_centralizer_card_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hx : orderOf x = 2) (hxZ : x ∉ Subgroup.center G)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    ∀ z ∈ commutator G, x * z * x⁻¹ = z⁻¹ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by
    simpa [pow_two, hx] using pow_orderOf_eq_one x)
  intro z hz
  obtain ⟨g, rfl⟩ :=
    (commutator_index_and_surjectivity_of_centralizer_card_four hG x hxZ hC).2 z hz
  simp only [commutatorElement_def, mul_inv_rev, inv_inv]
  group
  simp [hxinv]
  exact hx ▸ pow_orderOf_eq_one x

private theorem commutator_isMulCommutative_of_centralizer_card_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hx : orderOf x = 2) (hxZ : x ∉ Subgroup.center G)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    IsMulCommutative (commutator G) := by
  have hinv := involution_inverts_commutator_of_centralizer_card_four hG x hx hxZ hC
  apply isMulCommutative_iff.mpr
  intro a b
  apply Subtype.ext
  have hm := (MulAut.conj x).map_mul (a : G) (b : G)
  change x * ((a : G) * (b : G)) * x⁻¹ =
    (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹) at hm
  rw [hinv _ ((commutator G).mul_mem a.property b.property),
    hinv _ a.property, hinv _ b.property] at hm
  simpa using congrArg Inv.inv hm

private theorem involution_notMem_commutator_of_centralizer_card_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hx : orderOf x = 2) (hxZ : x ∉ Subgroup.center G)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    x ∉ commutator G := by
  intro hxD
  obtain ⟨g, hg⟩ :=
    (commutator_index_and_surjectivity_of_centralizer_card_four hG x hxZ hC).2
      x⁻¹ ((commutator G).inv_mem hxD)
  have hh : g * x * g⁻¹ = 1 := by
    have heq := congrArg (fun y : G => y * x) hg
    simpa [commutatorElement_def, mul_assoc] using heq
  have hx1 : x = 1 := by
    apply (MulAut.conj g).injective
    simpa using hh
  simp [hx1] at hx

private theorem frattini_eq_commutator_of_centralizer_card_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hxZ : x ∉ Subgroup.center G)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    frattini G = commutator G := by
  let : Fact (IsPGroup 2 G) := ⟨hG⟩
  have hcard : Nat.card (G ⧸ commutator G) = 2 ^ 2 :=
    (commutator_index_and_surjectivity_of_centralizer_card_four hG x hxZ hC).1
  have hncyc : ¬ IsCyclic (G ⧸ commutator G) := by
    intro hcyc
    let : IsCyclic (G ⧸ commutator G) := hcyc
    let : IsCyclic G := hG.isCyclic_of_cyclic_abelianization
    exact hxZ (by simp [Subgroup.center_eq_top])
  have hexp : Monoid.exponent (G ⧸ commutator G) = 2 :=
    (not_isCyclic_iff_exponent_eq_prime Nat.prime_two hcard).mp hncyc
  apply le_antisymm _ (commutator_le_frattini_of_isPGroup (p := 2))
  rw [frattini_eq_closure_commutator_union_powers (p := 2)]
  apply (Subgroup.closure_le (commutator G)).mpr
  intro y hy
  rcases hy with hy | ⟨g, rfl⟩
  · exact hy
  · apply (QuotientGroup.eq_one_iff (N := commutator G) (x := g ^ 2)).mp
    change QuotientGroup.mk' (commutator G) (g ^ 2) = 1
    have hpow := Monoid.pow_exponent_eq_one (QuotientGroup.mk' (commutator G) g)
    simpa only [hexp, map_pow] using hpow

private theorem cyclic_of_square_kernel_bound
    {A : Type u} [CommGroup A] [Finite A] (hA : IsPGroup 2 A)
    (hker : Nat.card (powMonoidHom 2 : A →* A).ker ≤ 2) : IsCyclic A := by
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let squares := (powMonoidHom 2 : A →* A).range
  have hindex : squares.index ≤ 2 := by rwa [Subgroup.index_range]
  have hpositive := Nat.card_pos (α := A ⧸ squares)
  have hdiv : Nat.card (A ⧸ squares) ∣ 2 := by
    change Nat.card (A ⧸ squares) ≤ 2 at hindex
    interval_cases Nat.card (A ⧸ squares) <;> norm_num
  let : IsCyclic (A ⧸ squares) := isCyclic_of_card_dvd_prime hdiv
  obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (A ⧸ squares))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective squares q
  have hmap : (Subgroup.zpowers a).map (QuotientGroup.mk' squares) = ⊤ := by
    simpa using hq
  have hsup : Subgroup.zpowers a ⊔ squares = ⊤ := by
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' squares)) hmap
  have hsquares : squares ≤ frattini A := by
    rintro y ⟨a, rfl⟩
    exact pth_power_mem_frattini_of_isPGroup (p := 2) a
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨a, frattini_nongenerating (G := A) ?_⟩
  apply top_unique
  rw [← hsup]
  exact sup_le_sup_left hsquares _

private theorem cyclic_of_inverted_subgroup_centralizer_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (H : Subgroup G) [IsMulCommutative H]
    (x : G) (hxH : x ∉ H)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4)
    (hinv : ∀ d ∈ H, x * d * x⁻¹ = d⁻¹) : IsCyclic H := by
  let square := (powMonoidHom 2 : H →* H)
  have hcomm (a : square.ker) : (a.val : G) ∈ Subgroup.centralizer ({x} : Set G) := by
    have ha : (a.val : G) ^ 2 = 1 := congrArg Subtype.val a.property
    have hai : (a.val : G)⁻¹ = (a.val : G) := inv_eq_of_mul_eq_one_right (by
      simpa [pow_two] using ha)
    have hi := hinv (a.val : G) a.val.property
    rw [hai] at hi
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hi' := congrArg (fun y : G => y * x) hi
    simpa [mul_assoc] using hi'.symm
  let embedding : square.ker →* Subgroup.centralizer ({x} : Set G) :=
    { toFun := fun a => ⟨a.val.val, hcomm a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hemb : Function.Injective embedding := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : Subgroup.centralizer ({x} : Set G) => (c : G)) hab
  have hle := Nat.card_le_card_of_injective embedding hemb
  have hdvd := Subgroup.card_dvd_of_injective embedding hemb
  have hne : Nat.card square.ker ≠ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    intro heq
    have hsurj := (hemb.bijective_of_nat_card_le heq.ge).surjective
    obtain ⟨a, ha⟩ := hsurj ⟨x, by simp [Subgroup.mem_centralizer_singleton_iff]⟩
    apply hxH
    have hav := congrArg Subtype.val ha
    change a.val.val = x at hav
    exact hav ▸ a.val.property
  rw [hC] at hle hdvd hne
  apply cyclic_of_square_kernel_bound (hG.to_subgroup H)
  change Nat.card square.ker ≤ 2
  have hlt : Nat.card square.ker < 4 := lt_of_le_of_ne hle hne
  interval_cases Nat.card square.ker <;> norm_num at *

private theorem derived_isCyclic
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hx : orderOf x = 2) (hxZ : x ∉ Subgroup.center G)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    IsCyclic (commutator G) := by
  let : IsMulCommutative (commutator G) :=
    commutator_isMulCommutative_of_centralizer_card_four hG x hx hxZ hC
  exact cyclic_of_inverted_subgroup_centralizer_four hG (commutator G) x
    (involution_notMem_commutator_of_centralizer_card_four hG x hx hxZ hC) hC
    (involution_inverts_commutator_of_centralizer_card_four hG x hx hxZ hC)

private theorem square_generator_complement
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (H : Subgroup G) (hH : H.index = 4) (hHne : H ≠ ⊥)
    (x a : G) (hx : orderOf x = 2) (hxH : x ∉ H)
    (ha : Subgroup.zpowers (a ^ 2) = H) :
    (Subgroup.zpowers a).index = 2 ∧ x ∉ Subgroup.zpowers a := by
  have ha1 : a ≠ 1 := by
    intro he
    simp [he] at ha
    exact hHne ha.symm
  have hdvd := hG.dvd_orderOf ha1
  have horder : orderOf a = 2 * Nat.card H := by
    have hh := Nat.card_zpowers (a ^ 2)
    rw [ha, orderOf_pow_of_dvd (by decide) hdvd] at hh
    omega
  have hcard := H.index_mul_card
  have hcarda := (Subgroup.zpowers a).index_mul_card
  rw [hH] at hcard
  rw [Nat.card_zpowers, horder] at hcarda
  have hpos := Nat.card_pos (α := H)
  refine ⟨by nlinarith, ?_⟩
  intro hxa
  have hle : H ≤ Subgroup.zpowers a := by
    rw [← ha]
    exact Subgroup.zpowers_le.mpr ((Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) 2)
  have hsub : H.subgroupOf (Subgroup.zpowers a) ≠ ⊥ := by
    intro he
    apply hHne
    apply bot_unique
    intro y hy
    have hm : (⟨y, hle hy⟩ : Subgroup.zpowers a) ∈ H.subgroupOf (Subgroup.zpowers a) := hy
    rw [he, Subgroup.mem_bot] at hm
    exact congrArg Subtype.val hm
  exact hxH ((hG.to_subgroup (Subgroup.zpowers a)).involution_mem_subgroup_of_ne_bot
    (x := ⟨x, hxa⟩) (by simpa using hx) _ hsub)

private theorem consecutive_generates
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G) (d : G) (exponent : ℤ) :
    d ∈ Subgroup.zpowers (d ^ exponent) ∨
      d ∈ Subgroup.zpowers (d ^ (1 - exponent)) := by
  obtain ⟨power, hpower⟩ := hG.exists_orderOf_eq_pow d
  rw [mem_zpowers_zpow_iff, mem_zpowers_zpow_iff, hpower]
  have hparity : exponent.natAbs.Coprime 2 ∨ (1 - exponent).natAbs.Coprime 2 := by
    simp only [Nat.coprime_two_right, Int.natAbs_odd, Int.odd_iff]
    omega
  rcases hparity with hodd | hodd
  · left
    exact hodd.pow_right power
  · right
    exact hodd.pow_right power

private theorem complement_of_cyclic_derived_data
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (H : Subgroup G) [IsCyclic H] (hH : H.index = 4) (hHne : H ≠ ⊥)
    (x : G) (hx : orderOf x = 2) (hxH : x ∉ H)
    (hsurj : ∀ d ∈ H, ∃ g : G, ⁅g, x⁆ = d)
    (hsquare : ∀ g : G, g ^ 2 ∈ H)
    (hinv : ∀ d ∈ H, x * d * x⁻¹ = d⁻¹) :
    ∃ a : G, (Subgroup.zpowers a).index = 2 ∧ x ∉ Subgroup.zpowers a := by
  obtain ⟨d, hd⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hdH : d ∈ H := hd ▸ Subgroup.mem_zpowers d
  obtain ⟨g, hg⟩ := hsurj d hdH
  obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp (hd ▸ hsquare g)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by
    simpa [pow_two, hx] using pow_orderOf_eq_one x)
  have hidentity : (g * x) ^ 2 = d ^ (1 - exponent) := by
    have hinvg := hinv (g ^ 2) (hsquare g)
    rw [← hexponent] at hinvg
    rw [zpow_sub, zpow_one, hexponent]
    rw [← hg]
    simp only [commutatorElement_def]
    have hinvg' : x * g ^ 2 * x⁻¹ = (g ^ 2)⁻¹ := by simpa [hexponent] using hinvg
    rw [← hinvg']
    group
    simp [hxinv]
    simp [pow_two, mul_assoc]
  have hchoice : Subgroup.zpowers (g ^ 2) = H ∨ Subgroup.zpowers ((g * x) ^ 2) = H := by
    rcases consecutive_generates hG d exponent with hmem | hmem
    · left
      apply le_antisymm
      · exact Subgroup.zpowers_le.mpr (hsquare g)
      · rw [← hd]
        exact Subgroup.zpowers_le.mpr (hexponent ▸ hmem)
    · right
      apply le_antisymm
      · exact Subgroup.zpowers_le.mpr (hsquare (g * x))
      · rw [← hd]
        exact Subgroup.zpowers_le.mpr (hidentity ▸ hmem)
  rcases hchoice with ha | ha
  · exact ⟨g, square_generator_complement hG H hH hHne x g hx hxH ha⟩
  · exact ⟨g * x, square_generator_complement hG H hH hHne x (g * x) hx hxH ha⟩

public theorem exists_zpowers_index_two_of_involution_centralizer_card_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (x : G) (hx : orderOf x = 2) (hxZ : x ∉ Subgroup.center G)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    ∃ a : G, (Subgroup.zpowers a).index = 2 ∧ x ∉ Subgroup.zpowers a := by
  let : IsCyclic (commutator G) := derived_isCyclic hG x hx hxZ hC
  let : Fact (IsPGroup 2 G) := ⟨hG⟩
  have hne : commutator G ≠ ⊥ := by
    intro he
    exact hxZ (by simp [(commutator_eq_bot_iff_center_eq_top G).mp he])
  have hsquare (g : G) : g ^ 2 ∈ commutator G := by
    rw [← frattini_eq_commutator_of_centralizer_card_four hG x hxZ hC]
    exact pth_power_mem_frattini_of_isPGroup (p := 2) g
  obtain ⟨hindex, hsurj⟩ :=
    commutator_index_and_surjectivity_of_centralizer_card_four hG x hxZ hC
  exact complement_of_cyclic_derived_data hG (commutator G) hindex hne x hx
    (involution_notMem_commutator_of_centralizer_card_four hG x hx hxZ hC)
    hsurj hsquare (involution_inverts_commutator_of_centralizer_card_four hG x hx hxZ hC)
