module

public import Theory.SpecificGroups.GL2.ThreeResidualImages
public import Theory.GroupTheory.ConjugateSpanKernel
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# The literal action and its Frattini image for cubic two-residuals

A proper action kernel of a two-perfect group with cubic two-core quotient
lies in its two-core. Consequently passage to the Frattini quotient of an
odd p-group cannot enlarge this kernel: the image of the enlarged kernel
would be simultaneously a two-group and a p-group. An actual cubic actor
therefore survives both actions. In characteristic three the existing
GL₂(3) classification gives the determinant kernel and order 24 as soon
as the original two-core has nontrivial image.

These are the action comparisons in Aschbacher--Smith 15.4.10, printed
p.1159. They preserve the supplied homomorphisms; no abstract affine model
or prime-five image classification is assumed.
-/

public section
open Subgroup Matrix
namespace Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
variable {X P : Type*} [Group X] [Finite X] [Group P] [Finite P]

omit [Finite X] in
/-- Nontrivial two-core action survives the literal Frattini quotient. -/
theorem twoCore_frattini_image_ne_bot {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hP : IsPGroup p P) (a : X →* MulAut P)
    (hne : (pCore 2 X).map a ≠ ⊥) :
    (pCore 2 X).map ((quotientAut (frattini P)).comp a) ≠ ⊥ := by
  intro hbot
  apply hne
  apply eq_bot_iff.mpr
  rintro y ⟨x, hx, rfl⟩
  have hb : a x ∈ (quotientAut (frattini P)).ker :=
    mem_bot.mp (hbot ▸ mem_map_of_mem ((quotientAut (frattini P)).comp a) hx)
  exact Subgroup.disjoint_def.mp
    (IsPGroup.disjoint_of_coprime (pCore_isPGroup.map a)
      (isPGroup_quotientAut_frattini_kernel hP)
      ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm))
    (mem_map_of_mem a hx) hb

/-- The original action and its Frattini action have exactly the same kernel.
The properness assumption concerns the Frattini action, not an assumed model. -/
theorem frattini_action_ker_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hP : IsPGroup p P) (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (a : X →* MulAut P)
    (hne : ((quotientAut (frattini P)).comp a).ker ≠ ⊤) :
    ((quotientAut (frattini P)).comp a).ker = a.ker := by
  let b := (quotientAut (frattini P)).comp a
  have hcore : b.ker ≤ pCore 2 X :=
    normal_le_pCore_of_pPerfect_prime_quotient hX (by rw [hX3]; exact Nat.prime_three)
      b.ker hne
  apply le_antisymm ?_ (by intro x hx; change quotientAut (frattini P) (a x) = 1; rw [hx, map_one])
  intro x hx
  change a x = 1
  exact Subgroup.disjoint_def.mp
    (IsPGroup.disjoint_of_coprime (pCore_isPGroup.map a)
      (isPGroup_quotientAut_frattini_kernel hP)
      ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm))
    (mem_map_of_mem a (hcore hx)) hx

/-- Equality of the actual kernels gives equality of the image cardinalities. -/
theorem frattini_action_card_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hP : IsPGroup p P) (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (a : X →* MulAut P)
    (hne : ((quotientAut (frattini P)).comp a).ker ≠ ⊤) :
    Nat.card a.range = Nat.card (((quotientAut (frattini P)).comp a).range) := by
  let b := (quotientAut (frattini P)).comp a
  let e := (QuotientGroup.quotientKerEquivRange a).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (frattini_action_ker_eq hp hP hX hX3 a hne).symm).trans
      (QuotientGroup.quotientKerEquivRange b))
  exact Nat.card_congr e.toEquiv

omit [Finite P] in
/-- Every actual element of order three survives a proper Frattini action.
There is no assertion that a cubic element in a quotient has a cubic lift. -/
theorem cubic_actor_survives (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (a : X →* MulAut P)
    (hne : ((quotientAut (frattini P)).comp a).ker ≠ ⊤)
    (x : X) (hx : orderOf x = 3) :
    orderOf (((quotientAut (frattini P)).comp a) x) = 3 ∧ orderOf (a x) = 3 := by
  let b := (quotientAut (frattini P)).comp a
  have hcore : b.ker ≤ pCore 2 X :=
    normal_le_pCore_of_pPerfect_prime_quotient hX (by rw [hX3]; exact Nat.prime_three)
      b.ker hne
  have hk : IsPGroup 2 b.ker := pCore_isPGroup.of_injective (inclusion hcore)
    (inclusion_injective hcore)
  have hb : orderOf (b x) = 3 :=
    (b.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x (by rw [hx]; decide)).trans hx
  refine ⟨hb, Nat.dvd_antisymm (hx ▸ orderOf_map_dvd a x) ?_⟩
  rw [← hb]
  exact orderOf_map_dvd (quotientAut (frattini P)) (a x)

omit [Finite P] in
/-- Cauchy supplies the original cubic actor, which survives both actions. -/
theorem exists_cubic_actor (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (a : X →* MulAut P)
    (hne : ((quotientAut (frattini P)).comp a).ker ≠ ⊤) :
    ∃ x : X, orderOf x = 3 ∧ orderOf (a x) = 3 ∧
      orderOf (((quotientAut (frattini P)).comp a) x) = 3 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3
    (hX3 ▸ card_quotient_dvd_card (pCore 2 X))
  have h := cubic_actor_survives hX hX3 a hne x hx
  exact ⟨x, hx, h.2, h.1⟩

omit [Finite X] in
/-- A nontrivial original two-core image excludes the cubic GL₂(3) alternative. -/
theorem ternary_range_eq (hX : IsPPerfect 2 X) (a : X →* GL (Fin 2) (ZMod 3))
    (hne : (pCore 2 X).map a ≠ ⊥) : a.range = threeSpecialLinear := by
  have hr : a.range ≠ ⊥ := by
    intro h
    exact hne (le_bot_iff.mp ((map_le_range a (pCore 2 X)).trans h.le))
  rcases three_twoPerfect_subgroup a.range
    (hX.of_surjective a.rangeRestrict a.rangeRestrict_surjective) hr with hc | he
  · exfalso
    apply hne
    have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup.map a)
      (show IsPGroup 3 a.range from IsPGroup.of_card (n := 1) (by simpa using hc)) (by decide : Nat.Coprime 2 3)
    exact le_bot_iff.mp ((le_inf le_rfl (map_le_range a (pCore 2 X))).trans (disjoint_iff.mp hd).le)
  · exact he

omit [Finite X] in
/-- The literal ternary image has order 24. -/
theorem ternary_range_card (hX : IsPPerfect 2 X) (a : X →* GL (Fin 2) (ZMod 3))
    (hne : (pCore 2 X).map a ≠ ⊥) : Nat.card a.range = 24 := by
  rw [ternary_range_eq hX a hne, Nat.card_congr threeSpecialLinearEquiv.toEquiv,
    Nat.card_eq_fintype_card]
  decide +kernel

/-- In ternary coordinates the order-24 conclusion holds on P itself, not
only on P/Φ(P). The supplied coordinates are an actual automorphism equivalence. -/
theorem ternary_original_action_card (hP : IsPGroup 3 P) (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (a : X →* MulAut P)
    (e : MulAut (P ⧸ frattini P) ≃* GL (Fin 2) (ZMod 3))
    (hne : (pCore 2 X).map a ≠ ⊥) : Nat.card a.range = 24 := by
  let b := (quotientAut (frattini P)).comp a
  have hb : (pCore 2 X).map b ≠ ⊥ := twoCore_frattini_image_ne_bot (by decide) hP a hne
  have hk : b.ker ≠ ⊤ := by
    intro h
    exact hb ((Subgroup.map_eq_bot_iff _).mpr (h ▸ le_top))
  have hc : (pCore 2 X).map (e.toMonoidHom.comp b) ≠ ⊥ := by
    intro h
    apply hb
    apply eq_bot_iff.mpr
    rintro y ⟨x, hx, rfl⟩
    apply e.injective
    simpa only [map_one] using mem_bot.mp (h ▸ mem_map_of_mem (e.toMonoidHom.comp b) hx)
  rw [frattini_action_card_eq (by decide) hP hX hX3 a hk]
  calc
    Nat.card b.range = Nat.card (b.range.map e.toMonoidHom) :=
      Nat.card_congr (b.range.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    _ = 24 := by
      rw [← MonoidHom.range_comp]
      exact ternary_range_card hX _ hc

end Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
