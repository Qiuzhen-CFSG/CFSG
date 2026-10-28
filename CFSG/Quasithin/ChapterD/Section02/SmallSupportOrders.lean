module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportInvolutions
public import Stellmacher.SectionOne.GLFourTwoClassification
public import Theory.GroupAction.OrderFifteenOnSixteen
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupAction.InvertedFifteenOnSixteen

/-!
# Orders on the small binary supports

This module supplies the element-order conclusions in Aschbacher--Smith,
*The Classification of Quasithin Groups*, D.2.11(1--2), printed p.183.
The action of the cyclic odd subgroup is restricted to its commutator support;
faithfulness is transferred through the coprime fixed-space decomposition.
The small-support bound applies to every power of the odd element. Orbit
counting excludes order seven on a sixteen-element support, and the cyclic-nine
obstruction excludes order nine. The GL₄(2) cardinal bound then leaves only
divisors of fifteen. The fixed-point bound for a binary involution excludes order fifteen, leaving
orders three and five.
-/

open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterD

private theorem elementaryAbelian_subgroup
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative :=
    ⟨⟨fun x y => Subtype.ext
      (show (x : V) * (y : V) = (y : V) * (x : V) from
        (IsMulCommutative.is_comm (M := V)).comm x y)⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro z
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (z : V)

private theorem commutatorAction_restriction_faithful
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (K : Subgroup G) (hKodd : Nat.Coprime 2 (Nat.card K))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    let U : Subgroup V := commutatorAction K V
    let : IsInvariant K V U := commutatorAction_isInvariant
    let : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
    Function.Injective
      (Representation.ofElementaryAbelianAction
        (A := K) (G := U) (p := 2)).asGroupHom := by
  let U : Subgroup V := commutatorAction K V
  let hUinv : IsInvariant K V U := commutatorAction_isInvariant
  let : IsInvariant K V U := hUinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let : IsElementaryAbelian 2 U := hUelem
  let rho := Representation.ofElementaryAbelianAction
    (A := K) (G := U) (p := 2)
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro k hk
    have hrhok : rho k = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hk)
    have hkfixU (w : U) : k • w = w := by
      apply Additive.ofMul.injective
      have happ := LinearMap.congr_fun hrhok (Additive.ofMul w)
      simpa [rho] using happ
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    have hcop : Nat.Coprime (Nat.card K) (Nat.card V) := by
      rw [hm]
      exact hKodd.symm.pow_right m
    have hcompl :
        IsCompl (FixedPoints.subgroup K V) U :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := V) (A := K)
        (Group.isSolvable_of_comm fun x y =>
          (IsMulCommutative.is_comm (M := V)).comm x y)
        hcop (inferInstance : IsMulCommutative V)
    have hkfixV (w : V) : (k : G) • w = w := by
      have hwtop : w ∈ (FixedPoints.subgroup K V ⊔ U) := by
        rw [hcompl.sup_eq_top]
        exact Subgroup.mem_top w
      let hfixnorm : (FixedPoints.subgroup K V).Normal :=
        Subgroup.normal_of_isMulCommutative _
      let : (FixedPoints.subgroup K V).Normal := hfixnorm
      rcases Subgroup.mem_sup_of_normal_left.mp hwtop with
        ⟨c, hc, z, hz, hcz⟩
      have hkc : k • c = c :=
        (FixedPoints.mem_subgroup (M := K) (a := c)).1 hc k
      have hkc' : (k : G) • c = c := by
        simpa only [Subgroup.smul_def] using hkc
      have hkz : (k : G) • z = z :=
        congrArg Subtype.val (hkfixU ⟨z, hz⟩)
      rw [← hcz, smul_mul', hkc', hkz]
    have hkG : (k : G) ∈ fixingSubgroup G (Set.univ : Set V) :=
      (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set V))).2
        (fun w _ => hkfixV w)
    rw [hfaith] at hkG
    simpa using hkG
  · exact bot_le

private theorem card_zpowers_dvd_gl_of_support_card
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x : G) (hodd : Odd (orderOf x))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers x) V) = 4 ∨
      Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16) :
    Nat.card (Subgroup.zpowers x) ∣ (if Nat.card (commutatorAction (Subgroup.zpowers x) V) = 4 then 6 else 20160) := by
  let U : Subgroup V := commutatorAction (Subgroup.zpowers x) V
  let hUinv : IsInvariant (Subgroup.zpowers x) V U := commutatorAction_isInvariant
  let : IsInvariant (Subgroup.zpowers x) V U := hUinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let : IsElementaryAbelian 2 U := hUelem
  let K := Subgroup.zpowers x
  have hKodd : Nat.Coprime 2 (Nat.card K) := by
    simpa [K, Nat.card_zpowers] using hodd
  have hρinj : Function.Injective
      (Representation.ofElementaryAbelianAction
        (A := K) (G := U) (p := 2)).asGroupHom := by
    change Function.Injective
      (Representation.ofElementaryAbelianAction
        (A := Subgroup.zpowers x)
        (G := commutatorAction (Subgroup.zpowers x) V) (p := 2)).asGroupHom
    exact commutatorAction_restriction_faithful (K := Subgroup.zpowers x)
      hKodd hfaith
  let nU := Module.finrank (ZMod 2) (Additive U)
  have hcardU : Nat.card U = 4 ∨ Nat.card U = 16 := by simpa [U] using hcard
  have hnU : nU = 2 ∨ nU = 4 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = Nat.card (ZMod 2) ^ nU at hc
    rw [show Nat.card (ZMod 2) = 2 by norm_num] at hc
    rcases hcardU with h4 | h16
    · left
      rw [h4] at hc
      exact Nat.pow_right_injective (by omega : 1 < 2) hc.symm
    · right
      rw [h16] at hc
      exact Nat.pow_right_injective (by omega : 1 < 2) hc.symm
  rcases hnU with h2 | h4
  · let b : Module.Basis (Fin 2) (ZMod 2) (Additive U) :=
      Module.finBasisOfFinrankEq (ZMod 2) (Additive U) h2
    have hU4 : Nat.card U = 4 := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
      change Nat.card U = Nat.card (ZMod 2) ^ nU at hc
      rw [show Nat.card (ZMod 2) = 2 by norm_num, h2] at hc
      simpa using hc
    let ρ := Representation.ofElementaryAbelianAction
      (A := K) (G := U) (p := 2)
    let φ : K →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
      (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
    have hφinj : Function.Injective φ :=
      (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρinj
    have hdiv : Nat.card K ∣
        Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
      Subgroup.card_dvd_of_injective φ hφinj
    have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    rw [hgl] at hdiv
    simpa [K, U, hU4] using hdiv
  · let b : Module.Basis (Fin 4) (ZMod 2) (Additive U) :=
      Module.finBasisOfFinrankEq (ZMod 2) (Additive U) h4
    have hU16 : Nat.card U = 16 := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
      change Nat.card U = Nat.card (ZMod 2) ^ nU at hc
      rw [show Nat.card (ZMod 2) = 2 by norm_num, h4] at hc
      simpa using hc
    let ρ := Representation.ofElementaryAbelianAction
      (A := K) (G := U) (p := 2)
    let φ : K →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
      (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
    have hφinj : Function.Injective φ :=
      (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρinj
    have hdiv : Nat.card K ∣
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
      Subgroup.card_dvd_of_injective φ hφinj
    have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    rw [hgl] at hdiv
    simpa [K, U, hU16] using hdiv

public theorem invertedOddElement_order_three_of_involution_card_two
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hx : x ≠ 1) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 2)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    orderOf x = 3 ∧ Nat.card (commutatorAction (Subgroup.zpowers x) V) = 4 := by
  have hfour := invertedOddElement_support_card_four_of_involution_card_two
    x t hx hodd ht hinv hcard hfaith
  have hdvd := card_zpowers_dvd_gl_of_support_card x hodd hfaith (Or.inl hfour)
  rw [hfour] at hdvd
  have horderdvd : orderOf x ∣ 6 := by simpa [Nat.card_zpowers] using hdvd
  have hne : orderOf x ≠ 1 := by
    intro h
    exact hx (orderOf_eq_one_iff.mp h)
  have hle : orderOf x ≤ 6 := Nat.le_of_dvd (by norm_num) horderdvd
  obtain ⟨m, hm⟩ := hodd
  have hm' : orderOf x = m + m + 1 := by
    simpa [two_mul, Nat.add_assoc] using hm
  have hmle : m ≤ 2 := by
    by_contra h
    have hm3 : 3 ≤ m := by omega
    have hn7 : 7 ≤ orderOf x := by omega
    omega
  obtain ⟨k, hk⟩ := horderdvd
  have hcases : orderOf x = 1 ∨ orderOf x = 3 := by
    interval_cases m
    · left; omega
    · right; omega
    · exfalso
      have hn5 : orderOf x = 5 := by omega
      rw [hn5] at hk
      have hk' : 6 = k + k + k + k + k := by
        simpa [Nat.mul_comm, Nat.mul_succ, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hk
      omega
  exact ⟨hcases.resolve_left hne, hfour⟩

public theorem invertedOddElement_order_three_of_support_card_four
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hx : x ≠ 1) (hodd : Odd (orderOf x)) (_ht : IsInvolution t)
    (_hinv : t * x * t⁻¹ = x⁻¹)
    (hcardx : Nat.card (commutatorAction (Subgroup.zpowers x) V) = 4)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    orderOf x = 3 := by
  have hdvd := card_zpowers_dvd_gl_of_support_card x hodd hfaith (Or.inl hcardx)
  rw [hcardx] at hdvd
  have horderdvd : orderOf x ∣ 6 := by simpa [Nat.card_zpowers] using hdvd
  have hne : orderOf x ≠ 1 := by
    intro h
    exact hx (orderOf_eq_one_iff.mp h)
  have hle : orderOf x ≤ 6 := Nat.le_of_dvd (by norm_num) horderdvd
  obtain ⟨m, hm⟩ := hodd
  have hm' : orderOf x = m + m + 1 := by
    simpa [two_mul, Nat.add_assoc] using hm
  have hmle : m ≤ 2 := by
    by_contra h
    have hm3 : 3 ≤ m := by omega
    have hn7 : 7 ≤ orderOf x := by omega
    omega
  obtain ⟨k, hk⟩ := horderdvd
  have hcases : orderOf x = 1 ∨ orderOf x = 3 := by
    interval_cases m
    · left; omega
    · right; omega
    · exfalso
      have hn5 : orderOf x = 5 := by omega
      rw [hn5] at hk
      have hk' : 6 = k + k + k + k + k := by
        simpa [Nat.mul_comm, Nat.mul_succ, Nat.mul_one, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hk
      omega
  exact hcases.resolve_left hne

public theorem invertedOddElement_order_five_support_card_sixteen
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (horder : orderOf x = 5)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V)) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16 := by
  have hcard := invertedOddElement_commutatorAction_card_eq_four_or_sixteen
    x t (by intro hx; subst x; simp at horder) (by simpa [horder] using hodd)
    ht hinv hindex hfaith
  rcases hcard with h4 | h16
  · exfalso
    have hthree := invertedOddElement_order_three_of_support_card_four
      x t (by intro hx; subst x; simp at horder) hodd ht hinv h4 hfaith
    omega
  · simpa using h16

private theorem support_fixed_eq_bot
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (K : Subgroup G) (hodd : Odd (Nat.card K)) :
    let U := commutatorAction K V
    let : IsInvariant K V U := commutatorAction_isInvariant
    FixedPoints.subgroup K U = ⊥ := by
  let U := commutatorAction K V
  let : IsInvariant K V U := commutatorAction_isInvariant
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hcop : Nat.Coprime (Nat.card K) (Nat.card V) := by
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hc := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := K) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact hc.disjoint.le_bot ⟨fun k => congrArg Subtype.val (hv k), v.property⟩

private theorem support_action_faithful
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (K : Subgroup G) (hodd : Odd (Nat.card K))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    let U := commutatorAction K V
    let : IsInvariant K V U := commutatorAction_isInvariant
    fixingSubgroup K (Set.univ : Set U) = ⊥ := by
  let U := commutatorAction K V
  let : IsInvariant K V U := commutatorAction_isInvariant
  let : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  have hinj := commutatorAction_restriction_faithful (V := V) K hodd.coprime_two_left hfaith
  apply bot_unique
  intro k hk
  apply hinj
  apply Units.ext
  apply LinearMap.ext
  intro v
  change Additive.ofMul (k • Additive.toMul v) = Additive.ofMul ((1 : K) • Additive.toMul v)
  simp only [one_smul]
  exact congrArg Additive.ofMul
    (((mem_fixingSubgroup_iff (M := K) (s := (Set.univ : Set U))).mp hk)
      (Additive.toMul v) trivial)

private theorem order_ne_seven_of_support_card_sixteen
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x : G) (hcard : Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16) :
    orderOf x ≠ 7 := by
  intro hx
  let K := Subgroup.zpowers x
  let U := commutatorAction K V
  let : IsInvariant K V U := commutatorAction_isInvariant
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hK : Nat.card K = 7 := by simpa [K, Nat.card_zpowers] using hx
  have hp : IsPGroup 7 K := IsPGroup.of_card (n := 1) (by simpa using hK)
  have hfix : FixedPoints.subgroup K U = ⊥ := support_fixed_eq_bot K (by rw [hK]; decide)
  have hm := hp.card_modEq_card_fixedPoints U
  change Nat.ModEq 7 (Nat.card U) (Nat.card (FixedPoints.subgroup K U)) at hm
  rw [hfix] at hm
  have : Nat.ModEq 7 16 1 := by simpa [U, K, hcard] using hm
  norm_num at this

private theorem order_ne_nine_of_support_card_sixteen
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x : G) (hcard : Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    orderOf x ≠ 9 := by
  intro hx
  let K := Subgroup.zpowers x
  let U := commutatorAction K V
  let : IsInvariant K V U := commutatorAction_isInvariant
  have hK : Nat.card K = 9 := by simpa [K, Nat.card_zpowers] using hx
  exact not_isCyclic_of_card_nine_of_faithful_on_card_sixteen hK hcard
    (support_action_faithful K (by rw [hK]; decide) hfaith) inferInstance

/-- The only possible prime divisors are three and five, each to exponent one. -/
public theorem invertedOddElement_order_dvd_fifteen
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hx : x ≠ 1) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) ≤ 4)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    orderOf x ∣ 15 := by
  have hsupport := invertedOddElement_support_card_four_or_sixteen
    x t hx hodd ht hinv hcard hfaith
  have hdvd := card_zpowers_dvd_gl_of_support_card x hodd hfaith hsupport
  have hd : orderOf x ∣ 20160 := by
    rcases hsupport with h4 | h16
    · have hd6 : orderOf x ∣ 6 := by simpa [h4, Nat.card_zpowers] using hdvd
      exact hd6.trans (by norm_num)
    · simpa [h16, Nat.card_zpowers] using hdvd
  have hnot (m : ℕ) (hm : m = 7 ∨ m = 9) : ¬ m ∣ orderOf x := by
    intro hmdiv
    let y := x ^ (orderOf x / m)
    have hyorder : orderOf y = m := orderOf_pow_orderOf_div (orderOf_pos x).ne' hmdiv
    have hy : y ≠ 1 := by
      intro hy
      rw [hy, orderOf_one] at hyorder
      rcases hm with rfl | rfl <;> omega
    have hyodd : Odd (orderOf y) := by
      rw [hyorder]
      rcases hm with rfl | rfl <;> decide
    have hyinv : t * y * t⁻¹ = y⁻¹ := by
      dsimp [y]
      rw [← conj_pow, hinv, inv_pow]
    rcases invertedOddElement_support_card_four_or_sixteen
      y t hy hyodd ht hyinv hcard hfaith with h4 | h16
    · have h3 := invertedOddElement_order_three_of_support_card_four
        y t hy hyodd ht hyinv h4 hfaith
      rcases hm with rfl | rfl <;> omega
    · rcases hm with rfl | rfl
      · exact order_ne_seven_of_support_card_sixteen y h16 hyorder
      · exact order_ne_nine_of_support_card_sixteen y h16 hfaith hyorder
  have h7 := hnot 7 (Or.inl rfl)
  have h9 := hnot 9 (Or.inr rfl)
  have hd315 : orderOf x ∣ 315 :=
    (hodd.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left (by simpa using hd)
  have hmem : orderOf x ∈ Nat.divisors 315 := Nat.mem_divisors.mpr ⟨hd315, by decide⟩
  have hfinite : ∀ n : (Nat.divisors 315),
      ¬ 7 ∣ (n : ℕ) → ¬ 9 ∣ (n : ℕ) → (n : ℕ) ∣ 15 := by decide
  exact hfinite ⟨orderOf x, hmem⟩ h7 h9

private theorem order_ne_fifteen_of_support_card_sixteen
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (ht : IsInvolution t) (hinv : t * x * t⁻¹ = x⁻¹)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    orderOf x ≠ 15 := by
  intro hx
  let K := Subgroup.zpowers x
  let N := Subgroup.normalizer (K : Set G)
  let U := commutatorAction K V
  have hodd : Odd (Nat.card K) := by
    change Odd (Nat.card (Subgroup.zpowers x))
    rw [Nat.card_zpowers, hx]
    decide
  have htN : t ∈ N := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hi (r : G) (hr : r ∈ K) : t * r * t⁻¹ = r⁻¹ := by
      obtain ⟨z, rfl⟩ := hr
      rw [← conj_zpow, hinv, inv_zpow]
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      change t * r * t⁻¹ ∈ K
      rw [hi r hr]
      exact K.inv_mem hr
    · intro r hr
      refine ⟨r⁻¹, K.inv_mem hr, ?_⟩
      change t * r⁻¹ * t⁻¹ = r
      simpa using hi r⁻¹ (K.inv_mem hr)
  let : IsInvariant N V U := commutatorAction_isInvariant_of_normalizing_actor N K le_rfl
  let : IsInvariant K V U := commutatorAction_isInvariant
  let : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let xi : N := ⟨x, Subgroup.le_normalizer (Subgroup.mem_zpowers x)⟩
  let ti : N := ⟨t, htN⟩
  let xk : K := ⟨x, Subgroup.mem_zpowers x⟩
  let φ := MulDistribMulAction.toMulAut N U
  let ψ := MulDistribMulAction.toMulAut K U
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro k hk
    have he : ψ k = 1 := hk
    have hfix : k ∈ fixingSubgroup K (Set.univ : Set U) := by
      rw [mem_fixingSubgroup_iff]
      intro v _
      exact congrArg (fun a : MulAut U => a v) he
    rw [support_action_faithful K hodd hfaith] at hfix
    exact hfix
  have hxaut : orderOf (φ xi) = 15 := by
    have he : φ xi = ψ xk := by ext v; rfl
    rw [he, orderOf_injective ψ hψinj]
    change orderOf xk = 15
    rw [← Subgroup.orderOf_coe xk]
    exact hx
  apply MulAut.not_inverts_order_fifteen_on_sixteen hcard (φ xi) (φ ti) hxaut
    (by rw [← map_pow, show ti ^ 2 = 1 from Subtype.ext ht.2, map_one])
  have hi : ti * xi * ti⁻¹ = xi⁻¹ := Subtype.ext hinv
  simpa only [map_mul, map_inv] using congrArg φ hi

/-- An involution of binary support rank at most two inverts only elements
of order three or five. This includes arbitrary odd composite orders. -/
public theorem invertedOddElement_order_three_or_five_of_small_involution_support
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hx : x ≠ 1) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) ≤ 4)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    orderOf x = 3 ∨ orderOf x = 5 := by
  have hd := invertedOddElement_order_dvd_fifteen x t hx hodd ht hinv hcard hfaith
  have hn1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  have hn15 : orderOf x ≠ 15 := by
    intro h15
    rcases invertedOddElement_support_card_four_or_sixteen
      x t hx hodd ht hinv hcard hfaith with h4 | h16
    · have h3 := invertedOddElement_order_three_of_support_card_four
        x t hx hodd ht hinv h4 hfaith
      omega
    · exact order_ne_fifteen_of_support_card_sixteen x t ht hinv h16 hfaith h15
  have hm : orderOf x ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hc : Nat.divisors 15 = {1, 3, 5, 15} := by decide
  rw [hc] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  tauto

/-- D.2.11(2), stated using cardinalities of the two binary supports. -/
public theorem invertedOddElement_order_three_or_five_of_involution_card_four
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hx : x ≠ 1) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 4)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    (orderOf x = 3 ∨ orderOf x = 5) ∧
      (orderOf x = 5 → Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16) := by
  refine ⟨invertedOddElement_order_three_or_five_of_small_involution_support
    x t hx hodd ht hinv hcard.le hfaith, ?_⟩
  intro h5
  rcases invertedOddElement_support_card_four_or_sixteen
    x t hx hodd ht hinv hcard.le hfaith with h4 | h16
  · have h3 := invertedOddElement_order_three_of_support_card_four
      x t hx hodd ht hinv h4 hfaith
    omega
  · exact h16

end CFSG.Quasithin.ChapterD
