module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanAction
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms
public import Theory.Representation.BinaryPrimeDegree
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.OrthogonalRoots

/-!
# The solvable Suzuki endpoint in a binary hexagon

In the actual small Suzuki actor, two distinct involutions have a product
of order five, and every nontrivial normal subgroup contains this product.
Choose one involution in the canonical simple root and the other as an
actual source reflection. Coprime Frattini faithfulness therefore detects
the product on the literal effective section, giving binary degree at
least four without simplicity or perfectness.

The source three-core T = Z(O₃(H)) centralizes every small Suzuki root:
all automorphisms of Sz(2) are inner and have order dividing twenty.
For a linear opposite endpoint, (1J) supplies its Cartan cubic, so T has
no nonidentity fixed point on any opposite root. Thus C(T) intersect U_sj
is exactly U_j^(s_i) U_j^(s_i s_j), with Frattini index at most four.
The odd product moves this SAME centralizer section: the reflection sends
the first factor into the conjugate radical V_j^(s_i), disjoint from that
factor, while its simple-root partner belongs to that conjugate radical.
The lower bound sixteen contradicts the upper bound four.

Together with the regular Suzuki proof this excludes every Suzuki
parameter opposite a linear endpoint under the source square profile.
The existing two-layer bound also excludes regular Suzuki opposite any
order-four root. The CFSG companion supplies original and geometric
applications, including the dihedral original quotient whose actual
root actor is Sz(2). Suzuki/Suzuki with two regular endpoints or two
small endpoints, remaining unitary rows and exhaustive assembly remain.

Source: Fong--Seitz I (3G), (5D)(b), (5H), printed pp.14--16,26--27,29--30;
(6C), printed pp.39--41. All right-conjugation words and actions are in
the same marked finite quotient. No whole-panel model is assumed.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped MatrixGroups Pointwise IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource GTwoSource

set_option synthInstance.maxSize 512 in
private theorem smallSuzuki_distinct_involutions (x y : SuzukiMatrixGroup 0)
    (hx : x^2 = 1) (hy : y^2 = 1) (hxn : x ≠ 1) (hyn : y ≠ 1) (hne : x ≠ y) : (x*y)^5 = 1 := by
  let e := FiveFour.suzukiZeroEquiv.symm
  have hf : ∀ a b : FiveFour.Group, a^2 = 1 → b^2 = 1 → a ≠ 1 → b ≠ 1 →
      a ≠ b → (a*b)^5 = 1 := by decide +kernel
  apply e.injective
  simpa only [map_pow,map_mul,map_one] using hf (e x) (e y)
    (by rw [← map_pow,hx,map_one]) (by rw [← map_pow,hy,map_one])
    (e.map_ne_one_iff.mpr hxn) (e.map_ne_one_iff.mpr hyn) (fun h => hne (e.injective h))

private theorem fiveFour_normal_contains_five (N : Subgroup FiveFour.Group) [N.Normal]
    (hne : N ≠ ⊥) (c : FiveFour.Group) (hc : c^5 = 1) : c ∈ N := by
  have hd : Nat.card N ∣ 20 := FiveFour.card ▸ N.card_subgroup_dvd_card
  have hn1 : Nat.card N ≠ 1 := fun h => hne (card_eq_one.mp h)
  have hn2 (n : ℕ) : Nat.card N ≠ 2^n := by
    intro h
    have htwo : IsPGroup 2 N := IsPGroup.of_card h
    have hle : N ≤ pCore 2 FiveFour.Group := le_sSup ⟨inferInstance,htwo⟩
    rw [FiveFour.twoCore_eq_bot] at hle
    exact hne (bot_unique hle)
  have hb := Nat.le_of_dvd (by decide : 0 < 20) hd
  have h2 := hn2 1
  have h4 := hn2 2
  have hn : Nat.card N = 5 ∨ Nat.card N = 10 ∨ Nat.card N = 20 := by
    interval_cases hk : Nat.card N <;> omega
  have hi : N.index ∣ 4 := by
    have he := N.index_mul_card
    rw [FiveFour.card] at he
    rcases hn with hn | hn | hn <;> rw [hn] at he
    · have : N.index = 4 := by omega
      simp [this]
    · have : N.index = 2 := by omega
      simp [this]
    · have : N.index = 1 := by omega
      simp [this]
  apply (QuotientGroup.eq_one_iff c).mp
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 4 5)
  · exact (orderOf_dvd_natCard (QuotientGroup.mk' N c)).trans hi
  · exact orderOf_dvd_of_pow_eq_one (by
      change (QuotientGroup.mk' N c)^5 = 1
      rw [← map_pow,hc,map_one])

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Two literal involutions yield an order-five product in the small actor. -/
theorem smallSuzuki_exists_oddProduct (j : Fin 2)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) :
    ∃ s : RootReflection Q split j, ∃ u : rankOne Q split j,
      (u : X ⧸ Q.D) ∈ simpleRoot Q split j ∧
        orderOf ((⟨s.val,s.mem_rankOne⟩ : rankOne Q split j)*u) = 5 := by
  have hc : Nat.card (simpleRoot Q split j) = 4 := by
    rw [Nat.card_congr ν.toEquiv,matrixRoot_card]
    norm_num
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := simpleRoot Q split j) 2 (by rw [hc]; decide)
  let s := involutoryRootReflection Q split j (UnitarySource.actorReflection Q split j)
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  let v : rankOne Q split j := ⟨u,(show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left) u.property⟩
  have hs2 : r^2 = 1 := Subtype.ext
    (involutoryRootReflection_sq Q split j (UnitarySource.actorReflection Q split j))
  have hsne : r ≠ 1 := fun he => involutoryRootReflection_ne_one Q split j
    (UnitarySource.actorReflection Q split j) (congrArg Subtype.val he)
  have hv2 : v^2 = 1 := Subtype.ext (congrArg (fun z : simpleRoot Q split j => (z : X ⧸ Q.D))
    (show u^2 = 1 from hu ▸ pow_orderOf_eq_one u))
  have hvne : v ≠ 1 := by
    intro he
    have hue : u = 1 := Subtype.ext (congrArg (fun z : rankOne Q split j => (z : X ⧸ Q.D)) he)
    rw [hue,orderOf_one] at hu
    omega
  have hne : r ≠ v := by
    intro he
    exact Q.tits.representative_not_mem_B (Q.simple_mem j) s.val s.class_eq
      (by rw [show (s.val : X ⧸ Q.D) = (u : X ⧸ Q.D) from congrArg Subtype.val he]
          exact split.U_le (simpleRoot_le Q split j u.property))
  refine ⟨s,v,u.property,?_⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply μ.injective
    simpa only [map_pow,map_mul,map_one] using smallSuzuki_distinct_involutions (μ r) (μ v)
      (by rw [←map_pow,hs2,map_one]) (by rw [←map_pow,hv2,map_one])
      (μ.map_ne_one_iff.mpr hsne) (μ.map_ne_one_iff.mpr hvne) (fun h => hne (μ.injective h))
  · intro he
    have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hv2)
    exact hne ((mul_eq_one_iff_eq_inv.mp he).trans hv)

/-- The small actor's actual effective kernel cannot contain an order-five
product that moves the section. This uses its normal subgroup structure. -/
theorem smallSuzuki_section_injective (j : Fin 2)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (c : rankOne Q split j) (hc : orderOf c = 5)
    (d : RootSection Q split j) (hmove : d.action c ≠ 1) :
    Function.Injective d.effectiveAction := by
  apply d.effectiveAction.ker_eq_bot_iff.mp
  by_contra hn
  let e := μ.trans FiveFour.suzukiZeroEquiv.symm
  let N := d.effectiveAction.ker.comap e.symm.toMonoidHom
  have hN : N ≠ ⊥ := by
    intro hz
    have he := congrArg (Subgroup.map e.symm.toMonoidHom) hz
    rw [map_comap_eq_self_of_surjective e.symm.surjective,Subgroup.map_bot] at he
    exact hn he
  have hmem := fiveFour_normal_contains_five N hN (e c) (by
    rw [←map_pow,show c^5 = 1 from hc ▸ pow_orderOf_eq_one c,map_one])
  have hker : d.effectiveAction c = 1 := by
    change e.symm (e c) ∈ d.effectiveAction.ker at hmem
    rw [e.symm_apply_apply] at hmem
    exact hmem
  exact hmove (d.action_eq_one_of_odd c (by rw [hc]; decide) hker)

/-- The degree-four bound is on the literal effective section. -/
theorem smallSuzuki_section_card_bound (j : Fin 2)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (c : rankOne Q split j) (hc : orderOf c = 5)
    (d : RootSection Q split j) (hmove : d.action c ≠ 1) :
    16 ≤ Nat.card d.EffectiveCarrier := by
  have hf := d.effectiveRepresentation_injective
    (smallSuzuki_section_injective Q split j μ c hc d hmove)
  have hd := Representation.BinaryPrimeDegree.orderOf_le_finrank
    (V := Additive d.EffectiveCarrier) d.effectiveRepresentation hf
    (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
    (by rw [Nat.card_congr μ.toEquiv,suzukiZero_card]; decide)
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_five] at hd
  have he : Nat.card d.EffectiveCarrier =
      2^Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    change Nat.card (Additive d.EffectiveCarrier) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier))
  rw [he]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hd

/-- The full three-core centralizes the actual small Suzuki actor: all its
automorphisms are inner, and their orders divide twenty. -/
theorem threeCartan_centralizes_smallSuzuki_rankOne (j : Fin 2)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0) :
    threeCartan Q ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)) := by
  let H := Q.tits.B ⊓ Q.tits.N
  let R := rankOne Q split j
  let e := μ.trans FiveFour.suzukiZeroEquiv.symm
  let ρR : H →* MulAut R := RootAction.action H R (rankOne_torus_normalizes Q split j)
  let ρ : H →* MulAut FiveFour.Group := (MulAut.congr e).toMonoidHom.comp ρR
  rw [threeCartan_eq_core_image Q split]
  rintro _ ⟨t,ht,rfl⟩
  obtain ⟨k,hk⟩ := pCore_isPGroup (⟨t,ht⟩ : pCore 3 H)
  have hpow : (ρ t)^(3^k) = 1 := by
    rw [←map_pow,show t^(3^k) = 1 from congrArg Subtype.val hk,map_one]
  obtain ⟨g,hg⟩ := FiveFour.automorphism_inner (ρ t)
  have hd : orderOf (ρ t) ∣ 20 := by
    rw [hg]
    exact (orderOf_map_dvd MulAut.conj g).trans (FiveFour.card ▸ orderOf_dvd_natCard g)
  have hone : ρ t = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 20 3).pow_right k) hd
      (orderOf_dvd_of_pow_eq_one hpow))
  have htR : ρR t = 1 := by
    apply (MulAut.congr e).injective
    exact hone.trans (map_one _).symm
  rw [mem_centralizer_iff]
  intro x hx
  have hh := congrArg (fun a : MulAut R => (a ⟨x,hx⟩ : X ⧸ Q.D)) htR
  change (t : X ⧸ Q.D)*x*(t : X ⧸ Q.D)⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The same source three-core centralizes all six small Suzuki roots. -/
theorem threeCartan_centralizes_smallSuzuki_roots (j : Fin 2)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0) (w : Weyl Q) :
    rootAt Q split j w ≤ centralizer (threeCartan Q : Set (X ⧸ Q.D)) := by
  have hC := le_centralizer_iff.mp (threeCartan_centralizes_smallSuzuki_rankOne Q split j μ)
  have hU : simpleRoot Q split j ≤ centralizer (threeCartan Q : Set (X ⧸ Q.D)) :=
    le_sup_left.trans hC
  let n := representative w
  have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hU
  change rootAt Q split j w ≤ rightConjugate (centralizer (threeCartan Q : Set (X ⧸ Q.D))) (n : X ⧸ Q.D) at hh
  rwa [rightConjugate_eq_self _ (normalizer_le_normalizer_centralizer _
    (threeCartan_normalized Q split n.property))] at hh

/-- A nontrivial square in the order-four root bounds its Frattini index by two. -/
theorem smallSuzuki_root_frattini_bound (j : Fin 2)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) :
    Nat.card (simpleRoot Q split j ⧸ frattini (simpleRoot Q split j)) ≤ 2 := by
  let A := simpleRoot Q split j
  let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split j)⟩
  obtain ⟨a,ha⟩ := suzuki_root_exists_nontrivial_square 0
  have hnon : frattini A ≠ ⊥ := by
    intro hz
    have hmem := pth_power_mem_frattini_of_isPGroup (p := 2) (ν.symm a)
    rw [hz,mem_bot] at hmem
    have hh := congrArg ν hmem
    rw [map_pow,ν.apply_symm_apply,map_one] at hh
    exact ha hh
  have hPhi := (frattini A).one_lt_card_iff_ne_bot.mpr hnon
  have hc : Nat.card A = 4 := by
    rw [Nat.card_congr ν.toEquiv,matrixRoot_card]
    norm_num
  have he := (frattini A).index_mul_card
  rw [hc] at he
  change (frattini A).index ≤ 2
  nlinarith

/-- The own-root version of (3G). The product of a reflection and any
simple-root element moves the actual two-root centralizer section. -/
theorem centralizerSection_oddProduct_moves (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (u : rankOne Q split j) (hu : (u : X ⧸ Q.D) ∈ simpleRoot Q split j)
    (T : Subgroup (X ⧸ Q.D))
    (hTR : T ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)))
    (hfix : rootAt Q split j (Q.simple i) ≤ centralizer (T : Set (X ⧸ Q.D))) :
    (centralizerSection Q split j hKj T hTR).action
      ((⟨s.val,s.mem_rankOne⟩ : rankOne Q split j)*u) ≠ 1 := by
  let d := centralizerSection Q split j hKj T hTR
  let n := representative (Q.simple i)
  let W := rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D)
  have hB : rootAt Q split j (Q.simple i) ≤ simpleRemainder Q split j :=
    (le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij)
  have hD : rootAt Q split j (Q.simple i*Q.simple j) ≤ simpleRemainder Q split j :=
    le_sup_right.trans (middleRoots_le_remainder Q split hm i j hij)
  have hUW : simpleRoot Q split j ≤ W := by
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hB
    change rightConjugate (rootAt Q split j (Q.simple i)) (n : X ⧸ Q.D) ≤ W at hh
    rw [rootAt_right Q split j _ _ n (representative_spec _),
      show Q.simple i*Q.simple i = 1 from by
        simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2,
      rootAt_one] at hh
    exact hh
  have hDW : rootAt Q split j (Q.simple i*Q.simple j) ≤ W := by
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hD
    change rightConjugate (rootAt Q split j (Q.simple i*Q.simple j)) (n : X ⧸ Q.D) ≤ W at hh
    rwa [rootAt_right Q split j _ _ n (representative_spec _),
      orthogonal_root_stabilizer Q split hm j i hij.symm] at hh
  intro he
  let c : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩*u
  have hei : d.action c⁻¹ = 1 := by rw [map_inv,he,inv_one]
  apply rootAt_ne_bot Q split j (Q.simple i)
  apply eq_bot_iff.mpr
  intro a ha
  let x : d.numerator := ⟨a,hB ha,hfix ha⟩
  let y := d.numeratorAction c⁻¹ x
  have hyx : y = x := by
    have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x)) hei
    rw [d.action_mk] at hh
    exact congrArg QuotientGroup.quotientBot hh
  have hy : (y : X ⧸ Q.D) =
      (u : X ⧸ Q.D)⁻¹*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*u := by
    dsimp only [y]
    rw [d.numeratorAction_apply]
    simp only [c,coe_inv,coe_mul,mul_inv_rev,inv_inv,mul_assoc]
    rfl
  have hsa : (s.val : X ⧸ Q.D)⁻¹*a*s.val ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [← rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*(s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
  have haW : a ∈ W := by
    have hyW : (y : X ⧸ Q.D) ∈ W := by
      rw [hy]
      exact W.mul_mem (W.mul_mem (W.inv_mem (hUW hu)) (hDW hsa)) (hUW hu)
    simpa only [hyx] using hyW
  have haU : (n : X ⧸ Q.D)*a*(n : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j := by
    rw [rootAt_eq Q split j (Q.simple i) n (representative_spec _)] at ha
    exact ha
  have hz : (n : X ⧸ Q.D)*a*(n : X ⧸ Q.D)⁻¹ = 1 :=
    disjoint_def.mp (simpleRoot_disjoint_remainder Q split j) haU haW
  exact mem_bot.mpr ((MulAut.conj (n : X ⧸ Q.D)).injective (hz.trans (map_one _).symm))

/-- The small Suzuki centralizer has incompatible bounds sixteen and four.
Both bounds refer to the same literal section and the constructed odd product. -/
theorem no_smallSuzuki_centralizer_section (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0)
    (T : Subgroup (X ⧸ Q.D)) (hTH : T ≤ Q.tits.B ⊓ Q.tits.N)
    (hfree : ∀ w, rootAt Q split i w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hfix : ∀ w, rootAt Q split j w ≤ centralizer (T : Set (X ⧸ Q.D))) : False := by
  have hTR : T ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · simpa only [rootAt_one] using hfix 1
    · exact hfix (Q.simple j)
  let d := centralizerSection Q split j hKj T hTR
  obtain ⟨s,u,hu,ho⟩ := smallSuzuki_exists_oddProduct Q split j μ ν
  have hlo := smallSuzuki_section_card_bound Q split j μ _ ho d
    (centralizerSection_oddProduct_moves Q split hm i j hij s hKj u hu T hTR (hfix _))
  have he : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  change 16 ≤ d.effectiveDenominator.index at hlo
  rw [he] at hlo
  have hup := centralizerSection_frattini_bound Q split hm i j hij T hTH hfree hfix
  have hroot := smallSuzuki_root_frattini_bound Q split j ν
  have hfour : Nat.card (d.numerator ⧸ frattini d.numerator) ≤ 4 :=
    hup.trans (Nat.pow_le_pow_left hroot 2)
  change Nat.card (d.numerator ⧸ frattini d.numerator) ≥ 16 at hlo
  omega

/-- The missing solvable Suzuki row in the mixed linear exclusion. The
source square profile supplies the nontrivial cubic in the linear Cartan. -/
theorem no_mixed_smallSuzuki_of_square_profile
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup 0)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  no_smallSuzuki_centralizer_section Q split hhex i j hij hKj μj νj
    (threeCartan Q) (threeCartan_le_cartan Q)
    (linear_threeCartan_nontrivial_fixedFree Q split i hKi μi
      (UnitarySource.actorReflection Q split i)
      (linear_cubic_of_suzuki_square_profile Q split i j hKi μi νj hsquare)).2
    (threeCartan_centralizes_smallSuzuki_roots Q split j μj)

/-- Every Suzuki parameter is excluded opposite a linear endpoint under
(1J), retaining Sz(2) and binary linear inputs. -/
theorem no_mixed_suzuki_all_of_square_profile
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    {m : ℕ} (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  by_cases hm : m = 0
  · subst m
    exact no_mixed_smallSuzuki_of_square_profile Q split hhex i j hij hKi hKj μi μj νj hsquare
  · exact no_mixed_suzuki_of_square_profile Q split hhex i j hij hKi hKj μi
      (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
      (Nat.pos_of_ne_zero hm) μj νj hsquare

/-- A regular Suzuki endpoint cannot be opposite any order-four root,
in particular Sz(2) or the original dihedral alternative. -/
theorem no_regular_suzuki_opposite_four (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m) (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hi : Nat.card (simpleRoot Q split i) = 4) : False := by
  have hb := suzuki_hexagon_parameter_bound Q split j hm μj hhex i hij
    (UnitarySource.actorReflection Q split j) hKj νj (a := 2) hi
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
