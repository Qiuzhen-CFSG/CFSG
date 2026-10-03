module
public import Theory.Representation.CommutingCThreeCTwo
public import Theory.Representation.InvertedThreeCentralizer
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupTheory.CyclicThreeNormalizer

/-!
# The kernel of an elementary action normalizing C₃ on sixteen points

Let S be elementary abelian and normalize a subgroup F of order three. On
U=[V,F] of order sixteen, an involution a centralizing F has four fixed
points. Suppose I≤S has order four, contains a, and its other involutions
invert F. Then S has the same action image on U as I, this image has order
four, and C_U(S) has order two. The theorem expresses both the subgroup join
S=I C_S(U) and the exact kernel cardinality.

Coprime action gives the polynomial t²+t+1=0 for a generator t of F on U.
The inverted-three operator theorem classifies elements centralizing t,a,b;
normalizer conjugation reduces each S element to this case after multiplying
by b if necessary. The image of I has order dividing four and contains the
three distinct images of 1,a,b. Thus its order is four. Finally the proof
identifies the linear kernel and fixed vectors with their original ambient
subgroups, using the same normalizer action throughout.

Source: Stellmacher (1.6), journal p. 18, the step S=AᵢS₀ and its fixed
quotient calculation; see `refs/latex/stellmacher-n-group.tex`. No value of
m(S), minimality, or later exceptional classification is assumed here.
-/

open scoped IsMulCommutative

namespace Representation

universe u

private theorem elementaryAbelian_subgroup
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
    (IsMulCommutative.is_comm.comm (x : V) (y : V))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)

private theorem cardThree_commutator_quadratic
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (hFcard : Nat.card F = 3)
    (f : F) (hfgen : ∀ x : F, x ∈ Subgroup.zpowers f)
    (hf3 : f ^ 3 = 1)
    [IsInvariant F V (commutatorAction F V)]
    [IsElementaryAbelian 2 (commutatorAction F V)] :
    let t := Representation.ofElementaryAbelianAction
      (A := F) (G := commutatorAction F V) (p := 2) f
    t ^ 2 + t + 1 = 0 := by
  let U := commutatorAction F V
  let ρ := Representation.ofElementaryAbelianAction (A := F) (G := U) (p := 2)
  let t : Module.End (ZMod 2) (Additive U) := ρ f
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hFcard, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hcompl : IsCompl (FixedPoints.subgroup F V) U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F) (Group.isSolvable_of_comm fun x y =>
        (IsMulCommutative.is_comm (M := V)).comm x y) hcop inferInstance
  have hfix : FixedPoints.subgroup F U = ⊥ := by
    apply Subgroup.map_injective U.subtype_injective
    rw [fixedPoints_subgroup_map_subtype_eq_inf, Subgroup.map_bot]
    simpa only [inf_comm] using hcompl.inf_eq_bot
  have ht3 : t ^ 3 = 1 := by
    change (ρ f) ^ 3 = 1
    rw [← map_pow, hf3, map_one]
  have htinj : Function.Injective (t - 1 : Module.End (ZMod 2) (Additive U)) := by
    apply (injective_iff_map_eq_zero (t - 1).toAddMonoidHom).2
    intro w hw
    have htw : t w = w := sub_eq_zero.mp hw
    have hwf : f • Additive.toMul w = Additive.toMul w := by
      exact Additive.ofMul.injective htw
    have hwfix : Additive.toMul w ∈ FixedPoints.subgroup F U := by
      intro g
      obtain ⟨n, hn⟩ := hfgen g
      change f ^ n = g at hn
      have hfmem : f ∈ fixingSubgroup F ({Additive.toMul w} : Set U) := by
        rw [mem_fixingSubgroup_iff]
        intro x hx
        simpa only [Set.mem_singleton_iff.mp hx] using hwf
      have hpow := (fixingSubgroup F ({Additive.toMul w} : Set U)).zpow_mem hfmem n
      have hgf : g ∈ fixingSubgroup F ({Additive.toMul w} : Set U) := by
        rwa [hn] at hpow
      exact (mem_fixingSubgroup_iff (M := F) (s := ({Additive.toMul w} : Set U))).mp hgf
        _ (Set.mem_singleton _)
    have hone : Additive.toMul w = 1 := hfix.le hwfix
    exact Additive.toMul.injective hone
  have hfactor : (t - 1) * (t ^ 2 + t + 1) = 0 := by
    calc
      (t - 1) * (t ^ 2 + t + 1) =
          t * (t ^ 2 + t + 1) - (t ^ 2 + t + 1) := by rw [sub_mul, one_mul]
      _ = (t ^ 3 + t ^ 2 + t) - (t ^ 2 + t + 1) := by
        rw [mul_add, mul_add, mul_one, ← pow_succ']
        norm_num [pow_two]
      _ = t ^ 3 - 1 := by abel
      _ = 0 := by rw [ht3]; simp
  change t ^ 2 + t + 1 = 0
  apply LinearMap.ext
  intro w
  apply htinj
  have h := LinearMap.congr_fun hfactor w
  rw [Module.End.mul_apply, LinearMap.zero_apply] at h
  simpa only [LinearMap.zero_apply, map_zero] using h

private theorem normalizedThree_linear_image
    {S X : Type*} [Group S] [IsElementaryAbelian 2 S]
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) S X) (t : Module.End (ZMod 2) X)
    (a b : S) (ht : t ^ 2 + t + 1 = 0)
    (hbt : ρ b * t = t ^ 2 * ρ b) (hX : Nat.card X = 16)
    (hane : ρ a ≠ 1) (hat : ρ a * t = t * ρ a)
    (hcases : ∀ s : S, ρ s * t = t * ρ s ∨ ρ (s * b) * t = t * ρ (s * b)) :
    (∀ s : S, ∃ c : S, (c = 1 ∨ c = a ∨ c = b ∨ c = a * b) ∧ ρ s = ρ c) ∧
    Nat.card {x : X // ∀ s : S, ρ s x = x} = 2 := by
  have hsquare (s : S) : s * s = 1 := by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 S) s
    simpa only [pow_two] using h
  have hrhosq (s : S) : ρ s * ρ s = 1 := by rw [← map_mul, hsquare, map_one]
  have hcomm (s z : S) : ρ s * ρ z = ρ z * ρ s := by
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨hcentral, hfixed⟩ := invertedThree_cardSixteen_involution_centralizer
    t (ρ b) (ρ a) ht (hrhosq b) hbt hX (hrhosq a) hane hat (hcomm a b)
  have himage : ∀ s : S, ∃ c : S,
      (c = 1 ∨ c = a ∨ c = b ∨ c = a * b) ∧ ρ s = ρ c := by
    intro s
    rcases hcases s with h | h
    · rcases hcentral (ρ s) (hrhosq s) h (hcomm s b) (hcomm s a) with hs | hs
      · exact ⟨1, Or.inl rfl, by simpa only [map_one] using hs⟩
      · exact ⟨a, Or.inr (Or.inl rfl), hs⟩
    · have hsb : (s * b) * b = s := by rw [mul_assoc, hsquare, mul_one]
      rcases hcentral (ρ (s * b)) (hrhosq (s * b)) h
        (hcomm (s * b) b) (hcomm (s * b) a) with hs | hs
      · refine ⟨b, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
        calc
          ρ s = ρ (s * b) * ρ b := by rw [← map_mul, hsb]
          _ = ρ b := by rw [hs, one_mul]
      · refine ⟨a * b, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
        calc
          ρ s = ρ (s * b) * ρ b := by rw [← map_mul, hsb]
          _ = ρ (a * b) := by rw [hs, map_mul]
  refine ⟨himage, ?_⟩
  have hiff (x : X) : (∀ s : S, ρ s x = x) ↔ ρ a x = x ∧ ρ b x = x := by
    constructor
    · exact fun h => ⟨h a, h b⟩
    · rintro ⟨ha, hb⟩ s
      obtain ⟨c, hc, heq⟩ := himage s
      rw [heq]
      rcases hc with rfl | rfl | rfl | rfl
      · simp
      · exact ha
      · exact hb
      · rw [map_mul, Module.End.mul_apply, hb, ha]
  exact (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans hfixed

private theorem inverting_operator_not_commute
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (t b : Module.End (ZMod 2) X) (ht : t ^ 2 + t + 1 = 0)
    (hb : b * b = 1) (hbt : b * t = t ^ 2 * b)
    (hX : Nat.card X = 16) : b * t ≠ t * b := by
  intro hc
  have ht2 : t = t ^ 2 := by
    calc
      t = (t * b) * b := by rw [mul_assoc, hb, mul_one]
      _ = (t ^ 2 * b) * b := by rw [← hc, hbt]
      _ = t ^ 2 := by rw [mul_assoc, hb, mul_one]
  have htt : t + t = 0 := by
    have h := @two_smul (ZMod 2) (Module.End (ZMod 2) X) _ _ _ t
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, zero_smul] at h
    exact h.symm
  have hone : (1 : Module.End (ZMod 2) X) = 0 := by
    rw [← ht2, htt, zero_add] at ht
    exact ht
  have hxzero (x : X) : x = 0 := LinearMap.congr_fun hone x
  let _ : Subsingleton X := ⟨fun x y => (hxzero x).trans (hxzero y).symm⟩
  have hcard : Nat.card X = 1 := Nat.card_unique
  omega

public theorem normalizedCThree_cardSixteen_kernel_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F A I S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hAI : A ≤ I) (hIS : I ≤ S)
    (hSnorm : S ≤ Subgroup.normalizer (F : Set G))
    (hFcard : Nat.card F = 3) (hAcard : Nat.card A = 2) (hIcard : Nat.card I = 4)
    (hFA : ⁅F, A⁆ = ⊥)
    (hfull : ∀ b ∈ I, b ∉ A → ⁅F, Subgroup.zpowers b⁆ = F)
    (hUcard : Nat.card (commutatorAction F V) = 16)
    (hfixed : Nat.card (commutatorAction F V ⊓ FixedPoints.subgroup A V : Subgroup V) = 4) :
    S = I ⊔ (S ⊓ fixingSubgroup G (commutatorAction F V : Set V)) ∧
      Nat.card (commutatorAction F V ⊓ FixedPoints.subgroup S V : Subgroup V) = 2 ∧
      Nat.card S = 4 * Nat.card
        (S ⊓ fixingSubgroup G (commutatorAction F V : Set V) : Subgroup G) := by
  classical
  let U := commutatorAction F V
  let N := Subgroup.normalizer (F : Set G)
  let _ : IsElementaryAbelian 2 S := hS
  let _ : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let _ : IsInvariant N V U :=
    commutatorAction_isInvariant_of_normalizing_actor N F le_rfl
  let _ : IsInvariant F V U := commutatorAction_isInvariant
  let ρN : Representation (ZMod 2) N (Additive U) :=
    Representation.ofElementaryAbelianAction (A := N) (G := U) (p := 2)
  let j : S →* N := Subgroup.inclusion hSnorm
  let ρ : Representation (ZMod 2) S (Additive U) := ρN.comp j
  let _ : IsCyclic F := isCyclic_of_prime_card hFcard
  obtain ⟨f, hfgen⟩ := IsCyclic.exists_generator (α := F)
  have hforder : orderOf f = 3 :=
    (orderOf_eq_card_of_forall_mem_zpowers hfgen).trans hFcard
  have hfne : f ≠ 1 := by intro h; rw [h, orderOf_one] at hforder; omega
  have hfGne : (f : G) ≠ 1 := fun h => hfne (Subtype.ext h)
  have hf3 : f ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hforder])
  let fN : N := ⟨f, F.le_normalizer f.property⟩
  let t : Module.End (ZMod 2) (Additive U) := ρN fN
  have ht : t ^ 2 + t + 1 = 0 := by
    exact cardThree_commutator_quadratic F hFcard f hfgen hf3
  obtain ⟨a, hane, hauniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
  let aS : S := ⟨a, hIS (hAI a.property)⟩
  have hInot : ¬ I ≤ A := by
    intro h
    have h := Subgroup.card_le_of_le h
    rw [hIcard, hAcard] at h
    omega
  obtain ⟨b, hbI, hbA⟩ := SetLike.not_le_iff_exists.mp hInot
  let bS : S := ⟨b, hIS hbI⟩
  have hbne : b ≠ 1 := by intro h; exact hbA (h ▸ A.one_mem)
  have hsquare (s : S) : s * s = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 S) s
  have hb2 : b ^ 2 = 1 := by
    exact congrArg Subtype.val (show bS ^ 2 = 1 by simpa only [pow_two] using hsquare bS)
  have hBcard : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hb2 hbne
  have hBnorm : Subgroup.zpowers b ≤ N := Subgroup.zpowers_le.mpr (hSnorm (hIS hbI))
  have hbinv : b * (f : G) * b⁻¹ = (f : G)⁻¹ :=
    Subgroup.cyclicThree_full_commutator_inverts F (Subgroup.zpowers b) hFcard hBcard
      hBnorm (hfull b hbI hbA) f b f.property hfGne (Subgroup.mem_zpowers b) hbne
  have hfG3 : (f : G) ^ 3 = 1 := congrArg Subtype.val hf3
  have hfG2 : (f : G) ^ 2 = (f : G)⁻¹ := by
    have h := congrArg (fun z : G => z * (f : G)⁻¹) hfG3
    simpa [pow_succ, mul_assoc] using h
  have hbN : j bS * fN = fN ^ 2 * j bS := by
    apply Subtype.ext
    change b * (f : G) = (f : G) ^ 2 * b
    rw [hfG2]
    have h := congrArg (fun z : G => z * b) hbinv
    simpa [mul_assoc] using h
  have hbt : ρ bS * t = t ^ 2 * ρ bS := by
    change ρN (j bS) * ρN fN = (ρN fN) ^ 2 * ρN (j bS)
    rw [← map_pow, ← map_mul, ← map_mul, hbN]
  have haF : (a : G) * (f : G) = (f : G) * (a : G) :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hFA f.property) a a.property
  have hat : ρ aS * t = t * ρ aS := by
    change ρN (j aS) * ρN fN = ρN fN * ρN (j aS)
    rw [← map_mul, ← map_mul]
    apply congrArg ρN
    exact Subtype.ext haF
  have hrhoane : ρ aS ≠ 1 := by
    intro h
    have hUa : ∀ u : U, (a : G) • (u : V) = u := by
      intro u
      have hu := LinearMap.congr_fun h (Additive.ofMul u)
      exact congrArg (fun x : Additive U => ((Additive.toMul x : U) : V)) hu
    have hUfixed : U ≤ FixedPoints.subgroup A V := by
      intro u hu x
      by_cases hx : x = 1
      · simp [hx]
      · have hxa : x = a := (hauniq x hx).trans (hauniq a hane).symm
        subst x
        exact hUa ⟨u, hu⟩
    have heq : U ⊓ FixedPoints.subgroup A V = U := inf_eq_left.mpr hUfixed
    change Nat.card (U ⊓ FixedPoints.subgroup A V : Subgroup V) = 4 at hfixed
    rw [heq] at hfixed
    change Nat.card U = 16 at hUcard
    omega
  have hcases : ∀ s : S, ρ s * t = t * ρ s ∨
      ρ (s * bS) * t = t * ρ (s * bS) := by
    intro s
    rcases Subgroup.cyclicThree_normalizer_conjugates F hFcard f f.property hfGne
      s (hSnorm s.property) with hs | hs
    · left
      have hsN : j s * fN = fN * j s := by
        apply Subtype.ext
        have hh := congrArg (fun z : G => z * (s : G)) hs
        simpa [j, fN, mul_assoc] using hh
      change ρN (j s) * ρN fN = ρN fN * ρN (j s)
      rw [← map_mul, ← map_mul, hsN]
    · right
      have hsb : ((s : G) * b) * (f : G) * ((s : G) * b)⁻¹ = f := by
        calc
          ((s : G) * b) * (f : G) * ((s : G) * b)⁻¹ =
              (s : G) * (b * (f : G) * b⁻¹) * (s : G)⁻¹ := by group
          _ = (s : G) * (f : G)⁻¹ * (s : G)⁻¹ := by rw [hbinv]
          _ = ((s : G) * (f : G) * (s : G)⁻¹)⁻¹ := by group
          _ = f := by rw [hs, inv_inv]
      have hsN : j (s * bS) * fN = fN * j (s * bS) := by
        apply Subtype.ext
        have hh := congrArg (fun z : G => z * ((s : G) * b)) hsb
        simpa [j, fN, bS, mul_assoc] using hh
      change ρN (j (s * bS)) * ρN fN = ρN fN * ρN (j (s * bS))
      rw [← map_mul, ← map_mul, hsN]
  have hXcard : Nat.card (Additive U) = 16 :=
    (Nat.card_congr Additive.toMul).trans hUcard
  obtain ⟨himage, hfix⟩ := normalizedThree_linear_image ρ t aS bS ht hbt hXcard hrhoane hat hcases
  have hcb (c : S) (hc : c = 1 ∨ c = aS ∨ c = bS ∨ c = aS * bS) : (c : G) ∈ I := by
    rcases hc with rfl | rfl | rfl | rfl
    · exact I.one_mem
    · exact hAI a.property
    · exact hbI
    · exact I.mul_mem (hAI a.property) hbI
  have hindex : Nat.card S = 4 * Nat.card
      (S ⊓ fixingSubgroup G (commutatorAction F V : Set V) : Subgroup G) := by
    let φ := ρ.asGroupHom
    let φI := φ.comp (Subgroup.inclusion hIS)
    have hrange : φ.range = φI.range := by
      apply le_antisymm
      · rintro z ⟨s, rfl⟩
        obtain ⟨c, hc, heq⟩ := himage s
        refine ⟨⟨c, hcb c hc⟩, ?_⟩
        apply Units.ext
        exact heq.symm
      · rintro z ⟨c, rfl⟩
        exact ⟨Subgroup.inclusion hIS c, rfl⟩
    have hdiv : Nat.card φ.range ∣ 4 := by
      rw [hrange, ← hIcard]
      exact Subgroup.card_range_dvd φI
    have hφane : φ aS ≠ 1 := fun h => hrhoane (congrArg Units.val h)
    have hbnot : ρ bS * t ≠ t * ρ bS :=
      inverting_operator_not_commute t (ρ bS) ht
        (by rw [← map_mul, hsquare, map_one]) hbt hXcard
    have hφbne : φ bS ≠ 1 := by
      intro h
      have hb1 : ρ bS = 1 := congrArg Units.val h
      exact hbnot (by rw [hb1, one_mul, mul_one])
    have hφab : φ aS ≠ φ bS := by
      intro h
      have hab : ρ aS = ρ bS := congrArg Units.val h
      exact hbnot (by rw [← hab]; exact hat)
    let _ : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    let _ : Fintype φ.range := Fintype.ofFinite _
    have hgt : 2 < Nat.card φ.range := by
      rw [Nat.card_eq_fintype_card]
      apply Fintype.two_lt_card_iff.mpr
      refine ⟨1, ⟨φ aS, ⟨aS, rfl⟩⟩, ⟨φ bS, ⟨bS, rfl⟩⟩, ?_, ?_, ?_⟩
      · intro h
        exact hφane (congrArg Subtype.val h).symm
      · intro h
        exact hφbne (congrArg Subtype.val h).symm
      · intro h
        exact hφab (congrArg Subtype.val h)
    have hle : Nat.card φ.range ≤ 4 := Nat.le_of_dvd (by decide) hdiv
    have hrangecard : Nat.card φ.range = 4 := by
      have hcases : Nat.card φ.range = 3 ∨ Nat.card φ.range = 4 := by omega
      rcases hcases with h | h
      · rw [h] at hdiv
        norm_num at hdiv
      · exact h
    have hkerMap : φ.ker.map S.subtype =
        S ⊓ fixingSubgroup G (U : Set V) := by
      ext g
      constructor
      · rintro ⟨s, hs, rfl⟩
        refine ⟨s.property, ?_⟩
        change (s : G) ∈ fixingSubgroup G (U : Set V)
        rw [mem_fixingSubgroup_iff]
        intro v hv
        have hlin : ρ s = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hs)
        exact congrArg (fun x : Additive U => ((Additive.toMul x : U) : V))
          (LinearMap.congr_fun hlin (Additive.ofMul ⟨v, hv⟩))
      · rintro ⟨hgS, hgfix⟩
        refine ⟨⟨g, hgS⟩, ?_, rfl⟩
        change φ ⟨g, hgS⟩ = 1
        apply Units.ext
        apply LinearMap.ext
        intro u
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (mem_fixingSubgroup_iff (M := G) (s := (U : Set V))).mp hgfix
          ((Additive.toMul u : U) : V) (Additive.toMul u).property
    calc
      Nat.card S = Nat.card φ.ker * φ.ker.index := φ.ker.card_mul_index.symm
      _ = Nat.card φ.ker * 4 := by rw [Subgroup.index_ker, hrangecard]
      _ = 4 * Nat.card (S ⊓ fixingSubgroup G (U : Set V) : Subgroup G) := by
        rw [← hkerMap, Subgroup.card_map_of_injective S.subtype_injective, Nat.mul_comm]
  refine ⟨?_, ?_, hindex⟩
  · apply le_antisymm
    · intro s hs
      obtain ⟨c, hc, heq⟩ := himage ⟨s, hs⟩
      have hcI : (c : G) ∈ I := hcb c hc
      have hact (u : U) : s • (u : V) = (c : G) • (u : V) := by
        exact congrArg (fun x : Additive U => ((Additive.toMul x : U) : V))
          (LinearMap.congr_fun heq (Additive.ofMul u))
      have hk : (c : G)⁻¹ * s ∈
          S ⊓ fixingSubgroup G (commutatorAction F V : Set V) := by
        refine ⟨S.mul_mem (S.inv_mem c.property) hs, ?_⟩
        change (c : G)⁻¹ * s ∈ fixingSubgroup G (U : Set V)
        rw [mem_fixingSubgroup_iff]
        intro v hv
        rw [mul_smul, hact ⟨v, hv⟩, inv_smul_smul]
      have hmem := (I ⊔ (S ⊓ fixingSubgroup G (commutatorAction F V : Set V))).mul_mem
        (show (c : G) ∈ I ⊔ (S ⊓ fixingSubgroup G (commutatorAction F V : Set V)) from
          (le_sup_left : I ≤ I ⊔ (S ⊓ fixingSubgroup G (U : Set V))) hcI)
        (show (c : G)⁻¹ * s ∈ I ⊔ (S ⊓ fixingSubgroup G (commutatorAction F V : Set V)) from
          (le_sup_right : S ⊓ fixingSubgroup G (U : Set V) ≤
            I ⊔ (S ⊓ fixingSubgroup G (U : Set V))) hk)
      simpa only [mul_inv_cancel_left] using hmem
    · exact sup_le hIS inf_le_left
  · let e : ↥(U ⊓ FixedPoints.subgroup S V : Subgroup V) ≃
        {x : Additive U // ∀ s : S, ρ s x = x} :=
      { toFun := fun x => ⟨Additive.ofMul ⟨x, x.property.1⟩, by
          intro s
          apply Additive.toMul.injective
          apply Subtype.ext
          exact x.property.2 s⟩
        invFun := fun x => ⟨((Additive.toMul x.val : U) : V),
          ⟨(Additive.toMul x.val).property, fun s =>
            congrArg (fun w : Additive U => ((Additive.toMul w : U) : V)) (x.property s)⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact (Nat.card_congr e).trans hfix

/-- A generator of an order-three actor satisfies its nontrivial cyclotomic
polynomial on the action-commutator module. -/
public theorem cardThree_commutatorAction_generator_quadratic
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (hFcard : Nat.card F = 3)
    (f : F) (hfgen : ∀ x : F, x ∈ Subgroup.zpowers f)
    (hf3 : f ^ 3 = 1)
    [IsInvariant F V (commutatorAction F V)]
    [IsElementaryAbelian 2 (commutatorAction F V)] :
    let t := Representation.ofElementaryAbelianAction
      (A := F) (G := commutatorAction F V) (p := 2) f
    t ^ 2 + t + 1 = 0 :=
  cardThree_commutator_quadratic F hFcard f hfgen hf3

end Representation
