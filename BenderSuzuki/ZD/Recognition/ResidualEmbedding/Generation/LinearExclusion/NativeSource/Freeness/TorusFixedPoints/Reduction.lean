module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.RegularityContracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.OddNormalizer
public import BenderSuzuki.SE.Proposition53
public import Theory.GroupAction.PrimeOrderConjugation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree

/-!
# Prime reduction and the rank-one normalizer action

For a prime-order element of the actual residual torus, Section 3 constructs
an invariant Sylow subgroup of the pair stabilizer containing that element.
The ambient Sylow promotion and the weak-closure assertion (12H) remain
separate inputs to the final action argument below.

Once weak closure in an ambient Sylow subgroup lying in the pair stabilizer
is available, double transitivity and Sylow conjugacy supply a distinguished
normalizing involution interchanging any two fixed cosets. Lemma 12.12 gives
rank one for the distinguished closure of the normalizer. Its swapping
involution acts without fixed points, so the fixed set has even size. The
proved rank-one permutation theorem makes its size two. Prime-order
extraction then yields the literal torus semiregularity conclusion.

These are conditional endpoint theorems, not an assertion of (12H) or of
the unconditional Proposition 12.13. They use the actual quotient action,
right conjugation and the ambient Sylow subgroup throughout.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Proposition 12.13, lines 2290–2320;
the permutation consequence [II_1; 2.8] is proved in `SE.Proposition53`.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

private theorem pair_eq_stabilizers :
    residualPairStabilizer M t =
      MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
        MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ M) := by
  rw [baseCoset_stabilizer, conjugateCoset_stabilizer,
    (d.minimal.disconnected.involutions t d.t_mem).inv_eq_self]
  rfl

private theorem base_ne_translate :
    (QuotientGroup.mk 1 : G ⧸ M) ≠ QuotientGroup.mk t := by
  intro he
  exact d.t_not_mem_M (by simpa using (QuotientGroup.eq.mp he))

private theorem torus_fixes_pair {x : G} (hx : x ∈ residualCommutator M t) :
    x • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 ∧
      x • (QuotientGroup.mk t : G ⧸ M) = QuotientGroup.mk t := by
  have hD := (d.torus_structure.1 ▸ hx).1
  rw [pair_eq_stabilizers d] at hD
  exact hD

private theorem torus_normalizer_data {x : G}
    (hx : x ∈ residualCommutator M t) (hxne : x ≠ 1) :
    t ∈ normalizer (zpowers x : Set G) ∧
      t ∉ centralizer (zpowers x : Set G) := by
  have ht := d.minimal.disconnected.involutions t d.t_mem
  refine ⟨theorem4b_mem_normalizer_zpowers_of_inverts ht ?_, ?_⟩
  · simpa only [rightConjugateElem, ht.inv_eq_self] using d.torus_structure.2.2.2 x hx
  · intro hc
    have htC : t ∈ centralizerClosure Z x := subset_closure
      ⟨d.t_mem, mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hc x (mem_zpowers x)).symm)⟩
    rw [d.torus_centralizerClosure_eq_bot hx hxne] at htC
    exact ht.ne_one htC

/-- A weakly closed prime torus line lets its normalizer interchange any two fixed cosets. -/
public theorem Context.torus_normalizer_swap_of_weakClosure
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (P : Sylow p G)
    (hPD : (P : Subgroup G) ≤ residualPairStabilizer M t)
    (hweak : ∀ g : G, rightConjugateElem x g ∈ (P : Subgroup G) →
      g ∈ normalizer (zpowers x : Set G))
    {a b : G ⧸ M} (hab : a ≠ b) (hxa : x • a = a) (hxb : x • b = b) :
    ∃ s ∈ Z, s ∈ normalizer (zpowers x : Set G) ∧ s • a = b := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hga, hgb⟩ := (MulAction.is_two_pretransitive_iff.mp d.action.two_transitive)
    hab (base_ne_translate d)
  let D := residualPairStabilizer M t
  let y := MulAut.conj g x
  have hyD : y ∈ D := by
    change y ∈ residualPairStabilizer M t
    rw [pair_eq_stabilizers d]
    constructor
    · change y • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1
      rw [← hga]
      simp only [y, MulAut.conj_apply, mul_smul, inv_smul_smul, hxa]
    · change y • (QuotientGroup.mk t : G ⧸ M) = QuotientGroup.mk t
      rw [← hgb]
      simp only [y, MulAut.conj_apply, mul_smul, inv_smul_smul, hxb]
  have hyorder : orderOf (⟨y, hyD⟩ : D) = p := by
    rw [← orderOf_coe]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x).trans hxorder
  obtain ⟨k, hk⟩ := Theory.GroupAction.exists_conjugate_mem_of_prime_order
    (P.subtype hPD : Subgroup D) hp hyorder (P.subtype hPD).not_dvd_index
  let v : G := (k : G)⁻¹ * g
  have hvP : rightConjugateElem x v⁻¹ ∈ (P : Subgroup G) := by
    change (k : G)⁻¹ * y * (k : G) ∈ (P : Subgroup G) at hk
    simpa only [rightConjugateElem, v, inv_inv, mul_inv_rev, mul_assoc, y,
      MulAut.conj_apply] using hk
  have hvN : v ∈ normalizer (zpowers x : Set G) :=
    inv_mem_iff.mp (hweak v⁻¹ hvP)
  have hxne : x ≠ 1 := by
    intro he
    exact hp.ne_one (hxorder.symm.trans (orderOf_eq_one_iff.mpr he))
  have htN := (torus_normalizer_data d hx hxne).1
  have hsN : v⁻¹ * t * v ∈ normalizer (zpowers x : Set G) :=
    (normalizer (zpowers x : Set G)).mul_mem
      ((normalizer (zpowers x : Set G)).mul_mem
        ((normalizer (zpowers x : Set G)).inv_mem hvN) htN) hvN
  have hkfix : (k : G) ∈
      MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
        MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ M) := by
    simpa only [pair_eq_stabilizers d] using k.property
  have hva : v • a = QuotientGroup.mk 1 := by
    simp only [v, mul_smul, hga]
    exact (MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)).inv_mem hkfix.1))
  have hvb : v • b = QuotientGroup.mk t := by
    simp only [v, mul_smul, hgb]
    exact (MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ M)).inv_mem hkfix.2))
  refine ⟨v⁻¹ * t * v, ?_, hsN, ?_⟩
  · simpa only [MulAut.conj_apply, inv_inv] using d.minimal.disconnected.invariant v⁻¹ t d.t_mem
  apply MulAction.injective v
  simp only [mul_smul, hva, hvb, MulAction.Quotient.smul_mk,
    smul_eq_mul, mul_one, mul_inv_cancel_left]

/-- The rank-one normalizer action proves the fixed-point assertion once (12H) is supplied. -/
public theorem Context.torus_fixedPoints_of_weakClosure
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (P : Sylow p G)
    (hPD : (P : Subgroup G) ≤ residualPairStabilizer M t)
    (hweak : ∀ g : G, rightConjugateElem x g ∈ (P : Subgroup G) →
      g ∈ normalizer (zpowers x : Set G)) :
    ∀ beta : G ⧸ M, x • beta = beta ↔
      beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t := by
  classical
  have hxne : x ≠ 1 := by
    intro he
    exact hp.ne_one (hxorder.symm.trans (orderOf_eq_one_iff.mpr he))
  let Q := zpowers x
  let N := normalizer (Q : Set G)
  let F : SubMulAction N (G ⧸ M) :=
    { carrier := fixedPointsOfSubgroup G (G ⧸ M) Q
      smul_mem' := fun n _ h => fixedPoints_smul_of_mem_normalizer n.property h }
  have hfix {a : G ⧸ M} : x • a = a ↔ a ∈ F := by
    change x ∈ MulAction.stabilizer G a ↔ Q ≤ MulAction.stabilizer G a
    exact zpowers_le.symm
  have ht := d.minimal.disconnected.involutions t d.t_mem
  have htn := torus_normalizer_data d hx hxne
  have hodd : Odd (Nat.card Q) := by
    rw [Nat.card_zpowers]
    exact d.torus_odd.of_dvd_nat ((residualCommutator M t).orderOf_dvd_natCard hx)
  have hstr := d.odd_normalizer_structure Q hodd d.t_mem htn.1 htn.2
  let C := zpowers (⟨t, htn.1⟩ : N)
  let : MulAction C F := MulAction.compHom F C.subtype
  have hC : IsPGroup 2 C := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← orderOf_coe, orderOf_eq_prime ht.sq_eq_one ht.ne_one, pow_one])
  have hzero : Nat.card (MulAction.fixedPoints C F) = 0 := by
    rw [Finite.card_eq_zero_iff]
    refine ⟨fun a => ?_⟩
    have hta := congrArg (fun b : F => (b : G ⧸ M))
      (MulAction.mem_fixedPoints.mp a.property
        (⟨⟨t, htn.1⟩, mem_zpowers _⟩ : C))
    have htC := d.odd_normalizer_at_fixedPoint_centralizes Q hodd d.t_mem htn.1 hta
      (show Q ≤ MulAction.stabilizer G (a.val : G ⧸ M) from a.val.property)
    exact htn.2 htC
  have hEven : Even (Nat.card F) := by
    have hmod := hC.card_modEq_card_fixedPoints F
    rw [hzero] at hmod
    exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp hmod)
  let L : Subgroup N := closure (N.subtype ⁻¹' Z)
  let : MulAction L F := MulAction.compHom F L.subtype
  let alpha : F := ⟨QuotientGroup.mk 1, hfix.mp (torus_fixes_pair d hx).1⟩
  let beta0 : F := ⟨QuotientGroup.mk t, hfix.mp (torus_fixes_pair d hx).2⟩
  let : Nonempty F := ⟨alpha⟩
  have hpair : ∀ a b : F, a ≠ b → ∃ s : L, PFAppendixIII.IsInvolution s ∧ s • a = b := by
    intro a b hab
    obtain ⟨s, hsZ, hsN, hs⟩ := d.torus_normalizer_swap_of_weakClosure hx hp hxorder P hPD hweak
      (fun he => hab (Subtype.ext he)) (hfix.mpr a.property) (hfix.mpr b.property)
    let sN : N := ⟨s, hsN⟩
    have hsL : sN ∈ L := subset_closure hsZ
    refine ⟨⟨sN, hsL⟩, IsInvolution.subtype
      (IsInvolution.subtype (d.minimal.disconnected.involutions s hsZ) hsN) hsL, ?_⟩
    exact Subtype.ext hs
  have hcard : Nat.card F = 2 := chapter1_rank_one_pair_involutions_card_eq_two
    hstr.rank hEven hpair
  have hab : beta0 ≠ alpha := by
    intro he
    exact base_ne_translate d (congrArg (fun a : F => (a : G ⧸ M)) he).symm
  obtain ⟨b, hb, huniq⟩ := (Nat.card_eq_two_iff' alpha).mp hcard
  intro beta
  constructor
  · intro hbeta
    let a : F := ⟨beta, hfix.mp hbeta⟩
    by_cases ha : a = alpha
    · exact Or.inl (congrArg (fun c : F => (c : G ⧸ M)) ha)
    · exact Or.inr (congrArg (fun c : F => (c : G ⧸ M))
        ((huniq a ha).trans (huniq beta0 hab).symm))
  · rintro (rfl | rfl)
    · exact (torus_fixes_pair d hx).1
    · exact (torus_fixes_pair d hx).2

/-- Prime-order extraction reduces Proposition 12.13 to its prime-order elements. -/
public theorem Context.torus_semiregular_of_prime_fixedPoints
    (hprime : ∀ (p : ℕ), p.Prime → ∀ x ∈ residualCommutator M t,
      orderOf x = p → ∀ beta : G ⧸ M, x • beta = beta →
        beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t) :
    TorusSemiregular M t := by
  intro x hx hxne beta
  constructor
  · intro hfix
    have ho : orderOf x ≠ 1 := fun h => hxne (orderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd ho
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := zpowers x) p
      (by rwa [Nat.card_zpowers])
    have hyK : (y : G) ∈ residualCommutator M t := (zpowers_le.mpr hx) y.property
    have hyfix : (y : G) • beta = beta :=
      (zpowers_le.mpr (show x ∈ MulAction.stabilizer G beta from hfix)) y.property
    exact hprime p hp y hyK ((orderOf_coe y).trans hy) beta hyfix
  · rintro (rfl | rfl)
    · exact (torus_fixes_pair d hx).1
    · exact (torus_fixes_pair d hx).2

/-- The final normalizer-action and prime-reduction assembly, with weak closure explicit. -/
public theorem Context.torus_semiregular_of_weakClosure
    (hweak : ∀ (p : ℕ), p.Prime → ∀ x ∈ residualCommutator M t, orderOf x = p →
      ∃ P : Sylow p G, (P : Subgroup G) ≤ residualPairStabilizer M t ∧
        ∀ g : G, rightConjugateElem x g ∈ (P : Subgroup G) →
          g ∈ normalizer (zpowers x : Set G)) : TorusSemiregular M t := by
  apply d.torus_semiregular_of_prime_fixedPoints
  intro p hp x hx hxorder beta hfix
  obtain ⟨P, hPD, hP⟩ := hweak p hp x hx hxorder
  exact (d.torus_fixedPoints_of_weakClosure hx hp hxorder P hPD hP beta).mp hfix


/-- The initial invariant Sylow subgroup of the pair stabilizer, containing the chosen torus element. -/
public theorem Context.exists_invariant_pairSylow_torus_prime
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) :
    ∃ P : Subgroup G, theorem4bIsSylowSubgroupOf p P (residualPairStabilizer M t) ∧
      x ∈ P ∧ t ∈ normalizer (P : Set G) := by
  have ht := d.minimal.disconnected.involutions t d.t_mem
  have hodd : Odd p := hxorder ▸
    d.torus_odd.of_dvd_nat ((residualCommutator M t).orderOf_dvd_natCard hx)
  have hxne : x ≠ 1 := by
    intro he
    exact hp.ne_one (hxorder.symm.trans (orderOf_eq_one_iff.mpr he))
  have htD : t ∈ normalizer (residualPairStabilizer M t : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (M ⊓ M.conjBy t⁻¹).map (MulAut.conj t).toMonoidHom = M ⊓ M.conjBy t⁻¹
    rw [map_inf _ _ _ (MulAut.conj t).injective]
    change M.conjBy t ⊓ (M.conjBy t⁻¹).conjBy t = M ⊓ M.conjBy t⁻¹
    rw [conjBy_inv', ht.inv_eq_self, inf_comm]
  have hCp : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxorder, pow_one])
  have hCD : zpowers x ≤ residualPairStabilizer M t :=
    zpowers_le.mpr (d.torus_structure.1 ▸ hx).1
  have htbase : t • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk t := by
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  obtain ⟨P, hP, hCP, htP, _⟩ :=
    (actionSectionThree_of_productDisconnected d.minimal.disconnected).swapping_sylow
      t d.t_mem (QuotientGroup.mk 1) (by rw [htbase]; exact (base_ne_translate d).symm)
      p hp hodd (residualPairStabilizer M t) (zpowers x)
      (by rw [htbase, ← pair_eq_stabilizers d]) htD hCp hCD
      (torus_normalizer_data d hx hxne).1
  exact ⟨P, hP, hCP (mem_zpowers x), htP⟩

end BenderSuzuki.ZD.LinearExclusion
