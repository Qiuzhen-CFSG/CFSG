module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.TorusFixedPoints.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.TorusFixedPoints.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.OddNormalizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed

/-!
# The ambient torus Sylow and its fixed intersection

Let `K = residualCommutator M t` and let `P` be a `t`-invariant Sylow
subgroup of the literal pair stabilizer `D`, containing a prime-order
`x ∈ K`. The identity `K = [D, ⟨t⟩]` identifies `K ∩ P` with the
inverted elements of the odd subgroup `P`. Section 3 therefore gives
`K ∩ P` the full prime-share inverted cardinality.

If this intersection fixed a third point, enlarge it to a maximal
Proposition 5.2 candidate `Q`. Clause (a) makes `Q` fix a point fixed
by a distinguished involution normalizing `Q`. The odd-normalizer
centralization theorem then makes that involution centralize `x`,
contrary to (12F). This proves (12G) before ambient Sylow promotion.
Since `P` also has exactly the two marked fixed points, the two-point
Sylow criterion promotes `P` to an ambient Sylow subgroup.

The resulting `TorusSylowData` discharges the Sylow premise of
`Context.torus_semiregular_of_sylowData`. Weak closure (12H) and the
final Proposition 12.13 assembly remain with their independent owners.
No odd-order assumption on `D` is made.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Proposition 12.13, equation
(12G), Proposition 5.2(a), and Corollary 7.12(a).
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
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

omit d in
private theorem pgroup_odd {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {P : Subgroup G} (hP : IsPGroup p P) : Odd (Nat.card P) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact hpodd.pow

omit d [Finite G] in
private theorem sylow_data {p : ℕ} {P D : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P D) : P ≤ D ∧ IsPGroup p P := by
  obtain ⟨Q, rfl⟩ := hP
  refine ⟨?_, Q.isPGroup'.map D.subtype⟩
  simpa using map_le_range D.subtype (Q : Subgroup D)

/-- The torus intersection with an odd subgroup of the pair stabilizer is its actual inverted set. -/
public theorem Context.torus_inf_eq_inverted {P : Subgroup G}
    (hPodd : Odd (Nat.card P)) (hPD : P ≤ residualPairStabilizer M t) :
    ((residualCommutator M t ⊓ P : Subgroup G) : Set G) =
      {y | y ∈ P ∧ t * y * t⁻¹ = y⁻¹} := by
  have ht := d.minimal.disconnected.involutions t d.t_mem
  ext y
  constructor
  · intro hy
    exact ⟨hy.2, by simpa only [rightConjugateElem, ht.inv_eq_self]
      using d.torus_structure.2.2.2 y hy.1⟩
  · intro hy
    refine ⟨?_, hy.1⟩
    rw [residualCommutator_eq_pair_commutator d.minimal.disconnected d.t_mem d.t_not_mem_M]
    apply commutator_mono hPD le_rfl
    exact IsStronglyEmbedded.mem_commutator_zpowers_of_mem_peterfalviKSet P hPodd ht
      ⟨hy.1, by simpa only [rightConjugateElem, ht.inv_eq_self] using hy.2⟩

private theorem torus_inf_invertedCard {P : Subgroup G}
    (hPodd : Odd (Nat.card P)) (hPD : P ≤ residualPairStabilizer M t) :
    theorem4bInvertedCard t (residualCommutator M t ⊓ P) = theorem4bInvertedCard t P := by
  unfold theorem4bInvertedCard
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro y
  have he := Set.ext_iff.mp (d.torus_inf_eq_inverted hPodd hPD) y
  change y ∈ residualCommutator M t ⊓ P ↔
    y ∈ P ∧ t * y * t⁻¹ = y⁻¹ at he
  change (y ∈ residualCommutator M t ⊓ P ∧ t * y * t⁻¹ = y⁻¹) ↔
    (y ∈ P ∧ t * y * t⁻¹ = y⁻¹)
  rw [he]
  exact and_iff_left_of_imp And.right

private theorem distinguished_has_fixedPoint {s : G} (hs : s ∈ Z) :
    ∃ beta : G ⧸ M, s • beta = beta := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (d.reduction.one_class z d.z_mem s hs)
  have hzfix : z • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 :=
    MulAction.mem_stabilizer_iff.mp (by simpa only [baseCoset_stabilizer] using d.z_mem_M)
  refine ⟨g • QuotientGroup.mk 1, ?_⟩
  rw [← hg]
  simp only [mul_smul, inv_smul_smul, hzfix]

private theorem no_candidate_containing_torus_prime
    {x : G} (hx : x ∈ residualCommutator M t) (hxne : x ≠ 1)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) {R : Subgroup G}
    (hR : actionPrimeShareCandidate Z M z p R) (hxR : x ∈ R) : False := by
  obtain ⟨Q, hRQ, hmax⟩ := Finite.exists_le_maximal hR
  obtain ⟨s, hsZ, hsN, _⟩ := hmax.1.2.2
  obtain ⟨beta, hsBeta⟩ := distinguished_has_fixedPoint d hsZ
  have hQBeta := actionPrimeShareMaximalFixes_of_sectionThree d.minimal d.reduction
    (actionSectionThree_of_productDisconnected d.minimal.disconnected)
    z d.z_mem d.z_mem_M p hp hpodd Q hmax s hsZ hsN beta hsBeta
  have hsC := d.odd_normalizer_at_fixedPoint_centralizes Q
    (pgroup_odd hp hpodd hmax.1.1) hsZ hsN hsBeta hQBeta
  have hsx : s ∈ centralizerClosure Z x := subset_closure
    ⟨hsZ, mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hsC x (hRQ hxR)).symm)⟩
  rw [d.torus_centralizerClosure_eq_bot hx hxne] at hsx
  exact (d.minimal.disconnected.involutions s hsZ).ne_one hsx

/-- Equation (12G), proved for the invariant pair Sylow before ambient promotion. -/
public theorem Context.torus_pairSylow_fixedPoints
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) {P : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P (residualPairStabilizer M t))
    (hxP : x ∈ P) (htP : t ∈ normalizer (P : Set G)) :
    ∀ beta : G ⧸ M,
      (∀ y ∈ residualCommutator M t ⊓ P, y • beta = beta) ↔
        beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t := by
  classical
  have hpodd : Odd p := hxorder ▸
    d.torus_odd.of_dvd_nat ((residualCommutator M t).orderOf_dvd_natCard hx)
  have hxne : x ≠ 1 := by
    intro he
    exact hp.ne_one (hxorder.symm.trans (orderOf_eq_one_iff.mpr he))
  obtain ⟨hPD, hPp⟩ := sylow_data hP
  let R := residualCommutator M t ⊓ P
  have hRp : IsPGroup p R := hPp.to_inf_right
  have hRD : R ≤ residualPairStabilizer M t := inf_le_right.trans hPD
  have hfix (beta : G ⧸ M)
      (hb : beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t) :
      ∀ y ∈ R, y • beta = beta := by
    intro y hy
    have hyD := hRD hy
    rw [pair_eq_stabilizers d] at hyD
    rcases hb with rfl | rfl
    · exact hyD.1
    · exact hyD.2
  have htR : t ∈ normalizer (R : Set G) := inf_normalizer_le_normalizer_inf
    ⟨normalizer_commutator_ge_right _ _ (mem_zpowers t), htP⟩
  have htbase : t • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk t := by
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hshare : theorem4bInvertedCard t R = theorem4bPrimeShare M z p := by
    rw [torus_inf_invertedCard d (pgroup_odd hp hpodd hPp) hPD]
    apply ((actionSectionThree_of_productDisconnected d.minimal.disconnected).swapping_bound
      z d.z_mem d.z_mem_M t d.t_mem (QuotientGroup.mk 1)
      (by rw [htbase]; exact (base_ne_translate d).symm) p hp hpodd P hPp
      (by rwa [htbase, ← pair_eq_stabilizers d]) htP).2
    rwa [htbase, ← pair_eq_stabilizers d]
  intro beta
  refine ⟨?_, hfix beta⟩
  intro hbeta
  by_contra hnot
  have ha := hfix (QuotientGroup.mk 1) (Or.inl rfl)
  have hb := hfix (QuotientGroup.mk t) (Or.inr rfl)
  let a : theorem4bFixedPoints M R := ⟨QuotientGroup.mk 1, ha⟩
  let b : theorem4bFixedPoints M R := ⟨QuotientGroup.mk t, hb⟩
  let c : theorem4bFixedPoints M R := ⟨beta, hbeta⟩
  have hba : b ≠ a := fun he => base_ne_translate d (congrArg Subtype.val he).symm
  have hca : c ≠ a := fun he => hnot (Or.inl (congrArg Subtype.val he))
  have hcb : c ≠ b := fun he => hnot (Or.inr (congrArg Subtype.val he))
  have hthree : 3 ≤ Nat.card (theorem4bFixedPoints M R) := by
    have htwo := action_two_le_fixedPoints (hRD.trans inf_le_left)
      (show R ≤ MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ M) from hb)
      (base_ne_translate d).symm
    by_contra hlt
    have hcard : Nat.card (theorem4bFixedPoints M R) = 2 := by omega
    obtain ⟨q, _, hq⟩ := (Nat.card_eq_two_iff' a).mp hcard
    exact hcb ((hq c hca).trans (hq b hba).symm)
  exact no_candidate_containing_torus_prime d hx hxne hp hpodd
    ⟨hRp, hthree, t, d.t_mem, htR, hshare⟩ (show x ∈ R from ⟨hx, hxP⟩)

/-- The invariant ambient Sylow and fixed-intersection data used immediately before (12H). -/
public theorem Context.exists_torusSylowData
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) : Nonempty (TorusSylowData M t x p) := by
  classical
  obtain ⟨P, hP, hxP, htP⟩ := d.exists_invariant_pairSylow_torus_prime hx hp hxorder
  obtain ⟨hPD, hPp⟩ := sylow_data hP
  have hfixed := d.torus_pairSylow_fixedPoints hx hp hxorder hP hxP htP
  have hfix : ∀ beta : G ⧸ M, beta ∈ fixedPointsOfSubgroup G (G ⧸ M) P ↔
      beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t := by
    intro beta
    constructor
    · intro hb
      exact (hfixed beta).mp (fun y hy => hb y hy.2)
    · rintro (rfl | rfl) y hy
      · have hh := hPD hy
        rw [pair_eq_stabilizers d] at hh
        exact hh.1
      · have hh := hPD hy
        rw [pair_eq_stabilizers d] at hh
        exact hh.2
  have hcard : Nat.card (theorem4bFixedPoints M P) = 2 := by
    apply Nat.card_eq_two_iff.mpr
    refine ⟨⟨QuotientGroup.mk 1, (hfix _).mpr (Or.inl rfl)⟩,
      ⟨QuotientGroup.mk t, (hfix _).mpr (Or.inr rfl)⟩,
      fun he => base_ne_translate d (congrArg Subtype.val he), ?_⟩
    ext beta
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ((hfix beta.val).mp beta.property).imp Subtype.ext Subtype.ext
  have hpodd : Odd p := hxorder ▸
    d.torus_odd.of_dvd_nat ((residualCommutator M t).orderOf_dvd_natCard hx)
  obtain ⟨S, hS⟩ := chapter1_two_fixed_local_sylow_is_ambient hp hpodd hPp
    (base_ne_translate d) ((hfix _).mpr (Or.inl rfl)) ((hfix _).mpr (Or.inr rfl))
    hcard (by rwa [← pair_eq_stabilizers d])
  refine ⟨⟨S, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [hS] using hPD
  · simpa only [hS] using hxP
  · simpa only [hS] using htP
  · simpa only [hS] using hfixed

end BenderSuzuki.ZD.SuzukiExclusion
