module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.OddModelSubgroups
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.Incidence
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.FixedPoints
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.Numerics
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.ModelAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting

/-!
# Section 17 counting and elimination of the nonlinear local models

The two incidence counts in the original u-conjugacy class give Lemma 17.1.
The centralizer factorizations and concrete model actions give a*c = q-1;
Section 16 divisibility then gives c ≡ 1 mod q. Marked fusion transports each
actual model to the twisted circle. Its odd subgroup and relative normalizer
exclude Suzuki, PSU₃, and SU₃, and select the linear torus with c = q+1.
The ratio `Section17.centralizerRatio` is the actual rational centralizer-order
ratio. The internal distinguished closure is transported through its subtype
map, yielding exactly the witness used by the existing counting constructor.

This is an explicitly conditional route. The original local data, all four
Section 16 model alternatives at one parameter, Sylow placement and divisibility,
marked fusion, and the literal 17.2(e,f) clauses remain inputs. Their earlier
source construction belongs to the unconditional Section 17 assembly.
No degree, incidence value, congruence, torus conclusion, or selected linear
model is assumed in the final theorem.

Source: GLS4, Chapter 2, (17B), (17D–F), Lemmas 17.1–17.5.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Source (17F), with the fixed-point count replaced by its proved local
index. The group D and the involution u remain the original ones. -/
public theorem fixed_pair_count_at_circle_index
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) :
    let f := (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index
    Nat.card {v : G // IsConj ((d.u : M) : G) v} * (f * (f - 1)) =
      (Nat.card (G ⧸ M) * (Nat.card (G ⧸ M) - 1)) *
        (centralizer ({((d.u : M) : G)} : Set G)).relIndex
          (residualPairStabilizer M d.t) := by
  have hc := fixed_pair_count h ha d hlocal
  dsimp only at hc ⊢
  rwa [fixedPoints_card_eq_circle_index h r d] at hc

/-- The actual Δ count with its local fixed-point index; the swapping
fiber is retained as a set in the original u-conjugacy class. -/
public theorem moved_pair_count_at_circle_index
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (d : TwoCoreLocalData Z M) :
    let f := (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index
    Nat.card {v : G // IsConj ((d.u : M) : G) v} * (Nat.card (G ⧸ M) - f) =
      (Nat.card (G ⧸ M) * (Nat.card (G ⧸ M) - 1)) *
        Nat.card {v : {v : G // IsConj ((d.u : M) : G) v} //
          v.val • (QuotientGroup.mk 1 : G ⧸ M) =
            d.t • (QuotientGroup.mk 1 : G ⧸ M)} := by
  have hc := moved_pair_count h ha d
  dsimp only at hc ⊢
  rwa [fixedPoints_card_eq_circle_index h r d] at hc

omit [Finite G] in
/-- Apply (17B) to any of the four actual carriers at the same parameter.
The equivalence is obtained from the marked ambient fusion, not conversely. -/
public theorem twisted_circle_model {K : Type*} [Group K]
    (h : IsProductDisconnected Z M) (d : TwoCoreLocalData Z M)
    (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G)))
    (e : centralizerClosure Z ((d.u : M) : G) ≃* K) :
    Nonempty (centralizerClosure Z (d.t * ((d.u : M) : G)) ≃* K) := by
  obtain ⟨f⟩ := centralizerClosure_equiv_of_isConj h hfusion
  exact ⟨f.symm.trans e⟩

section SourceInputs
open _root_.BenderSuzuki.MatrixGroups ModelAction
variable (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
  (ha : ResidualAction Z M) (hnM : ¬ IsStronglyEmbedded M)
  (hg : ResidualGeneration Z M) (d : TwoCoreLocalData Z M)
  (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
    HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
  (n : ℕ) (hn : 2 ≤ n)
  (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
  (hPM : (P : Subgroup _).map (centralizerClosure Z ((d.u : M) : G)).subtype ≤ M)
  (hdiv : 2 ^ n * Nat.card P ∣ Nat.card (G ⧸ M) - 1)
  (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G)))
  (hfix : ∀ gamma : G ⧸ M,
    residualPairStabilizer M d.t ⊓
        centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
      MulAction.stabilizer G gamma ↔
    gamma = QuotientGroup.mk 1 ∨ gamma = d.t • (QuotientGroup.mk 1 : G ⧸ M))
  (hN : let L := centralizerClosure Z (d.t * ((d.u : M) : G))
    let H := (residualPairStabilizer M d.t ⊓ L).subgroupOf L
    let t : L := ⟨d.t, t_mem_twisted_circle d⟩
    normalizer (H : Set L) ≤ H ⊔ zpowers t)
  (hmodels : Nonempty (centralizerClosure Z ((d.u : M) : G) ≃* PSL2BinaryMatrixGroup n) ∨
    (∃ m : ℕ, 1 ≤ m ∧ n = 2*m+1 ∧
      Nonempty (centralizerClosure Z ((d.u : M) : G) ≃* SuzukiMatrixGroup m)) ∨
    (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      Nat.card E = (2 ^ n)^2 ∧ Nat.card {x : E // J.conj x = x} = 2^n ∧
      (Nonempty (centralizerClosure Z ((d.u : M) : G) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
       Nonempty (centralizerClosure Z ((d.u : M) : G) ≃* J.specialSubgroup))))

include h r ha hnM hg d hlocal n hn P hPM hdiv hfusion hfix hN hmodels

/-- The conditional source route through Lemmas 17.1–17.5, at the SAME
parameter and local data as Section 16. All four concrete model alternatives
are retained as inputs; the three nonlinear alternatives are eliminated here.
The only earlier inputs beyond the original hypotheses and d are the model
alternatives, the original Sylow placement and divisibility, marked fusion,
and the literal fixed-point and relative-normalizer clauses 17.2(e,f).
The rational number is the actual centralizer-order ratio. -/
public theorem linear_count_at_source_parameter :
    (Nat.card (G ⧸ M) : ℚ) - 1 =
        (2 ^ n : ℚ) * (((2 ^ n : ℚ) + 1) * centralizerRatio d + 1) ∧
      centralizerRatio d * ((2 ^ n : ℚ) + 1) = (2 ^ n : ℚ) - 1 ∧
      Nonempty ((closure ((centralizer ({((d.u : M) : G)} : Set G)).subtype ⁻¹' Z)) ≃*
        PSL2BinaryMatrixGroup n) := by
  let L := centralizerClosure Z (d.t * ((d.u : M) : G))
  let H := (residualPairStabilizer M d.t ⊓ L).subgroupOf L
  let t : L := ⟨d.t, t_mem_twisted_circle d⟩
  let c := (centralizer ({t} : Set L)).relIndex H
  obtain ⟨hodd, ht, htH, hc⟩ := twistedPair_intrinsic h.disconnected d
  have hq : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have numerics (hqp : 2 ^ n ∣ Nat.card P)
      (hdeg : (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index = Nat.card P + 1)
      (htor : (centralizer ({d.t} : Set G)).relIndex
        (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G)) = 2 ^ n - 1) :
      centralizerRatio d * (c : ℚ) = (2 ^ n : ℚ) - 1 ∧ c % (2 ^ n) = 1 := by
    dsimp only [c, H, t, L]
    rw [twistedPair_index_eq_ambient d]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      ratio_and_congruence_of_action h.disconnected r ha d hlocal hfusion
        (Nat.card P) (2^n) Nat.card_pos hq hqp hdiv hdeg htor
  rcases hmodels with he | ⟨m, hm, hnm, ⟨e⟩⟩ | ⟨E, instE, finE, J, hcard, hfield, he⟩
  · obtain ⟨e⟩ := he
    obtain ⟨_, hp, hdeg, htor⟩ := linear_action h r ha hnM hg hlocal d hn e P hPM
    obtain ⟨hratio, hmod⟩ := numerics (by rw [hp]) hdeg htor
    obtain ⟨eL⟩ := twisted_circle_model h.disconnected d hfusion e
    have hcq := (psl2_odd_normalizer_index_eq_succ_of_equiv
      (Converse.card_binaryGaloisField n (by omega)) hn eL H hodd ht htH hN hc hmod).2.2.2
    change c = 2 ^ n + 1 at hcq
    rw [hcq] at hratio
    have hr : centralizerRatio d * ((2 ^ n : ℚ) + 1) = (2 ^ n : ℚ) - 1 := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hratio
    have hcount := count_at_circle_index h.disconnected r ha d hlocal hfusion
    dsimp only at hcount
    rw [hdeg, hp, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      add_sub_cancel_right] at hcount
    exact ⟨hcount, hr, ⟨(internalCentralizerClosureEquiv Z ((d.u : M) : G)).trans e⟩⟩
  · obtain ⟨_, hp, hdeg, htor⟩ := suzuki_action h r ha hnM hg hlocal d hn hm hnm e P hPM
    obtain ⟨_, hmod⟩ := numerics (by rw [hp]; exact dvd_pow_self _ (by decide)) hdeg htor
    obtain ⟨eL⟩ := twisted_circle_model h.disconnected d hfusion e
    exact False.elim ((suzuki_odd_normalizer_index_not_congruent_one_of_equiv
      (by omega) eL H hodd ht htH hN) (hnm ▸ hmod))
  · rcases he with he | he
    · obtain ⟨e⟩ := he
      obtain ⟨_, hp, hdeg, htor⟩ := projective_unitary_action h r ha hnM hg hlocal d J hn hcard hfield e P hPM
      obtain ⟨_, hmod⟩ := numerics (by rw [hp]; exact dvd_pow_self _ (by decide)) hdeg htor
      obtain ⟨eL⟩ := twisted_circle_model h.disconnected d hfusion e
      have hB := twistedPair_projective_noBorel h.disconnected r d hfix J hn hcard hfield eL
      exact False.elim ((projective_unitary_odd_normalizer_index_not_congruent_one_of_equiv
        J hn hcard hfield eL H hodd t ht htH hB hN hc) hmod)
    · obtain ⟨e⟩ := he
      obtain ⟨_, hp, hdeg, htor⟩ := special_unitary_action h r ha hnM hg hlocal d J hn hcard hfield e P hPM
      obtain ⟨_, hmod⟩ := numerics (by rw [hp]; exact dvd_pow_self _ (by decide)) hdeg htor
      obtain ⟨eL⟩ := twisted_circle_model h.disconnected d hfusion e
      have hB := twistedPair_special_noBorel h.disconnected r d hfix J hn hcard hfield eL
      exact False.elim ((special_unitary_odd_normalizer_index_not_congruent_one_of_equiv
        J hn hcard hfield eL H hodd t ht htH hB hN hc) hmod)

/-- The exact existential witness consumed by the existing counting
constructor. It retains the actual internal distinguished closure. -/
public theorem local_linear_count_of_source_inputs :
    ∃ n : ℕ, 0 < n ∧ ∃ a : ℚ,
      (Nat.card (G ⧸ M) : ℚ) - 1 = (2 ^ n : ℚ) * (((2 ^ n : ℚ) + 1) * a + 1) ∧
      a * ((2 ^ n : ℚ) + 1) = (2 ^ n : ℚ) - 1 ∧
      Nonempty ((closure ((centralizer ({((d.u : M) : G)} : Set G)).subtype ⁻¹' Z)) ≃*
        PSL2BinaryMatrixGroup n) := by
  exact ⟨n, by omega, centralizerRatio d,
    linear_count_at_source_parameter h r ha hnM hg d hlocal n hn P hPM hdiv hfusion hfix hN hmodels⟩

/-- Literal application to the existing TwoCoreCountingData constructor.
The parent must construct d and discharge the stated earlier source inputs;
this theorem does not assert the unconditional Section 17 implication. -/
public theorem twoCoreCountingData_of_source_inputs : Nonempty (TwoCoreCountingData Z M) := by
  obtain ⟨k, hk, a, hcount, hratio, he⟩ :=
    local_linear_count_of_source_inputs h r ha hnM hg d hlocal n hn P hPM hdiv hfusion hfix hN hmodels
  exact twoCoreCountingData_of_local_linear_count h.disconnected ha d k hk a hcount hratio he

end SourceInputs

end BenderSuzuki.ZD.Section17
