module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.LinearBorel
public import Theory.SpecificGroups.SL2.ProjectiveBorelFrobenius

/-!
# The free torus action on the distinguished closure

Let `L = residualGenerated M z t`, `D = residualPairStabilizer M t`, and
`A = ⟨Z ∩ M⟩`. The actual binary PSL₂ equivalence and the Borel--Weyl
marking supplied by `LinearBorel` identify `D ∩ L` with the diagonal torus.
The already proved elementary-abelian structure of `A` places its image in
the upper root group. The existing projective Borel fixed-point theorem,
transported through the injective central quotient in characteristic two,
then shows that every nonidentity torus element fixes only the identity in A.

The final theorem transports the previously established torus order into M
and gives precisely the singleton-centralizer premise of
`linear_localControl_of_localization_and_orders`. It needs only the source
containment `A ≤ L`, beyond properness and the actual model isomorphism;
the additional residual-action and normalizer hypotheses are unnecessary
for this particular piece of local geometry.

Source: GLS, Volume 4, Chapter 4, Lemma 3.2(b--e), and the use of
`C_{M°J}(y) = J` for each `y ∈ K#` in Chapter 2, Lemma 15.6
(`refs/KGroup/GLS4/Chapter4.tex` and `Chapter2.tex`).
-/

noncomputable section
open BenderSuzuki BenderSuzuki.Converse BenderSuzuki.PFAppendixIII
open BenderSuzuki.PFchapter1section1 Subgroup Theory.GroupTheory

private theorem borel_sq_mem_unip {F : Type*} [Field F] [CharP F 2]
    {x : SL2 F} (hx : x ∈ Borel F) (h2 : x ^ 2 = 1) : x ∈ Unip F := by
  have h10 := (mem_Borel_iff _).mp hx
  have h00 : x.val 0 0 = 1 := by
    have hh := congrArg (fun a : SL2 F => a.val 0 0) h2
    have hs : x.val 0 0 ^ 2 = 1 := by
      simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, h10] using hh
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have h11 : x.val 1 1 = 1 := by rw [Borel_lower_right hx, h00, inv_one]
  apply (mem_Unip_iff _).mpr
  refine ⟨x.val 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem torus_fixedPointFree {F : Type*} [Field F] [CharP F 2]
    {k a : SL2 F} (hk : k ∈ Torus F) (hkn : k ≠ 1)
    (ha : a ∈ Unip F) (hc : a * k = k * a) : a = 1 := by
  let c := Converse.pi F
  have hk' : c k ∈ Matrix.ProjectiveSpecialLinearGroup.OddBorel.complement F := by
    rw [Torus_eq_range] at hk
    obtain ⟨d, rfl⟩ := hk
    exact ⟨d, rfl⟩
  have ha' : c a ∈ Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F := by
    obtain ⟨b, rfl⟩ := ha
    exact ⟨b, rfl⟩
  have hkn' : (⟨c k, hk'⟩ : Matrix.ProjectiveSpecialLinearGroup.OddBorel.complement F) ≠ 1 := by
    intro he
    apply hkn
    apply pi_injective
    simpa using congrArg Subtype.val he
  have hh := Matrix.ProjectiveSpecialLinearGroup.OddBorel.fixedPointFree F
    ⟨c k, hk'⟩ hkn' ⟨c a, ha'⟩ (by
      change c k * c a * (c k)⁻¹ = c a
      rw [← map_inv, ← map_mul, ← map_mul, ← hc, mul_assoc, mul_inv_cancel, mul_one])
  apply pi_injective
  simpa using congrArg Subtype.val hh

namespace BenderSuzuki.ZD

private theorem marked_pair_mem_torus
    {G : Type*} [Group G] {M L : Subgroup G}
    {F : Type*} [Field F] [CharP F 2] (e : L ≃* SL2 F)
    (he : ∀ x : L, e x ∈ Borel F ↔ (x : G) ∈ M)
    {t : G} (htL : t ∈ L) (het : e ⟨t, htL⟩ = weyl F)
    (x : L) (hx : (x : G) ∈ residualPairStabilizer M t) : e x ∈ Torus F := by
  have hconj (N : Subgroup G) (a b : G) :
      b ∈ rightConjugate N a ↔ a * b * a⁻¹ ∈ N := by
    rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
    simp [MulAut.conj_apply]
  have ht : Torus F = Borel F ⊓ rightConjugate (Borel F) (weyl F) := by
    rw [Borel, rightConjugate_stabilizer, weyl_inv, weyl_smul_pInf]
    rfl
  rw [ht, mem_inf]
  refine ⟨(he x).mpr hx.1, ?_⟩
  rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
  have hh := (he (⟨t, htL⟩ * x * ⟨t, htL⟩⁻¹)).mpr ((hconj M t x).mp hx.2)
  simpa [map_mul, map_inv, het, MulAut.conj_apply] using hh

/-- Every nonidentity element of the actual local torus fixes only the identity
in the distinguished closure, with both subgroups viewed inside M. -/
public theorem psl2_distinguishedClosure_element_centralizer
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
      k ≠ 1 → (closure (Z ∩ (M : Set G))).subgroupOf M ⊓
        centralizer ({k} : Set M) = ⊥ := by
  have hA := (psl2_distinguishedClosure_elementary_card h r hz hzM ht htM hL ⟨e⟩ hn hAL).1
  let := hA
  obtain ⟨f, hf, hft⟩ := residual_equiv_sl2_borel_weyl h r hz hzM ht htM hL ⟨e⟩
  have htL : t ∈ residualGenerated M z t :=
    (show zpowers t ≤ residualGenerated M z t from le_trans le_sup_right le_sup_left)
      (mem_zpowers t)
  intro k hk hkn
  apply (eq_bot_iff_forall _).mpr
  intro a ha
  let kL : residualGenerated M z t := ⟨k, hk.2⟩
  let aL : residualGenerated M z t := ⟨a, hAL ha.1⟩
  have hkT : f kL ∈ Torus (BinaryGaloisField n) :=
    marked_pair_mem_torus f hf htL (hft htL) kL hk.1
  have hkn' : f kL ≠ 1 := by
    intro he
    apply hkn
    apply Subtype.ext
    exact congrArg (fun x : residualGenerated M z t => (x : G))
      (f.injective (he.trans (map_one f).symm))
  have haU : f aL ∈ Unip (BinaryGaloisField n) := by
    apply borel_sq_mem_unip ((hf aL).mpr a.property)
    rw [← map_pow, ← map_one f]
    apply congrArg f
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian
      (A := closure (Z ∩ (M : Set G))) (a : G) ha.1
  have hc : f aL * f kL = f kL * f aL := by
    rw [← map_mul, ← map_mul]
    apply congrArg f
    apply Subtype.ext
    exact congrArg (fun x : M => (x : G))
      (mem_centralizer_singleton_iff.mp ha.2)
  have ha1 : f aL = 1 := torus_fixedPointFree hkT hkn' haU hc
  apply Subtype.ext
  exact congrArg (fun x : residualGenerated M z t => (x : G))
    (f.injective (ha1.trans (map_one f).symm))

/-- The torus order and elementwise fixed-point geometry used by local control.
The ambient torus is transported into M by its literal subgroup inclusion. -/
public theorem linear_distinguishedClosure_torus_geometry
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    Nat.card ((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) =
        2 ^ n - 1 ∧
      ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
        k ≠ 1 → (closure (Z ∩ (M : Set G))).subgroupOf M ⊓
          centralizer ({k} : Set M) = ⊥ := by
  refine ⟨?_, psl2_distinguishedClosure_element_centralizer h.disconnected r hz hzM ht htM hL hn e hAL⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show residualPairStabilizer M t ⊓ residualGenerated M z t ≤ M from
      le_trans inf_le_left inf_le_left)).toEquiv]
  exact (psl2_local_pair_cyclic_card h.disconnected r hz hzM ht htM hL hn ⟨e⟩).2

end BenderSuzuki.ZD
