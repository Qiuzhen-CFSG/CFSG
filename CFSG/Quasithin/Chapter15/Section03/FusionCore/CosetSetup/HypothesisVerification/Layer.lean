module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.Core
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.SmallTwoCentralQuotientCommutator

/-!
# The order-two section and the containment of L₁T

The fixed plane has order four and Z has order two, so Z_S/Z has no proper
nontrivial subgroup. Normalization therefore gives the irreducible action
required by F.9.1(b). Its normal image in T/Z has order two and is central.
The product calculation places L₁ inside C_Y(V). This is contained in H
in the ordinary branch because O₂(Y) ≤ T, and in the extraspecial branch
by the explicit side condition in 15.3.48.

Finally H* here is the actual quotient H/O₂(H), whose two-core is trivial
by the general core-lifting theorem. No faithfulness assumption is needed
for this particular conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.48,
printed pp.1141–1142; F.9.1(b), printed p.318.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual section Z_S/Z has order two. -/
theorem four_two_quotient_card (A Z : Subgroup G) [(Z.subgroupOf A).Normal]
    (hZA : Z ≤ A) (hA : Nat.card A = 4) (hZ : Nat.card Z = 2) :
    Nat.card (A ⧸ Z.subgroupOf A) = 2 := by
  have hc := (Z.subgroupOf A).card_mul_index
  have hz : Nat.card (Z.subgroupOf A) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv).trans hZ
  rw [hz, hA, Subgroup.index_eq_card] at hc
  omega

/-- There are no intermediate subgroups in a section of orders four and
two, hence no intermediate invariant subgroups for any action. -/
theorem four_two_no_intermediate (A Z : Subgroup G)
    (hA : Nat.card A = 4) (hZ : Nat.card Z = 2) :
    ∀ W : Subgroup G, Z ≤ W → W ≤ A → W = Z ∨ W = A := by
  intro W hZW hWA
  have hlow : 2 ≤ Nat.card W := hZ ▸ card_le_of_le hZW
  have hupp : Nat.card W ≤ 4 := hA ▸ card_le_of_le hWA
  have hd : Nat.card W ∣ 4 := hA ▸ card_dvd_of_le hWA
  have he : Nat.card W = 2 ∨ Nat.card W = 4 := by
    interval_cases hw : Nat.card W <;> simp_all
  rcases he with he | he
  · exact Or.inl (eq_of_le_of_card_ge hZW (by omega)).symm
  · exact Or.inr (eq_of_le_of_card_ge hWA (by omega))

/-- The first assertion of 15.3.48(2), in the actual quotient of T. -/
theorem order_two_section_central (T A Z : Subgroup G) [(Z.subgroupOf T).Normal]
    (hAT : A ≤ T) (hZA : Z ≤ A) (hA : Nat.card A = 4) (hZ : Nat.card Z = 2)
    (hTA : T ≤ normalizer (A : Set G)) :
    (A.subgroupOf T).map (QuotientGroup.mk' (Z.subgroupOf T)) ≤
      center (T ⧸ Z.subgroupOf T) := by
  have ha : Nat.card (A.subgroupOf T) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans hA
  have hz : Nat.card (Z.subgroupOf T) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hZA.trans hAT)).toEquiv).trans hZ
  have hnormal : (A.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hTA
  let := hnormal
  have hp : IsPGroup 2 (A.subgroupOf T) := IsPGroup.of_card (n := 2) (by simpa using ha)
  have hc := commutator_le_of_card_lt_eight_of_normal_order_two
    (A.subgroupOf T) (Z.subgroupOf T) (⊤ : Subgroup T) hp
    (subgroupOf_mono T hZA) hz le_normalizer_of_normal (by omega)
  intro x hx
  obtain ⟨a, ha, rfl⟩ := hx
  apply mem_center_iff.mpr
  intro t
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf T) t
  have hc' := hc (commutator_mem_commutator ha (mem_top t))
  have hcomm : ⁅QuotientGroup.mk' (Z.subgroupOf T) a,
      QuotientGroup.mk' (Z.subgroupOf T) t⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hc'
  exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm

/-- Both branches give L₁T ≤ H. The second disjunct retains exactly the
extra containment required in the extraspecial branch. -/
theorem localL1_sup_le (M Y H V Z : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcases : Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2 ∨
      Y ⊓ centralizer (V : Set G) ≤ H) : localL1 Y Z ⊔ (T : Subgroup G) ≤ H := by
  apply sup_le _ hTH
  have hl := localL1_le_centralizer M Y V Z T hYM hM hTM hfactor
  rcases hcases with h | h
  · exact ((hl.trans_eq h).trans (core_le_sylow_of_invariant Y T hTY)).trans hTH
  · exact hl.trans h

/-- L₁ centralizes the entire V, while T normalizes the fixed plane. -/
theorem localL1_sup_normalizes (M Y V A Z : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G)) (hTM : (T : Subgroup G) ≤ M)
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hAV : A ≤ V) (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    localL1 Y Z ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) := by
  apply sup_le _ hTA
  exact ((localL1_le_centralizer M Y V Z T hYM hM hTM hfactor).trans inf_le_right).trans
    ((centralizer_le hAV).trans (Subgroup.centralizer_le_normalizer _))

/-- F.9.1(b): normalization and the absence of intermediate invariant
subgroups are proved separately, without assuming irreducibility. -/
theorem localL1_irreducible (M Y V A Z : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G)) (hTM : (T : Subgroup G) ≤ M)
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hAV : A ≤ V) (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hA : Nat.card A = 4) (hZ : Nat.card Z = 2) :
    localL1 Y Z ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) ∧
      ∀ W : Subgroup G, Z ≤ W → W ≤ A →
        localL1 Y Z ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) → W = Z ∨ W = A :=
  ⟨localL1_sup_normalizes M Y V A Z T hYM hM hTM hfactor hAV hTA,
    fun W hZW hWA _ => four_two_no_intermediate A Z hA hZ W hZW hWA⟩

/-- Source 15.3.48(4). Here H* is literally H/O₂(H). -/
theorem lemma_15_3_48_4 (H : Subgroup G) : pCore 2 (CoreQuotient H) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := q.comap_pCore_of_ker_isPGroup hq hk
  have hm := congrArg (Subgroup.map q) he
  rw [map_comap_eq_self_of_surjective hq] at hm
  exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

end
