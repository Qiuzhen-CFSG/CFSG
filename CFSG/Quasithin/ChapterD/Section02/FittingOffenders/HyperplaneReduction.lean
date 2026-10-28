module

public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.CyclicPrime
public import Theory.GroupAction.HyperplaneCommutatorGeneration
public import Theory.Representation.BinaryOffender.FixedSpaceFaithfulness
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Faithful hyperplane restrictions of Fitting offenders

For a hyperplane B of a noncyclic starred cubic actor A, Thompson A×B
makes C_(O_p(G))(B) faithful on C_V(B). If A fixed this space, its
commutator with the odd centralizer would lie in that faithful kernel.
A nontrivial commutator therefore forces D.2.7's strict ratio drop. The
image has rank one and its kernel in A is precisely B. Hyperplane
centralizers generate the odd-core commutator, so some such fixed space
is moved. Its faithful rank-one image has ratio at least one. Hence a
noncyclic actor has ratio greater than one, proving all of D.2.13(4)
by the already established cyclic case.

Source: Aschbacher--Smith, D.2.13, noncyclic reduction on printed p.185.
The subsequent identification of the odd commutator and its support is
not asserted here.
-/

public section
namespace CFSG.Quasithin.ChapterD
open Representation.BinaryOffender Subgroup
open scoped IsMulCommutative ENNReal commutatorElement
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The genuine hyperplane restriction in D.2.13: Thompson A×B makes the
odd centralizer faithful, so a nontrivial commutator forces the strict
ratio-drop branch on the literal hyperplane fixed space. -/
theorem source_lemma_D_2_13_hyperplane_restriction
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (B : Subgroup G) (hBA : B ≤ A) (hhyper : rank B + 1 = rank A)
    (hm : ⁅pCore p G ⊓ centralizer (B : Set G), A⁆ ≠ ⊥) :
    subspaceKernel ρ (fixedSpace ρ B) (pCore p G ⊓ centralizer (B : Set G)) = ⊥ ∧
      subspaceKernel ρ (fixedSpace ρ B) A = B ∧
      rank (restrictedSubgroup ρ (fixedSpace ρ B) A) = 1 ∧
      restrictedSubgroup ρ (fixedSpace ρ B) A ∈ Qhat
        (subspaceImageRepresentation ρ (fixedSpace ρ B)) ∧
      actionRatio (subspaceImageRepresentation ρ (fixedSpace ρ B))
        (restrictedSubgroup ρ (fixedSpace ρ B) A) < cubicRatio ρ := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hBne : B ≠ ⊥ := by
    intro hb
    rw [hb, Representation.BinaryOffender.rank_bot] at hhyper
    omega
  let : IsElementaryAbelian 2 B := (hA.1.2.1.of_le hBA hBne).2
  let C := pCore p G ⊓ centralizer (B : Set G)
  have hCB : ⁅C,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hCp : IsPGroup p C := pCore_isPGroup.to_le inf_le_left
  have hker := fixedSpace_primeGroup_kernel_eq_bot ρ hf hp C B hCp
    (IsElementaryAbelian.isPGroup 2 B) hCB
  have hCstab := le_stabilizer_fixedSpace_of_commutator_eq_bot ρ C B hCB
  have hAC : A ≤ normalizer (C : Set G) := by
    apply (le_inf (le_normalizer_of_normal (H := pCore p G)) ?_).trans
      inf_normalizer_le_normalizer_inf
    exact ((A.le_centralizer.trans (centralizer_le hBA)).trans
      (centralizer_le_normalizer (B : Set G))).trans
        (normalizer_le_normalizer_centralizer B)
  have hDle : ⁅C,A⁆ ≤ C := le_normalizer_iff_commutator_le_left.mp hAC
  have hmoved : subspaceCommutator ρ (fixedSpace ρ B) A ≠ ⊥ := by
    intro hz
    have hfix := (subspaceCommutator_eq_bot_iff ρ (fixedSpace ρ B) A).mp hz
    have hfixApply (a : G) (ha : a ∈ A) (v : V) (hv : v ∈ fixedSpace ρ B) :
        ρ a v = v := hfix hv ⟨a,ha⟩
    have hDK : ⁅C,A⁆ ≤ subspaceKernel ρ (fixedSpace ρ B) C := by
      rw [commutator_le]
      intro c hc a ha
      refine ⟨hDle (commutator_mem_commutator hc ha), ?_⟩
      intro v hv
      simp only [commutatorElement_def, map_mul, Module.End.mul_apply]
      rw [hfixApply a⁻¹ (A.inv_mem ha) v hv,
        hfixApply a ha (ρ c⁻¹ v) ((hCstab (C.inv_mem hc) v).2 hv)]
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply]
    exact hm (le_bot_iff.mp (hDK.trans_eq hker))
  exact ⟨hker, QhatStar.hyperplane_fixedSpace_ratio_drop ρ hA hBA hBne hhyper hmoved⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- Generation by hyperplane centralizers detects a nontrivial action on
the actual odd prime core. -/
theorem exists_moved_primeCore_hyperplane
    {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hm : ⁅pCore p G,A⁆ ≠ ⊥) :
    ∃ B : Subgroup G, B ≤ A ∧ rank B + 1 = rank A ∧
      ⁅pCore p G ⊓ centralizer (B : Set G), A⁆ ≠ ⊥ := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hpne : p ≠ 2 := fun he => (by decide : ¬ Odd (2 : ℕ)) (he ▸ hp)
  have hgen := iSup_hyperplane_centralizer_commutator hpne (pCore p G) A
    pCore_isPGroup (le_normalizer_of_normal (H := pCore p G))
  have hex : ∃ B : Subgroup A, B.index = 2 ∧
      ⁅pCore p G ⊓ centralizer (B.map A.subtype : Set G), A⁆ ≠ ⊥ := by
    by_contra! hn
    apply hm
    rw [← hgen]
    exact le_bot_iff.mp (iSup₂_le fun B hi => (hn B hi).le)
  obtain ⟨B, hi, hn⟩ := hex
  have hB := (IsElementaryAbelian.isPGroup 2 A).to_subgroup B
  obtain ⟨n, hcB⟩ := hB.exists_card_eq
  have hc := B.card_mul_index
  rw [hi, hcB, hA.1.2.1.card_eq_two_pow_rank] at hc
  have hr : n + 1 = rank A := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2 ^ (n + 1) = 2 ^ rank A
    rw [pow_succ]
    exact hc
  refine ⟨B.map A.subtype, map_subtype_le B, ?_, hn⟩
  change Nat.log 2 (Nat.card (B.map A.subtype)) + 1 = rank A
  rw [card_map_of_injective A.subtype_injective, hcB, Nat.log_pow (by decide : 1 < 2)]
  exact hr

/-- The strict hyperplane reduction excludes global cubic ratio at most one
for a noncyclic starred actor moving any odd prime core. -/
theorem QhatStar.one_lt_cubicRatio_of_noncyclic_primeCore_action
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ⁅pCore p G,A⁆ ≠ ⊥) : 1 < cubicRatio ρ := by
  obtain ⟨B, hBA, hh, hn⟩ := exists_moved_primeCore_hyperplane ρ hA hp hm
  obtain ⟨_, _, hIrank, hI, hlt⟩ :=
    source_lemma_D_2_13_hyperplane_restriction ρ hf hA hr hp B hBA hh hn
  have hpos := fixedCodim_pos_of_faithful
    (subspaceImageRepresentation ρ (fixedSpace ρ B))
    (subspaceImageRepresentation_injective ρ (fixedSpace ρ B)) hI.1.1
  apply lt_of_le_of_lt _ hlt
  rw [actionRatio, hIrank, Nat.cast_one, div_one]
  exact_mod_cast hpos

/-- Full D.2.13(4): ratio at most one forces ratio one, prime three and a
cyclic actor. The noncyclic case is excluded by the actual hyperplane
fixed-space action, with no assumed support or configuration conclusion. -/
theorem source_lemma_D_2_13_ratio_le_one
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hm : ⁅pCore p G,A⁆ ≠ ⊥)
    (hq : cubicRatio ρ ≤ 1) :
    cubicRatio ρ = 1 ∧ p = 3 ∧ rank A = 1 ∧ IsCyclic A := by
  have hpos := hA.1.2.1.rank_pos
  have hr : rank A = 1 := by
    by_contra hn
    have hhigh : 1 < rank A := by omega
    exact (not_lt_of_ge hq)
      (QhatStar.one_lt_cubicRatio_of_noncyclic_primeCore_action ρ hf hA hhigh hp hm)
  have hc := source_lemma_D_2_13_cyclic_prime ρ hf hA hr hp hm
  have he : cubicRatio ρ = 1 := hc.2.1.resolve_right (fun h => by
    rw [h] at hq
    norm_num at hq)
  have hcard : Nat.card A = 2 := by rw [hA.1.2.1.card_eq_two_pow_rank, hr, pow_one]
  exact ⟨he, hc.2.2 he, hr, isCyclic_of_prime_card hcard⟩
end CFSG.Quasithin.ChapterD
