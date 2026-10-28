module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.FixedSupplementSeparation
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportPermutation
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.SupportExclusion.Linear
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration

/-!
# Normality and fixed complements of saturated prime supports

The normality and starred-actor separation of the canonical cubic or quintic
support use only the original Core hypotheses. The original ratio
indecomposability additionally makes its odd fixed complement globally fixed,
so restriction to the support preserves the cubic minimum and starred actors.
No full-movement hypothesis is required for this prefix of D.2.23–24,
printed pp.189–190.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
private theorem involution_support (t : G) (ht : orderOf t = 2) :
    subspaceCommutator ρ ⊤ (zpowers t) = LinearMap.range (ρ t - LinearMap.id) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp ha)
    have hi := Finset.mem_range.mp hi
    rw [ht] at hi
    interval_cases i
    · simp
    · exact ⟨v,by simp⟩
  · rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨t,mem_zpowers t,v,Submodule.mem_top,rfl⟩

/-- Core hypotheses give normality and the literal starred support dichotomy. -/
theorem CoreHypotheses.saturated_prime_support_core (h : CoreHypotheses ρ) {k : ℕ}
    (hk : k = 1 ∨ k = 2) (hq : cubicRatio ρ = k)
    (D : Subgroup G) (hDF : D ≤ fittingSubgroup G)
    (hcard : Nat.card D = 2 * k + 1)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 2 * k) :
    D.Normal ∧ ∀ A ∈ QhatStar ρ,
      subspaceCommutator ρ ⊤ D ≤ fixedSpace ρ A ∨ fixedSpace ρ D ≤ fixedSpace ρ A := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ h.faithful
  have hD : D ∈ smallSupportFactors G (Multiplicative V) k := by
    refine ⟨hDF,hcard,?_⟩
    rw [BinaryGroupAction.commutator_card,hdim]
  have hs (A : Subgroup G) (hA : A ∈ QhatStar ρ) (t : G)
      (ht : orderOf t = 2) (he : zpowers t = A) :
      Nat.card (commutatorAction (zpowers t) (Multiplicative V)) = 2 ^ k := by
    have hd : fixedCodim ρ A = k := by
      exact_mod_cast (starred_codimension ρ hA (h.rank_one A hA)).trans hq
    rw [BinaryGroupAction.commutator_card,involution_support ρ t ht,
      ← fixedCodim_zpowers_eq_displacement_rank,he,hd]
  have hN : ⊤ ≤ normalizer (D : Set G) := by
    rw [← h.generated]
    apply sSup_le
    intro A hA
    obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
    rw [← he]
    apply zpowers_le.mpr
    exact smallSupportFactors_normalized_of_displacement_card hk t (hs A hA t ht he) D hD
  let : D.Normal := (normalizer_eq_top_iff.mp (top_unique hN))
  have hodd : Odd (Nat.card D) := by rw [hcard]; exact ⟨k,rfl⟩
  have hp : (Nat.card D).Prime := by rw [hcard]; rcases hk with rfl | rfl <;> decide
  have hfaith : fixingSubgroup G (Set.univ : Set (Multiplicative V)) = ⊥ := by
    apply bot_unique
    intro g hg
    apply eq_of_smul_eq_smul (α := Multiplicative V)
    intro v
    simpa only [one_smul] using ((mem_fixingSubgroup_iff (M := G)).mp hg v (Set.mem_univ v))
  have hdich (A : Subgroup G) (hA : A ∈ QhatStar ρ) :
      subspaceCommutator ρ ⊤ D ≤ fixedSpace ρ A ∨ fixedSpace ρ D ≤ fixedSpace ρ A := by
    obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
    have hti : IsInvolution t := ⟨fun he => by simp [he] at ht,ht ▸ pow_orderOf_eq_one t⟩
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one D hp t hti.2 (hN (mem_top t)) with hc | hi
    · left
      intro v hv
      rw [← he,mem_fixedSpace_zpowers_iff]
      have hh := smallSupportFactor_support_fixed_of_centralizes hk hD t hti.2 hc
        (Multiplicative.ofAdd v) (by rw [BinaryGroupAction.commutator_eq]; exact hv)
      exact congrArg Multiplicative.toAdd hh
    · right
      have hsq : Nat.card (commutatorAction D (Multiplicative V)) =
          Nat.card (commutatorAction (zpowers t) (Multiplicative V)) ^ 2 := by
        rw [hD.2.2,hs A hA t ht he,← pow_mul,Nat.mul_comm k 2]
      have hh := (invertedOddSubgroup_full_support D hodd t hti hi hsq hfaith).2.1
      intro v hv
      rw [← he,mem_fixedSpace_zpowers_iff]
      exact congrArg Multiplicative.toAdd (hh (Multiplicative.ofAdd v) hv)
  exact ⟨inferInstance,hdich⟩

/-- Under ratio indecomposability, the same literal odd fixed complement is
fixed by the whole original group. -/
theorem CoreHypotheses.saturated_prime_fixed_supplement (h : CoreHypotheses ρ)
    (hind : IsRatioIndecomposable ρ) {k : ℕ}
    (hk : k = 1 ∨ k = 2) (hq : cubicRatio ρ = k)
    (D : Subgroup G) (hDF : D ≤ fittingSubgroup G)
    (hcard : Nat.card D = 2 * k + 1)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 2 * k) :
    D.Normal ∧ fixedSpace ρ D ≤ fixedSpace ρ ⊤ ∧
      subspaceCommutator ρ ⊤ D ⊔ fixedSpace ρ ⊤ = ⊤ := by
  obtain ⟨hn,hdich⟩ := h.saturated_prime_support_core ρ hk hq D hDF hcard hdim
  let : D.Normal := hn
  have hN : ⊤ ≤ normalizer (D : Set G) := by rw [normalizer_eq_top]
  have hodd : Odd (Nat.card D) := by rw [hcard]; exact ⟨k,rfl⟩
  have hcompl := (ElementaryCore.SupportExclusion.moved_split ρ D hodd).symm
  have hne : subspaceCommutator ρ ⊤ D ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hdim
    rcases hk with hk | hk <;> omega
  have hnot : ¬ subspaceCommutator ρ ⊤ D ≤ fixedSpace ρ ⊤ := by
    intro he
    exact hne (hcompl.disjoint.eq_bot_of_le
      (he.trans (fixedSpace_antitone ρ (le_top : D ≤ ⊤))))
  have hW : ∀ g w, w ∈ subspaceCommutator ρ ⊤ D → ρ g w ∈ subspaceCommutator ρ ⊤ D := by
    intro g w hw
    exact (subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hN (mem_top g) w).2 hw
  have hC : ∀ g w, w ∈ fixedSpace ρ D → ρ g w ∈ fixedSpace ρ D := by
    intro g w hw
    exact (fixedSpace_invariant_normalizer ρ hN (mem_top g) w).2 hw
  have hf := complement_fixed_of_starred_dichotomy ρ h.generated hind _ _
    hcompl hW hC hnot hdich
  refine ⟨hn,hf,top_unique ?_⟩
  calc
    ⊤ = subspaceCommutator ρ ⊤ D ⊔ fixedSpace ρ D := hcompl.sup_eq_top.symm
    _ ≤ subspaceCommutator ρ ⊤ D ⊔ fixedSpace ρ ⊤ := sup_le_sup_left hf _

/-- Restricting to the literal saturated support preserves both the minimum
and the original starred actors after removing its fixed supplement. -/
theorem CoreHypotheses.saturated_prime_fixed_transport (h : CoreHypotheses ρ)
    (hind : IsRatioIndecomposable ρ) {k : ℕ}
    (hk : k = 1 ∨ k = 2) (hq : cubicRatio ρ = k)
    (D : Subgroup G) (hDF : D ≤ fittingSubgroup G)
    (hcard : Nat.card D = 2 * k + 1)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 2 * k)
    (W : Subrepresentation ρ) (hW : W.toSubmodule = subspaceCommutator ρ ⊤ D) :
    cubicRatio W.toRepresentation = cubicRatio ρ ∧
      ∀ A : Subgroup G, A ∈ QhatStar W.toRepresentation ↔ A ∈ QhatStar ρ := by
  obtain ⟨_,_,hspan⟩ := h.saturated_prime_fixed_supplement ρ hind hk hq D hDF hcard hdim
  exact RatioDecomposition.fixed_complement_transport ρ W (hW ▸ hspan)

/-- The original quintic-core commutator is normal and separates all starred
actors before any full-movement assumption or restriction of the action. -/
theorem CoreHypotheses.five_core_support_core (h : CoreHypotheses ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) :
    cubicRatio ρ = 2 ∧ (⁅pCore 5 G,A⁆ : Subgroup G).Normal ∧
      Nat.card (⁅pCore 5 G,A⁆ : Subgroup G) = 5 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore 5 G,A⁆) = 4 ∧
      ∀ B ∈ QhatStar ρ,
        subspaceCommutator ρ ⊤ ⁅pCore 5 G,A⁆ ≤ fixedSpace ρ B ∨
          fixedSpace ρ ⁅pCore 5 G,A⁆ ≤ fixedSpace ρ B := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hq,hc,_,hd,_⟩ := source_lemma_D_2_13_cyclic_five ρ h.faithful hA
    (h.rank_one A hA) hm
  have hDF : ⁅pCore 5 G,A⁆ ≤ fittingSubgroup G :=
    (commutator_le_left (pCore 5 G) A).trans (pCore_le_fitting G 5)
  obtain ⟨hn,hdich⟩ := h.saturated_prime_support_core ρ (k := 2) (Or.inr rfl)
    (by simpa using hq) ⁅pCore 5 G,A⁆ hDF (by simpa using hc) (by simpa using hd)
  exact ⟨hq,hn,hc,hd,hdich⟩

end CFSG.Quasithin.ChapterD.CyclicSource
