module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.Defs
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Dimension and minimality calculations for the reduced configurations

The literal support sum identifies fixed vectors component by component:
invariance and injectivity of addition force each component of a fixed vector
to be fixed. Rank-nullity then adds the fixed codimensions. The corresponding
group multiplication is an actual isomorphism, with its evaluation formula.

For an order-four starred actor, inclusion minimality is strict on every
order-two subactor. Thus a subactor moving at most two dimensions excludes
fixed codimension four. The hyperplane restriction theorem supplies the strict
lower bound on the ratio once the fixed space is noncentralized. In dimension
at most five these facts force codimension three and ratio three halves.

These are intermediate calculations for Aschbacher--Smith D.2.14, printed
pp.186--187. Construction of the support factors and the invariant-line
case split is not asserted here.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender
open scoped ENNReal
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The multiplication of the specified factors is a group isomorphism. -/
noncomputable def SupportFactors.productEquiv {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) (hP : IsElementaryAbelian 3 P) :
    ((i : Fin s) → d.factor i) ≃* P := by
  let : IsElementaryAbelian 3 P := hP
  let : CommGroup P := IsMulCommutative.instCommGroup
  let f : ((i : Fin s) → d.factor i) →* P :=
    { toFun := fun x => (List.ofFn fun i => (x i : P)).prod
      map_one' := by simp
      map_mul' := by intros; simp [Fin.prod_ofFn, Finset.prod_mul_distrib] }
  exact MulEquiv.ofBijective f d.multiply_bijective

/-- The isomorphism uses the original factor inclusions and their product. -/
theorem SupportFactors.productEquiv_apply {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) (hP : IsElementaryAbelian 3 P)
    (x : (i : Fin s) → d.factor i) :
    d.productEquiv ρ hP x = (List.ofFn fun i => (x i : P)).prod := rfl

private def sumMap {n : ℕ} (U : Fin n → Submodule (ZMod 2) V) :
    ((i : Fin n) → U i) →ₗ[ZMod 2] V where
  toFun v := ∑ i, (v i : V)
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

private theorem finrank_eq_sum_of_bijective [FiniteDimensional (ZMod 2) V]
    {n : ℕ} (U : Fin n → Submodule (ZMod 2) V)
    (h : Function.Bijective (sumMap U)) :
    Module.finrank (ZMod 2) V = ∑ i, Module.finrank (ZMod 2) (U i) := by
  rw [← (LinearEquiv.ofBijective (sumMap U) h).finrank_eq,
    Module.finrank_pi_fintype]

private def fixedSumMap {n : ℕ} (U : Fin n → Submodule (ZMod 2) V) (A : Subgroup G) :
    ((i : Fin n) → (U i ⊓ fixedSpace ρ A : Submodule (ZMod 2) V)) →ₗ[ZMod 2]
      fixedSpace ρ A where
  toFun v := ⟨∑ i, (v i : V), (fixedSpace ρ A).sum_mem (fun i _ => (v i).property.2)⟩
  map_add' v w := by ext; simp [Finset.sum_add_distrib]
  map_smul' c v := by ext; simp [Finset.smul_sum]

private theorem fixedSumMap_bijective {n : ℕ} (U : Fin n → Submodule (ZMod 2) V)
    (h : Function.Bijective (sumMap U)) (A : Subgroup G)
    (hstable : ∀ i, A ≤ subspaceStabilizer ρ (U i)) :
    Function.Bijective (fixedSumMap ρ U A) := by
  constructor
  · intro v w heq
    have heq' : sumMap U (fun i => ⟨v i, (v i).property.1⟩) =
        sumMap U (fun i => ⟨w i, (w i).property.1⟩) := congrArg Subtype.val heq
    have hvw := h.1 heq'
    funext i
    exact Subtype.ext (congrArg (fun x => ((x i : U i) : V)) hvw)
  · intro v
    obtain ⟨w, hw⟩ := h.2 v.val
    have hfix (i : Fin n) : (w i : V) ∈ fixedSpace ρ A := by
      intro a
      let w' : (j : Fin n) → U j := fun j =>
        ⟨ρ a (w j), (hstable j a.property (w j)).mpr (w j).property⟩
      have heq : sumMap U w' = sumMap U w := by
        change (∑ j, ρ a (w j)) = ∑ j, (w j : V)
        rw [← map_sum]
        change ρ a (sumMap U w) = sumMap U w
        rw [hw]
        exact v.property a
      exact congrArg (fun x => ((x i : U i) : V)) (h.1 heq)
    refine ⟨fun i => ⟨w i, (w i).property, hfix i⟩, ?_⟩
    exact Subtype.ext hw

private theorem finrank_fixedSpace_eq_sum [FiniteDimensional (ZMod 2) V]
    {n : ℕ} (U : Fin n → Submodule (ZMod 2) V)
    (h : Function.Bijective (sumMap U)) (A : Subgroup G)
    (hstable : ∀ i, A ≤ subspaceStabilizer ρ (U i)) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) =
      ∑ i, Module.finrank (ZMod 2) (U i ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) := by
  rw [← (LinearEquiv.ofBijective (fixedSumMap ρ U A)
    (fixedSumMap_bijective ρ U h A hstable)).finrank_eq,
    Module.finrank_pi_fintype]

/-- A direct sum of `s` binary planes has dimension `2s`. -/
theorem SupportFactors.finrank_eq [FiniteDimensional (ZMod 2) V]
    {P : Subgroup G} {s : ℕ} (d : SupportFactors ρ P s) :
    Module.finrank (ZMod 2) V = 2 * s := by
  rw [finrank_eq_sum_of_bijective (fun i => subspaceCommutator ρ ⊤ (d.ambient i))
    d.add_bijective]
  trans ∑ _i : Fin s, (2 : ℕ)
  · exact Finset.sum_congr rfl (fun i _ => d.support_dim i)
  · simp [Nat.mul_comm]

/-- If each invariant support has one fixed dimension, their direct sum has
fixed codimension `s` in the original representation. -/
theorem SupportFactors.fixedCodim_eq_of_fixed_lines [FiniteDimensional (ZMod 2) V]
    {P : Subgroup G} {s : ℕ} (d : SupportFactors ρ P s) (A : Subgroup G)
    (hstable : ∀ i, A ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ (d.ambient i)))
    (hlines : ∀ i, Module.finrank (ZMod 2)
      (subspaceCommutator ρ ⊤ (d.ambient i) ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) = 1) :
    fixedCodim ρ A = s := by
  have hf := finrank_fixedSpace_eq_sum ρ
    (fun i => subspaceCommutator ρ ⊤ (d.ambient i)) d.add_bijective A hstable
  simp only [hlines, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at hf
  have hd := fixedCodim_add_finrank ρ A
  have hv := d.finrank_eq ρ
  omega

/-- Coprime averaging gives the literal fixed/moved splitting used on each line. -/
theorem odd_fixed_moved_complement [Finite G] {Z : Subgroup G}
    (hZ : Odd (Nat.card Z)) :
    IsCompl (subspaceCommutator ρ ⊤ Z) (fixedSpace ρ Z) := by
  have hs := Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hZ
  have he : Representation.RegularCyclicNormalClosure.displacementSpan ρ Z ⊤ =
      subspaceCommutator ρ ⊤ Z := by
    unfold Representation.RegularCyclicNormalClosure.displacementSpan subspaceCommutator
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq, eq_comm]
  rw [he] at hs
  exact hs.symm

/-- The reduced module has no nonzero vector fixed by the whole odd core. -/
theorem Reduced.fixedSpace_core_eq_bot [Finite G]
    {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s) : fixedSpace ρ P = ⊥ := by
  have hs := odd_fixed_moved_complement ρ (h.card_core ▸ (by decide : Odd 3).pow)
  simpa only [h.moved, top_inf_eq] using hs.disjoint.eq_bot

/-- The order-four actor has binary rank two. -/
theorem Reduced.actor_rank {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s) :
    rank A = 2 := by
  simp only [rank, h.card_actor]
  decide

/-- The source's ratio bound gives the four-dimensional displacement budget. -/
theorem Reduced.fixedCodim_le_four [Finite G] {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) : fixedCodim ρ A ≤ 4 := by
  have hb := (actionRatio_le_nat_iff ρ h.starred.1.2.1 2).mp
    (h.starred.1.2.2.2.trans_le h.starred.1.1)
  simpa only [h.actor_rank ρ] using hb

/-- Fixed codimension three identifies the attained global cubic minimum. -/
theorem Reduced.cubicRatio_eq_of_fixedCodim_three {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hd : fixedCodim ρ A = 3) : cubicRatio ρ = 3 / 2 := by
  rw [← h.starred.1.2.2.2, actionRatio, hd, h.actor_rank ρ]
  norm_num

/-- The nontrivial hyperplane image has integral positive ratio strictly below
the original one; hence the original ratio is greater than one. -/
theorem Reduced.one_lt_ratio_of_moved_hyperplane [Finite G]
    [FiniteDimensional (ZMod 2) V] {P A B : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hBA : B ≤ A) (hrB : rank B = 1)
    (hn : subspaceCommutator ρ (fixedSpace ρ B) A ≠ ⊥) :
    1 < cubicRatio ρ := by
  have hB : B ≠ ⊥ := by
    intro he
    rw [he, Representation.BinaryOffender.rank_bot] at hrB
    omega
  obtain ⟨_, hr, hQ, hlt⟩ := QhatStar.hyperplane_fixedSpace_ratio_drop ρ h.starred
    hBA hB (by rw [hrB, h.actor_rank ρ]) hn
  have hpos := fixedCodim_pos_of_faithful (subspaceImageRepresentation ρ (fixedSpace ρ B))
    (subspaceImageRepresentation_injective ρ (fixedSpace ρ B)) hQ.1.1
  rw [actionRatio, hr, Nat.cast_one, div_one] at hlt
  exact lt_of_le_of_lt (by exact_mod_cast (Nat.succ_le_iff.mpr hpos)) hlt

/-- The two remaining numerical possibilities in D.2.14's equation (!!). -/
theorem Reduced.codimension_cases [Finite G] {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hlow : 1 < cubicRatio ρ) :
    fixedCodim ρ A = 3 ∨ fixedCodim ρ A = 4 := by
  have hup := h.fixedCodim_le_four ρ
  rw [← h.starred.1.2.2.2, actionRatio, h.actor_rank ρ] at hlow
  have hl : (2 : ℝ≥0∞) < fixedCodim ρ A := by
    simpa using (ENNReal.lt_div_iff_mul_lt (by simp) (by simp)).mp hlow
  have hl' : 2 < fixedCodim ρ A := by exact_mod_cast hl
  omega

/-- Inclusion minimality gives a strict integral inequality on each actor line. -/
theorem Reduced.strict_subactor_bound [Finite G] {P A B : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hBA : B ≤ A) (hB : Nat.card B = 2) :
    fixedCodim ρ A < 2 * fixedCodim ρ B := by
  have hne : B ≠ ⊥ := by intro he; rw [he, Subgroup.card_bot] at hB; omega
  have hlt : B < A := lt_of_le_of_ne hBA (by
    intro he; rw [he, h.card_actor] at hB; omega)
  have hr : rank B = 1 := by simp only [rank, hB]; decide
  have hc := QhatStar.ratio_lt_of_lt ρ h.starred hlt hne
  rw [actionRatio, actionRatio, h.actor_rank ρ, hr, Nat.cast_one, div_one] at hc
  have hc' : (fixedCodim ρ A : ℝ≥0∞) < (fixedCodim ρ B : ℝ≥0∞) * 2 :=
    (ENNReal.div_lt_iff (by norm_num) (by norm_num)).mp hc
  have hc'' : fixedCodim ρ A < fixedCodim ρ B * 2 := by exact_mod_cast hc'
  omega

/-- The equal-ratio order-two actor in the proper four-support branch is impossible. -/
theorem Reduced.no_codim_four_with_small_subactor [Finite G]
    {P A B : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hBA : B ≤ A) (hB : Nat.card B = 2) (hb : fixedCodim ρ B ≤ 2) :
    fixedCodim ρ A ≠ 4 := by
  have hi := h.strict_subactor_bound ρ hBA hB
  omega

/-- The involution half-dimension bound rules out codimension four in small degree. -/
theorem Reduced.fixedCodim_le_three_of_finrank_le_five [Finite G]
    [FiniteDimensional (ZMod 2) V] {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hdim : Module.finrank (ZMod 2) V ≤ 5) :
    fixedCodim ρ A ≤ 3 := by
  obtain ⟨a, ha, hane⟩ := (Subgroup.nontrivial_iff_exists_ne_one A).mp
    ((Subgroup.nontrivial_iff_ne_bot A).mpr h.starred.1.2.1.1)
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hane
  have hbound := (involution_actor_rank_and_fixedCodim ρ a ha2).2.2.2
  have hi := h.strict_subactor_bound ρ (Subgroup.zpowers_le.mpr ha)
    (by simpa only [Nat.card_zpowers] using ha2)
  omega

/-- In small degree the genuine global cubic minimum is three halves. -/
theorem Reduced.small_dimension_ratio [Finite G] [FiniteDimensional (ZMod 2) V]
    {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hlow : 1 < cubicRatio ρ) (hdim : Module.finrank (ZMod 2) V ≤ 5) :
    fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  have hcases := h.codimension_cases ρ hlow
  have hup := h.fixedCodim_le_three_of_finrank_le_five ρ hdim
  have he : fixedCodim ρ A = 3 := by omega
  exact ⟨he, h.cubicRatio_eq_of_fixedCodim_three ρ he⟩

/-- A cubic minimum greater than one excludes transvections in the whole group. -/
theorem no_transvections_of_one_lt_ratio [Finite G] [FiniteDimensional (ZMod 2) V]
    (hlow : 1 < cubicRatio ρ) (t : G) (ht : orderOf t = 2) :
    2 ≤ fixedCodim ρ (Subgroup.zpowers t) := by
  obtain ⟨he, hr, hq, _⟩ := involution_actor_rank_and_fixedCodim ρ t ht
  have hb : cubicRatio ρ ≤ actionRatio ρ (Subgroup.zpowers t) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨he, isCubic_of_isQuadratic hq⟩ le_rfl)
  rw [actionRatio, hr, Nat.cast_one, div_one] at hb
  have hlt : (1 : ℝ≥0∞) < fixedCodim ρ (Subgroup.zpowers t) := hlow.trans_le hb
  have hlt' : 1 < fixedCodim ρ (Subgroup.zpowers t) := by exact_mod_cast hlt
  omega

end CFSG.Quasithin.ChapterD.FittingConfigurations
