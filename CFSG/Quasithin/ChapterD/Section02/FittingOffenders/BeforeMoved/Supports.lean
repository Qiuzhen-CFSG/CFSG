module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceAssembly
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalTransport
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.ThreePlaneSplitting.Factors
public import Theory.GroupAction.NineSixteenFixedFactors
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-! The finite support argument before removing the Fitting fixed complement.
Only the four-unit codimension budget and its equality-case minimality pass
to the moved module. No minimum-ratio premise is imposed on that module.
Source: Aschbacher–Smith D.2.14, printed pp.186–187; the pre-moved use in
15.1.2, printed p.1084, retains the normalized two-plane FF alternative. -/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.BeforeMoved
open Subgroup Representation.BinaryOffender FittingConfigurations Representation.BinaryGroupAction
open scoped IsMulCommutative
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Linear and elementary-core data on the moved module. The last two clauses
are inherited from the original starred actor, including the equality case. -/
structure Input (P A : Subgroup G) (s : ℕ) : Prop where
  faithful : Function.Injective ρ
  normal : P.Normal
  elementary : IsElementaryAbelian 3 P
  card_core : Nat.card P = 3 ^ s
  rank_cases : s = 2 ∨ s = 3
  card_actor : Nat.card A = 4
  actor : IsElementaryTwo A
  generated : P ⊔ A = ⊤
  actor_faithful : A ⊓ centralizer (P : Set G) = ⊥
  common_centralizer : P ⊓ centralizer (A : Set G) = ⊥
  core_commutator : ⁅P,A⁆ = P
  moved : subspaceCommutator ρ ⊤ P = ⊤
  hyperplane_support : ElementaryCore.HyperplaneSupport ρ P A
  codim_bound : fixedCodim ρ A ≤ 4
  strict_four : ∀ B : Subgroup G, B ≤ A → Nat.card B = 2 →
    fixedCodim ρ A = 4 → 2 < fixedCodim ρ B

omit [Finite G] in
private theorem Input.fixedCodim_le_four {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) : fixedCodim ρ A ≤ 4 := h.codim_bound

omit [Finite G] in
private theorem Input.no_codim_four_with_small_subactor
    {P A B : Subgroup G} {s : ℕ} (h : Input ρ P A s)
    (hBA : B ≤ A) (hB : Nat.card B = 2) (hb : fixedCodim ρ B ≤ 2) :
    fixedCodim ρ A ≠ 4 := by
  intro he
  have hh := h.strict_four B hBA hB he
  omega

private theorem Input.fixedSpace_core_eq_bot
    {P A : Subgroup G} {s : ℕ} (h : Input ρ P A s) : fixedSpace ρ P = ⊥ := by
  have hs := odd_fixed_moved_complement ρ (h.card_core ▸ (by decide : Odd 3).pow)
  simpa only [h.moved, top_inf_eq] using hs.disjoint.eq_bot


private theorem Input.invariant_line_hyperplane {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z) :
    let B := A ⊓ centralizer (Z : Set G)
    Nat.card B = 2 ∧ rank B = 1 ∧ P ⊓ centralizer (B : Set G) = Z ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B) Z) = 2 :=
  ElementaryCore.line_fixed_support ρ P A Z h.card_actor hZ.1 hZ.2.1 hZ.2.2
    h.common_centralizer h.hyperplane_support


private theorem Input.invariant_line_commutator {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z) : ⁅Z, A⁆ = Z := by
  have hfix : Z ⊓ centralizer (A : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hZ.1).trans_eq h.common_centralizer)
  exact ElementaryCore.commutator_eq Z A
    (IsPGroup.of_card (n := 1) (by simpa using hZ.2.1))
    h.card_actor hZ.2.2 hfix


private theorem moved_on_invariant_eq_inf (D : Submodule (ZMod 2) V) (Z : Subgroup G)
    (hZ : Odd (Nat.card Z)) (hD : Z ≤ subspaceStabilizer ρ D) :
    subspaceCommutator ρ D Z = D ⊓ subspaceCommutator ρ ⊤ Z := by
  classical
  let := Fintype.ofFinite Z
  have hcard : (Fintype.card Z : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hZ
    rw [← Nat.card_eq_fintype_card, hk]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_add]
  let N : V →ₗ[ZMod 2] V := ∑ z : Z, ρ z
  have hN (v : V) : N v = ∑ z : Z, ρ z v := LinearMap.sum_apply _ _ _
  have hfixed (v : V) : N v ∈ fixedSpace ρ Z := by
    intro z
    change ρ (z : G) (N v) = N v
    simp only [hN, map_sum, ← Module.End.mul_apply, ← map_mul]
    exact (Group.mulLeft_bijective z).sum_comp (fun y : Z => ρ y v)
  have hdiff (v : V) (hv : v ∈ D) : N v - v ∈ subspaceCommutator ρ D Z := by
    have hm : (∑ z : Z, (ρ z v - v)) ∈ subspaceCommutator ρ D Z :=
      Submodule.sum_mem _ fun z _ => Submodule.subset_span ⟨z, z.property, v, hv, rfl⟩
    rw [Finset.sum_sub_distrib, ← hN, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard, one_smul] at hm
    exact hm
  have hm := subspaceCommutator_mono_left ρ (show D ≤ ⊤ from le_top) Z
  refine le_antisymm (le_inf (subspaceCommutator_le_of_invariant ρ hD) hm) ?_
  intro v hv
  have hNu : N v ∈ subspaceCommutator ρ ⊤ Z := by
    simpa only [sub_add_cancel] using
      (subspaceCommutator ρ ⊤ Z).add_mem (hm (hdiff v hv.1)) hv.2
  have hz : N v = 0 := (odd_fixed_moved_complement ρ hZ).disjoint.le_bot ⟨hNu, hfixed v⟩
  simpa only [hz, zero_sub, neg_neg] using (subspaceCommutator ρ D Z).neg_mem (hdiff v hv.1)

/-- The hyperplane's moved space is the fixed space on the original line support. -/
private theorem Input.invariant_line_fixed_support {P A Z : Subgroup G} {s : ℕ}
    (_h : Input ρ P A s) (hZ : IsInvariantLine P A Z) :
    let B := A ⊓ centralizer (Z : Set G)
    subspaceCommutator ρ (fixedSpace ρ B) Z =
      subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B := by
  dsimp only
  rw [moved_on_invariant_eq_inf ρ _ Z (hZ.2.1 ▸ (by decide : Odd 3))
    (fixedSpace_invariant_normalizer ρ
      ((le_centralizer_iff.mp (show A ⊓ centralizer (Z : Set G) ≤ centralizer (Z : Set G)
        from inf_le_right)).trans (Subgroup.centralizer_le_normalizer _))), inf_comm]

private def onSubgroup (D : Submodule (ZMod 2) V) (B : Subgroup G)
    (hD : B ≤ subspaceStabilizer ρ D) : Representation (ZMod 2) B D :=
  (stabilizerRepresentation ρ D).comp (inclusion hD)

private def fixedEquiv (D : Submodule (ZMod 2) V) (B : Subgroup G)
    (hD : B ≤ subspaceStabilizer ρ D) :
    fixedSpace (onSubgroup ρ D B hD) ⊤ ≃ₗ[ZMod 2] (D ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) where
  toFun v := ⟨v.val.val, v.val.property, fun b => congrArg Subtype.val (v.property ⟨b, mem_top _⟩)⟩
  invFun v := ⟨⟨v.val, v.property.1⟩, fun b => Subtype.ext (v.property.2 b.val)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem dimension_le_twice_fixed [FiniteDimensional (ZMod 2) V]
    (D : Submodule (ZMod 2) V) (B : Subgroup G)
    (hD : B ≤ subspaceStabilizer ρ D) (hc : Nat.card B = 2) :
    Module.finrank (ZMod 2) D ≤
      2 * Module.finrank (ZMod 2) (D ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) := by
  obtain ⟨b, hb, _⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hc
  have hb2 : orderOf b = 2 := orderOf_eq_prime
    (by simpa only [hc] using (pow_card_eq_one' : b ^ Nat.card B = 1)) hb
  have hgen : zpowers b = ⊤ := eq_of_le_of_card_ge le_top
    (by simp only [Nat.card_zpowers, hb2, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv, hc]; exact le_rfl)
  let σ := onSubgroup ρ D B hD
  have hi := (involution_actor_rank_and_fixedCodim σ b hb2).2.2.2
  have hs := fixedCodim_add_finrank σ ⊤
  rw [hgen] at hi
  rw [(fixedEquiv ρ D B hD).finrank_eq] at hs
  omega

private theorem support_dimension_ne_three [FiniteDimensional (ZMod 2) V]
    (Z : Subgroup G) (hc : Nat.card Z = 3) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) ≠ 3 := by
  let D := subspaceCommutator ρ ⊤ Z
  let : Finite D := Module.finite_of_finite (ZMod 2)
  have hD : Z ≤ subspaceStabilizer ρ D := subspaceCommutator_invariant ρ ⊤ Z
  let σ := onSubgroup ρ D Z hD
  let := Representation.BinaryGroupAction.action σ
  have hf : fixedSpace σ (⊤ : Subgroup Z) = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    apply Subtype.ext
    exact (odd_fixed_moved_complement ρ (hc ▸ (by decide : Odd 3))).disjoint.le_bot
      ⟨v.property, fun z => congrArg Subtype.val (hv ⟨z, mem_top _⟩)⟩
  have hp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hc)
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm := hp.card_modEq_card_fixedPoints (Multiplicative D)
  have hfc : Nat.card (MulAction.fixedPoints Z (Multiplicative D)) = 1 := by
    have he : MulAction.fixedPoints Z (Multiplicative D) ≃ fixedSpace σ (⊤ : Subgroup Z) :=
      { toFun v := ⟨v.val.toAdd, fun z => congrArg Multiplicative.toAdd (v.property z.val)⟩
        invFun v := ⟨Multiplicative.ofAdd v.val, fun z => congrArg Multiplicative.ofAdd (v.property ⟨z, mem_top _⟩)⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [Nat.card_congr he, hf]
    simp
  intro hd
  have hdcard : Nat.card (Multiplicative D) = 8 := by
    rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, hd]
    rfl
  rw [hdcard, hfc] at hm
  norm_num [Nat.ModEq] at hm

/-- The actual hyperplane hypotheses bound every invariant-line support by two or four. -/
private theorem Input.invariant_line_dimension [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Input ρ P A s)
    (hZ : IsInvariantLine P A Z) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 2 ∨
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4 := by
  let B := A ⊓ centralizer (Z : Set G)
  have hc := h.invariant_line_hyperplane ρ hZ
  have hd : Module.finrank (ZMod 2)
      (subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) = 2 := by
    rw [← h.invariant_line_fixed_support ρ hZ]
    exact hc.2.2.2
  have hs : B ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ Z) :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
      (inf_le_left.trans hZ.2.2)
  have hu := dimension_le_twice_fixed ρ (subspaceCommutator ρ ⊤ Z) B hs hc.1
  have hl := Submodule.finrank_mono
    (show subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B ≤ subspaceCommutator ρ ⊤ Z from inf_le_left)
  have hn := support_dimension_ne_three ρ Z hZ.2.1
  omega

omit [Finite G] in
private theorem plane_fixed_dimension [FiniteDimensional (ZMod 2) V]
    (D : Submodule (ZMod 2) V) (A : Subgroup G) (hp : IsPGroup 2 A)
    (hs : A ≤ subspaceStabilizer ρ D) (hd : Module.finrank (ZMod 2) D = 2)
    (hn : ¬ D ≤ fixedSpace ρ A) :
    Module.finrank (ZMod 2) (D ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) = 1 := by
  let : Finite D := Module.finite_of_finite (ZMod 2)
  let σ := onSubgroup ρ D A hs
  let := Representation.BinaryGroupAction.action σ
  have hcard : Nat.card (Multiplicative D) = 4 := by
    rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, hd]
    rfl
  obtain ⟨v, hv, hvn⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := Multiplicative D) (hcard ▸ (by decide : 2 ∣ 4))
    (a := 1) (by intro a; exact smul_one a)
  have hpos : Module.finrank (ZMod 2)
      (D ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) ≠ 0 := by
    intro he
    have hz := Submodule.finrank_eq_zero.mp he
    have hf : (v.toAdd : V) ∈ D ⊓ fixedSpace ρ A := by
      refine ⟨v.toAdd.property, fun a => ?_⟩
      exact congrArg (fun x : Multiplicative D => (x.toAdd : V)) (hv a)
    have hzv : (v.toAdd : V) = 0 := hz.le hf
    apply hvn
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hzv.symm
  have hlt : D ⊓ fixedSpace ρ A < D := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hn (he ▸ (inf_le_right : D ⊓ fixedSpace ρ A ≤ fixedSpace ρ A)))
  have hb := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-- Every invariant-line support has exactly one common A-fixed dimension.
The two-dimensional hyperplane fixed support is A-invariant and is not
centralized by A, because [Z,A]=Z. A two-group acting nontrivially on a
binary plane has a fixed line. -/
private theorem Input.invariant_line_fixed_dimension [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Input ρ P A s)
    (hZ : IsInvariantLine P A Z) :
    Module.finrank (ZMod 2)
      (subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) = 1 := by
  let B := A ⊓ centralizer (Z : Set G)
  let D := subspaceCommutator ρ (fixedSpace ρ B) Z
  have hd : Module.finrank (ZMod 2) D = 2 := (h.invariant_line_hyperplane ρ hZ).2.2.2
  have hs : A ≤ subspaceStabilizer ρ D := subspaceCommutator_invariant_normalizer ρ
    (fixedSpace_subactor_stabilized ρ h.actor inf_le_left) hZ.2.2
  have hn : ¬ D ≤ fixedSpace ρ A := by
    intro hf
    have hz := le_fixedSpace_commutator_of_invariant ρ
      (subspaceCommutator_invariant ρ (fixedSpace ρ B) Z) hf
    rw [h.invariant_line_commutator ρ hZ] at hz
    have hzero : D = ⊥ := le_bot_iff.mp (by
      intro v hv
      exact (odd_fixed_moved_complement ρ (hZ.2.1 ▸ (by decide : Odd 3))).disjoint.le_bot
        ⟨subspaceCommutator_mono_left ρ le_top Z hv, hz hv⟩)
    rw [hzero, finrank_bot] at hd
    omega
  let : IsElementaryAbelian 2 A := h.actor.2
  have he := plane_fixed_dimension ρ D A (IsElementaryAbelian.isPGroup 2 A) hs hd hn
  have hD : D = subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B :=
    h.invariant_line_fixed_support ρ hZ
  rw [hD, inf_assoc, inf_eq_right.mpr (fixedSpace_antitone ρ (show B ≤ A from inf_le_left))] at he
  exact he

omit [Finite G] in
/-- Elementary-core centrality makes an A-invariant line normal in the whole local group. -/
private theorem Input.invariant_line_normalizer {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z) :
    (⊤ : Subgroup G) ≤ normalizer (Z : Set G) := by
  let : IsElementaryAbelian 3 P := h.elementary
  have hp : P ≤ centralizer (Z : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hZ.1)
  rw [← h.generated]
  exact sup_le (hp.trans (Subgroup.centralizer_le_normalizer _)) hZ.2.2

omit [Finite G] in
/-- Both original summands of the invariant-line splitting are local-group invariant. -/
private theorem Input.invariant_line_stable {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z) :
    (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ Z) ∧
      (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (fixedSpace ρ Z) :=
  ⟨subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
    (h.invariant_line_normalizer ρ hZ),
    fixedSpace_invariant_normalizer ρ (h.invariant_line_normalizer ρ hZ)⟩

/-- The fixed complement is still generated by the original odd core's displacements. -/
private theorem Input.invariant_line_remainder_moved {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z) :
    subspaceCommutator ρ (fixedSpace ρ Z) P = fixedSpace ρ Z := by
  rw [moved_on_invariant_eq_inf ρ _ P (h.card_core ▸ (by decide : Odd 3).pow)
    (le_top.trans (h.invariant_line_stable ρ hZ).2), h.moved, inf_top_eq]

omit [Finite G] in
private theorem fixedSpace_split (U W : Submodule (ZMod 2) V) (A : Subgroup G)
    (hc : IsCompl U W) (hU : A ≤ subspaceStabilizer ρ U)
    (hW : A ≤ subspaceStabilizer ρ W) :
    (U ⊓ fixedSpace ρ A) ⊔ (W ⊓ fixedSpace ρ A) = fixedSpace ρ A := by
  refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ W by rw [hc.sup_eq_top]; trivial)
  have he (a : A) : (⟨ρ a u, (hU a.property u).2 hu⟩ : U) = ⟨u, hu⟩ ∧
      (⟨ρ a w, (hW a.property w).2 hw⟩ : W) = ⟨w, hw⟩ := by
    have hh := (U.prodEquivOfIsCompl W hc).injective
      (show (U.prodEquivOfIsCompl W hc)
          (⟨ρ a u, (hU a.property u).2 hu⟩, ⟨ρ a w, (hW a.property w).2 hw⟩) =
        (U.prodEquivOfIsCompl W hc) (⟨u, hu⟩, ⟨w, hw⟩) from
          (map_add (ρ a) u w).symm.trans (hv a))
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  exact Submodule.mem_sup.mpr ⟨u, ⟨hu, fun a => congrArg Subtype.val (he a).1⟩,
    w, ⟨hw, fun a => congrArg Subtype.val (he a).2⟩, rfl⟩

/-- Fixed codimensions add on the original fixed/moved splitting, for every
subgroup of the local group and its literal images on the two summands. -/
private theorem Input.invariant_line_codimension_split [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Input ρ P A s)
    (hZ : IsInvariantLine P A Z) (B : Subgroup G) :
    fixedCodim ρ B =
      fixedCodim (subspaceImageRepresentation ρ (subspaceCommutator ρ ⊤ Z))
        (restrictedSubgroup ρ (subspaceCommutator ρ ⊤ Z) B) +
      fixedCodim (subspaceImageRepresentation ρ (fixedSpace ρ Z))
        (restrictedSubgroup ρ (fixedSpace ρ Z) B) := by
  have hc := odd_fixed_moved_complement ρ (hZ.2.1 ▸ (by decide : Odd 3))
  have hst := h.invariant_line_stable ρ hZ
  have hsum := fixedSpace_split ρ _ _ B hc (le_top.trans hst.1) (le_top.trans hst.2)
  have hdis : Disjoint (subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B)
      (fixedSpace ρ Z ⊓ fixedSpace ρ B) := hc.disjoint.mono inf_le_left inf_le_left
  have hf := Submodule.finrank_sup_add_finrank_inf_eq
    (subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B) (fixedSpace ρ Z ⊓ fixedSpace ρ B)
  rw [hsum, hdis.eq_bot, finrank_bot, add_zero] at hf
  have ht := Submodule.finrank_add_eq_of_isCompl hc
  have hn := fixedCodim_add_finrank ρ B
  have hu := fixedCodim_restrictedSubgroup ρ (subspaceCommutator ρ ⊤ Z) B (le_top.trans hst.1)
  have hw := fixedCodim_restrictedSubgroup ρ (fixedSpace ρ Z) B (le_top.trans hst.2)
  have hlu := Submodule.finrank_mono
    (show subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B ≤ subspaceCommutator ρ ⊤ Z from inf_le_left)
  have hlw := Submodule.finrank_mono
    (show fixedSpace ρ Z ⊓ fixedSpace ρ B ≤ fixedSpace ρ Z from inf_le_left)
  omega

/-- On a four-dimensional line support, precisely three units of the global
codimension budget are spent; the actual remainder image has codimension at most one. -/
private theorem Input.invariant_line_remainder_budget [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Input ρ P A s)
    (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4) :
    fixedCodim ρ A = 3 + fixedCodim (subspaceImageRepresentation ρ (fixedSpace ρ Z))
        (restrictedSubgroup ρ (fixedSpace ρ Z) A) ∧
      fixedCodim (subspaceImageRepresentation ρ (fixedSpace ρ Z))
        (restrictedSubgroup ρ (fixedSpace ρ Z) A) ≤ 1 := by
  have hc := odd_fixed_moved_complement ρ (hZ.2.1 ▸ (by decide : Odd 3))
  have hst := h.invariant_line_stable ρ hZ
  have hsum := fixedSpace_split ρ _ _ A hc (le_top.trans hst.1) (le_top.trans hst.2)
  have hdis : Disjoint (subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ A)
      (fixedSpace ρ Z ⊓ fixedSpace ρ A) := hc.disjoint.mono inf_le_left inf_le_left
  have hfix := Submodule.finrank_sup_add_finrank_inf_eq
    (subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ A) (fixedSpace ρ Z ⊓ fixedSpace ρ A)
  rw [hsum, hdis.eq_bot, finrank_bot, add_zero, h.invariant_line_fixed_dimension ρ hZ] at hfix
  have htotal := Submodule.finrank_add_eq_of_isCompl hc
  rw [hd] at htotal
  have hnum := fixedCodim_add_finrank ρ A
  have hrest := fixedCodim_restrictedSubgroup ρ (fixedSpace ρ Z) A (le_top.trans hst.2)
  have hb := Submodule.finrank_mono
    (show fixedSpace ρ Z ⊓ fixedSpace ρ A ≤ fixedSpace ρ Z from inf_le_left)
  have hupper := h.fixedCodim_le_four ρ
  omega

/-- A proper line support has a nonzero literal fixed complement. -/
private theorem Input.invariant_line_remainder_ne_bot {P A Z : Subgroup G} {s : ℕ}
    (_h : Input ρ P A s) (hZ : IsInvariantLine P A Z)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) : fixedSpace ρ Z ≠ ⊥ := by
  intro hz
  have hc := (odd_fixed_moved_complement ρ (hZ.2.1 ▸ (by decide : Odd 3))).sup_eq_top
  rw [hz, sup_bot_eq] at hc
  exact hp hc

/-- A nonzero complement cannot be centralized by A: then [P,A]=P
would centralize a space which is generated by its own P-displacements. -/
private theorem Input.invariant_line_remainder_noncentral {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) : ¬ fixedSpace ρ Z ≤ fixedSpace ρ A := by
  intro hf
  have hh := le_fixedSpace_commutator_of_invariant ρ
    (show P ≤ subspaceStabilizer ρ (fixedSpace ρ Z) from
      le_top.trans (h.invariant_line_stable ρ hZ).2) hf
  rw [h.core_commutator] at hh
  have hz := (subspaceCommutator_eq_bot_iff ρ (fixedSpace ρ Z) P).mpr hh
  rw [h.invariant_line_remainder_moved ρ hZ] at hz
  exact h.invariant_line_remainder_ne_bot ρ hZ hp hz

/-- A proper four-dimensional support exhausts the four-unit codimension budget. -/
private theorem Input.proper_four_codimension [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Input ρ P A s)
    (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) : fixedCodim ρ A = 4 := by
  have hn := h.invariant_line_remainder_noncentral ρ hZ hp
  have hst : A ≤ subspaceStabilizer ρ (fixedSpace ρ Z) :=
    le_top.trans (h.invariant_line_stable ρ hZ).2
  have hi := restrictedSubgroup_ne_bot ρ (fixedSpace ρ Z) hst hn
  have hpos := fixedCodim_pos_of_faithful (subspaceImageRepresentation ρ (fixedSpace ρ Z))
    (subspaceImageRepresentation_injective ρ (fixedSpace ρ Z)) hi
  have hb := h.invariant_line_remainder_budget ρ hZ hd
  omega

/-- An order-two subgroup fixing the remainder moves at most two dimensions
when the other summand has dimension four. This is the original action. -/
private theorem Input.four_support_subactor_bound [FiniteDimensional (ZMod 2) V]
    {P A Z C : Subgroup G} {s : ℕ} (h : Input ρ P A s)
    (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4)
    (hC : Nat.card C = 2) (hfix : fixedSpace ρ Z ≤ fixedSpace ρ C) :
    fixedCodim ρ C ≤ 2 := by
  have hst := h.invariant_line_stable ρ hZ
  have he := h.invariant_line_codimension_split ρ hZ C
  have hu := fixedCodim_restrictedSubgroup ρ (subspaceCommutator ρ ⊤ Z) C (le_top.trans hst.1)
  have hw := fixedCodim_restrictedSubgroup ρ (fixedSpace ρ Z) C (le_top.trans hst.2)
  rw [inf_eq_left.mpr hfix, Nat.sub_self] at hw
  have hb := dimension_le_twice_fixed ρ (subspaceCommutator ρ ⊤ Z) C
    (le_top.trans hst.1) hC
  omega



variable [FiniteDimensional (ZMod 2) V]

private theorem no_faithful_four_coatom (hf : Function.Injective ρ)
    (P A : Subgroup G) (hP : IsPGroup 3 P) (hA : IsElementaryTwo A)
    (hcA : Nat.card A = 4) (hPA : ⁅P, A⁆ = P)
    (hm : subspaceCommutator ρ ⊤ P = ⊤) (hd : fixedCodim ρ A ≤ 1) : False := by
  let : IsElementaryAbelian 2 A := hA.2
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F := fixedSpace ρ A
  let S := subspaceStabilizer ρ F
  have hAS : A ≤ S := fixedSpace_subactor_stabilized ρ hA le_rfl
  have hgen := iSup_hyperplane_centralizer_commutator (by decide : 3 ≠ 2) P A hP
    (le_normalizer_iff_commutator_le_left.mpr hPA.le)
  have hPS : P ≤ S := by
    rw [← hPA, ← hgen]
    apply iSup₂_le
    intro B hB
    let B₀ := B.map A.subtype
    have hBA : B₀ ≤ A := map_subtype_le B
    have hcard : Nat.card B₀ = 2 := by
      have hh := B.card_mul_index
      rw [hB, hcA] at hh
      have hmap : Nat.card B₀ = Nat.card B := card_map_of_injective A.subtype_injective
      omega
    have hBn : B₀ ≠ ⊥ := by intro he; rw [he, card_bot] at hcard; omega
    have hpos := fixedCodim_pos_of_faithful ρ hf hBn
    have hle := Submodule.finrank_mono (fixedSpace_antitone ρ hBA)
    have ha := fixedCodim_add_finrank ρ A
    have hb := fixedCodim_add_finrank ρ B₀
    have he : fixedSpace ρ B₀ = F :=
      (fixedSpace_eq_of_fixedCodim_eq ρ hBA (by omega)).symm
    have hCS : P ⊓ centralizer (B₀ : Set G) ≤ S := by
      dsimp only [S]
      rw [← he]
      exact fixedSpace_invariant_normalizer ρ
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
    apply commutator_le.mpr
    intro p hp a ha
    exact S.mul_mem (S.mul_mem (S.mul_mem (hCS hp) (hAS ha)) (S.inv_mem (hCS hp)))
      (S.inv_mem (hAS ha))
  have hFP : F ≤ fixedSpace ρ P := by
    rw [← hPA]
    exact le_fixedSpace_commutator_of_invariant ρ hPS le_rfl
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hc := odd_fixed_moved_complement ρ (hn ▸ (by decide : Odd 3).pow)
  have hF : F = ⊥ := le_bot_iff.mp (by
    intro v hv
    have hu : v ∈ subspaceCommutator ρ ⊤ P := by rw [hm]; trivial
    exact hc.disjoint.le_bot ⟨hu, hFP hv⟩)
  have hvdim : Module.finrank (ZMod 2) V ≤ 1 := by
    have hh := fixedCodim_add_finrank ρ A
    change fixedCodim ρ A + Module.finrank (ZMod 2) F = _ at hh
    rw [hF, finrank_bot, add_zero] at hh
    omega
  obtain ⟨a, ha, han⟩ := (Subgroup.nontrivial_iff_exists_ne_one A).mp
    ((Subgroup.nontrivial_iff_ne_bot A).mpr hA.1)
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) han
  have hne : zpowers a ≠ ⊥ := by
    intro he
    exact han (he.le (mem_zpowers a))
  have hpos := fixedCodim_pos_of_faithful ρ hf hne
  have hhalf := (involution_actor_rank_and_fixedCodim ρ a ho).2.2.2
  omega

/-- Coprime hyperplane generation forces a nontrivial kernel on the complement
of a proper four-dimensional support. No remainder dimension is assumed. -/
private theorem Input.proper_four_remainder_kernel_ne_bot {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) :
    subspaceKernel ρ (fixedSpace ρ Z) A ≠ ⊥ := by
  intro hker
  let W := fixedSpace ρ Z
  let σ := subspaceImageRepresentation ρ W
  let P' := restrictedSubgroup ρ W P
  let A' := restrictedSubgroup ρ W A
  have hst := (h.invariant_line_stable ρ hZ).2
  have hPst : P ≤ subspaceStabilizer ρ W := le_top.trans hst
  have hAst : A ≤ subspaceStabilizer ρ W := le_top.trans hst
  have hcA : Nat.card A' = 4 := by
    have hc := card_subspaceKernel_mul_image ρ W A hAst
    rw [hker, card_bot, one_mul, h.card_actor] at hc
    exact hc
  have hnon : ¬ W ≤ fixedSpace ρ A := h.invariant_line_remainder_noncentral ρ hZ hp
  have hA' : IsElementaryTwo A' := h.actor.restrictedSubgroup ρ W hAst hnon
  let : IsElementaryAbelian 3 P := h.elementary
  have hP' : IsPGroup 3 P' := by
    change IsPGroup 3 ((P.subgroupOf (subspaceStabilizer ρ W)).map (subspaceActionHom ρ W))
    exact ((IsElementaryAbelian.isPGroup 3 P).comap_subtype).map _
  have hm : subspaceCommutator σ ⊤ P' = ⊤ := restricted_commutator_eq_top ρ W P hPst
    (h.invariant_line_remainder_moved ρ hZ)
  have hcomm : ⁅P', A'⁆ = P' := restrictedSubgroup_commutator ρ W hPst hAst h.core_commutator
  exact no_faithful_four_coatom σ (subspaceImageRepresentation_injective ρ W) P' A' hP' hA'
    hcA hcomm hm (h.invariant_line_remainder_budget ρ hZ hd).2

/-- The actual small order-two subactor in the proper-four branch is constructed
from the complement kernel, with its bound on the original representation. -/
private theorem Input.proper_four_small_subactor {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) :
    ∃ C : Subgroup G, C ≤ A ∧ Nat.card C = 2 ∧
      fixedSpace ρ Z ≤ fixedSpace ρ C ∧ fixedCodim ρ C ≤ 2 := by
  obtain ⟨c, hc, hcn⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp
    ((Subgroup.nontrivial_iff_ne_bot _).mpr (h.proper_four_remainder_kernel_ne_bot ρ hZ hd hp))
  let : IsElementaryAbelian 2 A := h.actor.2
  have ho : orderOf c = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian c hc.1) hcn
  have hC : Nat.card (zpowers c) = 2 := (Nat.card_zpowers c).trans ho
  have hf : fixedSpace ρ Z ≤ fixedSpace ρ (zpowers c) := by
    intro v hv
    exact (mem_fixedSpace_zpowers_iff ρ c v).mpr (hc.2 v hv)
  exact ⟨zpowers c, zpowers_le.mpr hc.1, hC, hf, h.four_support_subactor_bound ρ hZ hd hC hf⟩

/-- A proper four-dimensional invariant-line support is impossible: its
constructed order-two subactor violates the strict minimality inequality. -/
private theorem Input.no_proper_four_support {P A Z : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4) :
    subspaceCommutator ρ ⊤ Z = ⊤ := by
  by_contra hp
  obtain ⟨C, hCA, hC, _, hb⟩ := h.proper_four_small_subactor ρ hZ hd hp
  exact h.no_codim_four_with_small_subactor ρ hCA hC hb (h.proper_four_codimension ρ hZ hd hp)

omit [FiniteDimensional (ZMod 2) V] in
private theorem Input.invariant_lines_generate {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) :
    (⨆ Z : {Z : Subgroup G // IsInvariantLine P A Z}, Z.val) = P := by
  let : IsElementaryAbelian 2 A := h.actor.2
  let : IsElementaryAbelian 3 P := h.elementary
  let : P.Normal := h.normal
  have hn : A ≤ Subgroup.normalizer (P : Set G) := by rw [Subgroup.normalizer_eq_top]; exact le_top
  apply le_antisymm (iSup_le fun Z => Z.property.1)
  conv_lhs => rw [← h.core_commutator, ← Subgroup.iSup_hyperplane_centralizer_commutator
    (by decide : 3 ≠ 2) P A (IsElementaryAbelian.isPGroup 3 P) hn]
  apply iSup₂_le
  intro B hB
  let D := P ⊓ Subgroup.centralizer (B.map A.subtype : Set G)
  have hBA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
  have hnD : A ≤ Subgroup.normalizer (D : Set G) := by
    apply (le_inf hn ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    apply (le_trans ?_ (Subgroup.centralizer_le_normalizer (B.map A.subtype : Set G))).trans
      (Subgroup.normalizer_le_normalizer_centralizer _)
    exact (Subgroup.le_centralizer A).trans (Subgroup.centralizer_le hBA)
  have hcom : ⁅D, A⁆ ≤ D := Subgroup.le_normalizer_iff_commutator_le_left.mp hnD
  by_cases hd : D = ⊥
  · exact hcom.trans (hd.le.trans bot_le)
  have hc : Nat.card (B.map A.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    have hh := B.card_mul_index
    rw [hB, h.card_actor] at hh
    omega
  have hr : rank (B.map A.subtype) = 1 := by simp only [rank, hc]; decide
  have hD3 : Nat.card D = 3 := (h.hyperplane_support _ hBA hr hd).1
  exact hcom.trans (le_iSup_of_le ⟨D, inf_le_left, hD3, hnD⟩ le_rfl)



/-- Distinct invariant support planes are fixed by each other's lines. -/
private theorem Input.invariant_lines_cross_fixed {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hsmall : SmallInvariantSupports ρ P A)
    {X Y : Subgroup G} (hX : IsInvariantLine P A X) (hY : IsInvariantLine P A Y)
    (hne : X ≠ Y) : subspaceCommutator ρ ⊤ Y ≤ fixedSpace ρ X := by
  let := Representation.BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := Representation.BinaryGroupAction.elementary
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : FaithfulSMul G (Multiplicative V) := Representation.BinaryGroupAction.faithful ρ h.faithful
  let : IsElementaryAbelian 3 P := h.elementary
  have hPF : P ≤ fittingSubgroup G :=
    le_sSup ⟨h.normal, (IsElementaryAbelian.isPGroup 3 P).isNilpotent⟩
  have hmem (Z : Subgroup G) (hZ : IsInvariantLine P A Z) :
      Z ∈ smallSupportFactors G (Multiplicative V) 1 := by
    refine ⟨hZ.1.trans hPF, hZ.2.1, ?_⟩
    rw [Representation.BinaryGroupAction.commutator_card, hsmall Z hZ]
  have hh := smallSupportFactors_cross_fixed_of_commuting (V := Multiplicative V)
    (Or.inl rfl : 1 = 1 ∨ 1 = 2) (hmem X hX) (hmem Y hY) hne
    (hX.1.trans ((Subgroup.le_centralizer P).trans (Subgroup.centralizer_le hY.1)))
  rw [Representation.BinaryGroupAction.commutator_eq,
    Representation.BinaryGroupAction.fixedPoints_eq] at hh
  exact (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).le_iff_le.mp hh

/-- Coprime splitting separates each support from the sum of all the others. -/
private theorem Input.invariant_supports_independent {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hsmall : SmallInvariantSupports ρ P A) :
    iSupIndep (fun Z : {Z : Subgroup G // IsInvariantLine P A Z} =>
      subspaceCommutator ρ ⊤ Z.val) := by
  rw [iSupIndep_def]
  intro Z
  apply (odd_fixed_moved_complement ρ (Z.property.2.1 ▸ (by decide : Odd 3))).disjoint.mono_right
  exact iSup_le fun Y => iSup_le fun hne =>
    h.invariant_lines_cross_fixed ρ hsmall Z.property Y.property
      (fun he => hne (Subtype.ext he.symm))

omit [FiniteDimensional (ZMod 2) V] in
private theorem line_support_faithful {Z : Subgroup G}
    (hf : Function.Injective ρ) (hZ : Nat.card Z = 3)
    {z : G} (hz : z ∈ Z)
    (hfix : ∀ v ∈ subspaceCommutator ρ ⊤ Z, ρ z v = v) : z = 1 := by
  apply hf
  ext v
  have hc := odd_fixed_moved_complement ρ (hZ ▸ (by decide : Odd 3))
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (hc.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
  have hwf : ρ z w = w := hw ⟨z, hz⟩
  simp only [map_add, hfix u hu, hwf, map_one, Module.End.one_apply]

/-- Faithfulness on each support makes the original core lines independent. -/
private theorem Input.invariant_lines_independent {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hsmall : SmallInvariantSupports ρ P A) :
    iSupIndep (fun Z : {Z : Subgroup G // IsInvariantLine P A Z} => Z.val) := by
  rw [iSupIndep_def]
  intro Z
  apply Subgroup.disjoint_def.mpr
  intro z hz hrest
  apply line_support_faithful ρ h.faithful Z.property.2.1 hz
  have hle : (⨆ Y : {Y : Subgroup G // IsInvariantLine P A Y}, ⨆ (_ : Y ≠ Z), Y.val) ≤
      subspaceKernel ρ (subspaceCommutator ρ ⊤ Z.val) ⊤ := by
    apply iSup_le
    intro Y
    apply iSup_le
    intro hne y hy
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    exact h.invariant_lines_cross_fixed ρ hsmall Y.property Z.property
      (fun he => hne (Subtype.ext he)) hv ⟨y, hy⟩
  exact (hle hrest).2

omit [FiniteDimensional (ZMod 2) V] in
/-- All the literal supports span the original moved module. -/
private theorem Input.invariant_supports_generate {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) :
    (⨆ Z : {Z : Subgroup G // IsInvariantLine P A Z}, subspaceCommutator ρ ⊤ Z.val) = ⊤ := by
  rw [← Representation.BinaryGroupAction.moved_iSup, h.invariant_lines_generate ρ, h.moved]


private theorem product_bijective {H I : Type*} [CommGroup H] [Fintype I]
    (F : I → Subgroup H) (hi : iSupIndep F) (hg : ⨆ i, F i = ⊤) :
    Function.Bijective (fun x : (i : I) → F i => ∏ i, (x i : H)) := by
  have hc : Pairwise (fun i j : I => ∀ x y : H, x ∈ F i → y ∈ F j → Commute x y) :=
    fun _ _ _ x y _ _ => Commute.all x y
  have he : (fun x : (i : I) → F i => ∏ i, (x i : H)) = Subgroup.noncommPiCoprod hc := by
    funext x
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  rw [he]
  refine ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep hi, ?_⟩
  apply MonoidHom.range_eq_top.mp
  rw [Subgroup.noncommPiCoprod_range, hg]

private theorem sum_bijective {W I : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype I] (U : I → Submodule (ZMod 2) W)
    (hi : iSupIndep U) (hg : ⨆ i, U i = ⊤) :
    Function.Bijective (fun v : (i : I) → U i => ∑ i, (v i : W)) := by
  classical
  let f : ((i : I) → U i) →ₗ[ZMod 2] W :=
    { toFun := fun v => ∑ i, (v i : W)
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum] }
  constructor
  · intro v w he
    funext i
    apply Subtype.ext
    exact (iSupIndep_iff_finsetSum_eq_imp_eq U).mp hi Finset.univ
      (fun j => (v j : W)) (fun j => (w j : W))
      (fun j _ => ⟨(v j).property, (w j).property⟩) he i (Finset.mem_univ i)
  · change Function.Surjective f
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hg]
    apply iSup_le
    intro i v hv
    refine ⟨Pi.single i ⟨v, hv⟩, ?_⟩
    change ∑ j, ((Pi.single i (⟨v, hv⟩ : U i) : (j : I) → U j) j : W) = v
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp

/-- Construction of all literal factors and support summands, before the
ratio inequality rules out two planes. -/
private theorem Input.exists_invariant_supportFactors {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hsmall : SmallInvariantSupports ρ P A) :
    ∃ d : SupportFactors ρ P s, ∀ i, A ≤ Subgroup.normalizer (d.ambient i : Set G) := by
  classical
  let : IsElementaryAbelian 3 P := h.elementary
  let : CommGroup P := IsMulCommutative.instCommGroup
  let I := {Z : Subgroup G // IsInvariantLine P A Z}
  let : Fintype I := Fintype.ofFinite I
  let F : I → Subgroup P := fun Z => Z.val.subgroupOf P
  have hm (Z : I) : (F Z).map P.subtype = Z.val :=
    Subgroup.map_subgroupOf_eq_of_le Z.property.1
  have hcard (Z : I) : Nat.card (F Z) = 3 := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, hm]
    exact Z.property.2.1
  have hi : iSupIndep F := by
    rw [iSupIndep_def]
    intro Z
    apply Subgroup.disjoint_def.mpr
    intro z hz hrest
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp ((h.invariant_lines_independent ρ hsmall) Z) hz
    have hh := Subgroup.mem_map_of_mem P.subtype hrest
    rw [Subgroup.map_iSup] at hh
    simp only [Subgroup.map_iSup, hm] at hh
    exact hh
  have hg : (⨆ Z, F Z) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_iSup]
    simp only [hm, ← MonoidHom.range_eq_map, P.range_subtype]
    exact h.invariant_lines_generate ρ
  have hb := product_bijective F hi hg
  have hpow : 3 ^ Fintype.card I = 3 ^ s := by
    calc
      3 ^ Fintype.card I = Nat.card ((Z : I) → F Z) := by simp [Nat.card_pi, hcard]
      _ = Nat.card P := Nat.card_congr (Equiv.ofBijective _ hb)
      _ = 3 ^ s := h.card_core
  have hI : Fintype.card I = s := (Nat.pow_right_injective (by decide : 2 ≤ 3)) hpow
  let e : Fin s ≃ I := (Fintype.equivFinOfCardEq hI).symm
  let factor : Fin s → Subgroup P := F ∘ e
  have hif : iSupIndep factor := hi.comp e.injective
  have hgf : (⨆ i, factor i) = ⊤ := by
    simpa only [factor, Function.comp_def, e.surjective.iSup_comp] using hg
  have hmf (i : Fin s) : (factor i).map P.subtype = (e i).val := hm (e i)
  have hvs : iSupIndep (fun i : Fin s => subspaceCommutator ρ ⊤ ((factor i).map P.subtype)) := by
    simp only [hmf]
    exact (h.invariant_supports_independent ρ hsmall).comp e.injective
  have hvg : (⨆ i : Fin s, subspaceCommutator ρ ⊤ ((factor i).map P.subtype)) = ⊤ := by
    simp only [hmf]
    rw [e.surjective.iSup_comp (fun Z : I => subspaceCommutator ρ ⊤ Z.val)]
    exact h.invariant_supports_generate ρ
  refine ⟨{
    factor := factor
    card_factor := fun i => hcard (e i)
    multiply_bijective := ?_
    support_dim := ?_
    add_bijective := sum_bijective _ hvs hvg }, ?_⟩
  · simpa only [Fin.prod_ofFn] using product_bijective factor hif hgf
  · intro i
    rw [hmf]
    exact hsmall _ (e i).property
  · intro i
    change A ≤ Subgroup.normalizer ((factor i).map P.subtype : Set G)
    rw [hmf]
    exact (e i).property.2.2

omit [Finite G] in
private theorem Input.core_rank_eq_two_of_finrank_four {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hdim : Module.finrank (ZMod 2) V = 4) : s = 2 := by
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let f := (MulDistribMulAction.toMulAut G (Multiplicative V)).comp P.subtype
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply h.faithful
    ext v
    exact congrArg Multiplicative.toAdd
      (MulEquiv.congr_fun he (Multiplicative.ofAdd v))
  have hc : Nat.card (Multiplicative V) = 2 ^ 4 := by
    change Nat.card V = 2 ^ 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hd := Subgroup.card_dvd_of_injective f hi
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow
    (Multiplicative V) 4 hc, h.card_core] at hd
  rcases h.rank_cases with hs | hs
  · exact hs
  · rw [hs] at hd
    norm_num [Fin.prod_univ_succ] at hd


private theorem moved_comp_subtype {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (P : Subgroup G) (K : Subgroup P) :
    subspaceCommutator (ρ.comp P.subtype) ⊤ K =
      subspaceCommutator ρ ⊤ (K.map P.subtype) := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨k, hk, w, hw, rfl⟩
    exact ⟨k, Subgroup.mem_map_of_mem P.subtype hk, w, hw, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, w, hw, rfl⟩
    exact ⟨k, hk, w, hw, rfl⟩

private theorem moved_eq_opposite_fixed {H V : Type*} [CommGroup H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) H V) (K L : Subgroup H)
    (hK : Odd (Nat.card K)) (hC : IsCompl (fixedSpace σ K) (fixedSpace σ L)) :
    subspaceCommutator σ ⊤ K = fixedSpace σ L := by
  have hle : subspaceCommutator σ ⊤ K ≤ fixedSpace σ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, _, rfl⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fixedSpace σ K ⊔ fixedSpace σ L from hC.sup_eq_top ▸ Submodule.mem_top)
    have hu' : σ k u = u := hu ⟨k, hk⟩
    rw [map_add, hu', add_sub_add_left_eq_sub]
    intro l
    change σ (l : H) (σ k w - w) = σ k w - w
    rw [map_sub]
    have hc : σ (l : H) (σ k w) = σ k (σ (l : H) w) := by
      simp only [← Module.End.mul_apply, ← map_mul, mul_comm]
    have hw' : σ (l : H) w = w := hw l
    rw [hc, hw']
  exact (le_iff_eq_of_codisjoint_of_disjoint
    (odd_fixed_moved_complement σ hK).codisjoint hC.disjoint).mp hle

private theorem two_factor_product_bijective {H : Type*} [Group H] [Finite H]
    (K L : Subgroup H) (hcard : Nat.card K * Nat.card L = Nat.card H)
    (hd : Disjoint K L) :
    Function.Bijective (fun x : (i : Fin 2) → (![K, L] i : Subgroup H) =>
      (List.ofFn fun i => (x i : H)).prod) := by
  have hp : Function.Bijective (fun x : K × L => (x.1 : H) * (x.2 : H)) :=
    (Subgroup.isComplement_iff_bijective K L).mp
      (Subgroup.isComplement'_of_card_mul_and_disjoint hcard hd)
  have hh : Function.Bijective (fun x : (i : Fin 2) → (![K, L] i : Subgroup H) =>
      (x 0 : H) * (x 1 : H)) :=
    hp.comp (piFinTwoEquiv (fun i => (![K, L] i : Subgroup H))).bijective
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one] using hh

private theorem two_support_sum_bijective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (U : Fin 2 → Submodule (ZMod 2) V) (hU : IsCompl (U 0) (U 1)) :
    Function.Bijective (fun v : (i : Fin 2) → U i => ∑ i, (v i : V)) := by
  have hh := (Submodule.prodEquivOfIsCompl (U 0) (U 1) hU).bijective.comp
    (piFinTwoEquiv (fun i => U i)).bijective
  simpa only [Function.comp_def, piFinTwoEquiv_apply,
    Submodule.coe_prodEquivOfIsCompl', Fin.sum_univ_two] using hh

/-- The full-support four-space has two literal order-three support factors,
whose original moved planes sum bijectively onto the original module. -/
private theorem Input.fullSupport_supportFactors {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) (hfull : FullSupport ρ P A) :
    Nonempty (SupportFactors ρ P s) := by
  obtain ⟨Z, hZ, hmove, hdim⟩ := hfull
  have hs := h.core_rank_eq_two_of_finrank_four ρ hdim
  subst s
  let : IsElementaryAbelian 3 P := h.elementary
  let : CommGroup P := IsMulCommutative.instCommGroup
  let σ : Representation (ZMod 2) P V := ρ.comp P.subtype
  let := action σ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hfσ : Function.Injective σ := fun x y he => Subtype.ext (h.faithful he)
  let := Representation.BinaryGroupAction.faithful σ hfσ
  have hP : Nat.card P = 9 := by rw [h.card_core]; rfl
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    norm_num
  have hf : FixedPoints.subgroup (⊤ : Subgroup P) (Multiplicative V) = ⊥ := by
    rw [fixedPoints_eq σ, fixedSpace_comp_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, h.fixedSpace_core_eq_bot ρ]
    exact (submoduleEquivSubgroup (V := V)).map_bot
  obtain ⟨K, L, hK, hL, hKL, hFK, hFL, hF⟩ :=
    nine_sixteen_fixed_factor_decomposition hP hV hf
  have hC : IsCompl (fixedSpace σ K) (fixedSpace σ L) := by
    apply (submoduleEquivSubgroup (V := V)).isCompl_iff.mpr
    simpa only [← fixedPoints_eq σ] using hF
  have hdimF (M : Subgroup P)
      (hc : Nat.card (FixedPoints.subgroup M (Multiplicative V)) = 4) :
      Module.finrank (ZMod 2) (fixedSpace σ M) = 2 := by
    rw [fixedPoints_eq σ, card_submoduleEquivSubgroup,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  have hMK : subspaceCommutator ρ ⊤ (K.map P.subtype) = fixedSpace σ L := by
    rw [← moved_comp_subtype]
    exact moved_eq_opposite_fixed σ K L (hK ▸ (by decide : Odd 3)) hC
  have hML : subspaceCommutator ρ ⊤ (L.map P.subtype) = fixedSpace σ K := by
    rw [← moved_comp_subtype]
    exact moved_eq_opposite_fixed σ L K (hL ▸ (by decide : Odd 3)) hC.symm
  refine ⟨{
    factor := ![K, L]
    card_factor := ?_
    multiply_bijective := two_factor_product_bijective K L (by rw [hK, hL, hP]) hKL.disjoint
    support_dim := ?_
    add_bijective := ?_ }⟩
  · intro i
    fin_cases i
    · exact hK
    · exact hL
  · intro i
    fin_cases i
    · change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (K.map P.subtype)) = 2
      rw [hMK]
      exact hdimF L hFL
    · change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (L.map P.subtype)) = 2
      rw [hML]
      exact hdimF K hFK
  · apply two_support_sum_bijective
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hMK, hML] using hC.symm

private theorem Input.fullSupport_or_smallInvariantSupports {P A : Subgroup G} {s : ℕ}
    (h : Input ρ P A s) : FullSupport ρ P A ∨ SmallInvariantSupports ρ P A := by
  classical
  by_cases hf : FullSupport ρ P A
  · exact Or.inl hf
  right
  intro Z hZ
  rcases h.invariant_line_dimension ρ hZ with hd | hd
  · exact hd
  · have ht := h.no_proper_four_support ρ hZ hd
    have hdim : Module.finrank (ZMod 2) V = 4 := by
      rw [ht] at hd
      simpa only [finrank_top] using hd
    exact (hf ⟨Z, hZ, ht, hdim⟩).elim



/-- Canonical plane geometry, including the two-plane FF alternative. -/
theorem Input.supports {P A : Subgroup G} {s : ℕ} (h : Input ρ P A s) :
    ∃ d : SupportFactors ρ P s,
      s = 3 → ∀ i, A ≤ normalizer (d.ambient i : Set G) := by
  rcases h.fullSupport_or_smallInvariantSupports ρ with hfull | hsmall
  · obtain ⟨d⟩ := h.fullSupport_supportFactors ρ hfull
    have hs := h.core_rank_eq_two_of_finrank_four ρ hfull.choose_spec.2.2
    exact ⟨d,fun he => by omega⟩
  · obtain ⟨d,hn⟩ := h.exists_invariant_supportFactors ρ hsmall
    exact ⟨d,fun _ => hn⟩

end CFSG.Quasithin.ChapterD.BeforeMoved
