module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.InvariantLineReduction.Hyperplanes
public import Theory.Representation.BinaryGroupAction

/-!
# Fixed and moved dimensions of invariant order-three lines

Odd averaging identifies the moved space inside an invariant subspace with
its intersection with the whole moved space. Thus the hyperplane hypothesis
identifies a fixed plane on each line support. Involution rank--nullity bounds
the support dimension by four; orbit counting for the three-action excludes
odd dimension. The actor fixes exactly a line in that plane, and hence in the
whole support.

The original fixed/moved splitting is invariant under the entire local group.
Its fixed codimensions add. A proper four-dimensional support therefore leaves
a nonzero complement of fixed codimension one. Minimality of the starred actor
forces its action on this complement to be faithful: an order-two kernel would
move at most two dimensions on the four-dimensional summand.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, D.2.14,
printed pp.186--187, (+), (++), and the proper four-support paragraph.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender Subgroup
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

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
theorem Reduced.invariant_line_fixed_support {P A Z : Subgroup G} {s : ℕ}
    (_h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z) :
    let B := A ⊓ centralizer (Z : Set G)
    subspaceCommutator ρ (fixedSpace ρ B) Z =
      subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B := by
  dsimp only
  rw [moved_on_invariant_eq_inf ρ _ Z (hZ.2.1 ▸ (by decide : Odd 3))
    (fixedSpace_invariant_normalizer ρ
      ((le_centralizer_iff.mp (show A ⊓ centralizer (Z : Set G) ≤ centralizer (Z : Set G)
        from inf_le_right)).trans (centralizer_le_normalizer _))), inf_comm]

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
theorem Reduced.invariant_line_dimension [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
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
theorem Reduced.invariant_line_fixed_dimension [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hZ : IsInvariantLine P A Z) :
    Module.finrank (ZMod 2)
      (subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) = 1 := by
  let B := A ⊓ centralizer (Z : Set G)
  let D := subspaceCommutator ρ (fixedSpace ρ B) Z
  have hd : Module.finrank (ZMod 2) D = 2 := (h.invariant_line_hyperplane ρ hZ).2.2.2
  have hs : A ≤ subspaceStabilizer ρ D := subspaceCommutator_invariant_normalizer ρ
    (fixedSpace_subactor_stabilized ρ h.starred.1.2.1 inf_le_left) hZ.2.2
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
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  have he := plane_fixed_dimension ρ D A (IsElementaryAbelian.isPGroup 2 A) hs hd hn
  have hD : D = subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B :=
    h.invariant_line_fixed_support ρ hZ
  rw [hD, inf_assoc, inf_eq_right.mpr (fixedSpace_antitone ρ (show B ≤ A from inf_le_left))] at he
  exact he

omit [Finite G] in
/-- Elementary-core centrality makes an A-invariant line normal in the whole local group. -/
theorem Reduced.invariant_line_normalizer {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z) :
    (⊤ : Subgroup G) ≤ normalizer (Z : Set G) := by
  let : IsElementaryAbelian 3 P := h.elementary
  have hp : P ≤ centralizer (Z : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hZ.1)
  rw [← h.generated]
  exact sup_le (hp.trans (centralizer_le_normalizer _)) hZ.2.2

omit [Finite G] in
/-- Both original summands of the invariant-line splitting are local-group invariant. -/
theorem Reduced.invariant_line_stable {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z) :
    (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ Z) ∧
      (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (fixedSpace ρ Z) :=
  ⟨subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
    (h.invariant_line_normalizer ρ hZ),
    fixedSpace_invariant_normalizer ρ (h.invariant_line_normalizer ρ hZ)⟩

/-- The fixed complement is still generated by the original odd core's displacements. -/
theorem Reduced.invariant_line_remainder_moved {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z) :
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
theorem Reduced.invariant_line_codimension_split [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
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
theorem Reduced.invariant_line_remainder_budget [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
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
theorem Reduced.invariant_line_remainder_ne_bot {P A Z : Subgroup G} {s : ℕ}
    (_h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) : fixedSpace ρ Z ≠ ⊥ := by
  intro hz
  have hc := (odd_fixed_moved_complement ρ (hZ.2.1 ▸ (by decide : Odd 3))).sup_eq_top
  rw [hz, sup_bot_eq] at hc
  exact hp hc

/-- A nonzero complement cannot be centralized by A: then [P,A]=P
would centralize a space which is generated by its own P-displacements. -/
theorem Reduced.invariant_line_remainder_noncentral {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z)
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
theorem Reduced.proper_four_codimension [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
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
theorem Reduced.four_support_subactor_bound [FiniteDimensional (ZMod 2) V]
    {P A Z C : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
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

/-- In the proper-four case the action on the nonzero complement must be faithful
on A. An order-two kernel would give the forbidden equal-ratio subactor. -/
theorem Reduced.proper_four_remainder_kernel_eq_bot [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) :
    subspaceKernel ρ (fixedSpace ρ Z) A = ⊥ := by
  apply le_bot_iff.mp
  intro c hc
  by_contra hcn
  have hcne : c ≠ 1 := hcn
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  have ho : orderOf c = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian c hc.1) hcne
  have hCA : zpowers c ≤ A := zpowers_le.mpr hc.1
  have hC : Nat.card (zpowers c) = 2 := (Nat.card_zpowers c).trans ho
  have hf : fixedSpace ρ Z ≤ fixedSpace ρ (zpowers c) := by
    intro v hv
    exact (mem_fixedSpace_zpowers_iff ρ c v).mpr (hc.2 v hv)
  have hb := h.four_support_subactor_bound ρ hZ hd hC hf
  exact h.no_codim_four_with_small_subactor ρ hCA hC hb (h.proper_four_codimension ρ hZ hd hp)

end CFSG.Quasithin.ChapterD.FittingConfigurations
