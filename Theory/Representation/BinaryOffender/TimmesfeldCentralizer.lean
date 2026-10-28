module

public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.BinaryOffender.ComponentDisplacement
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Timmesfeld replacement for the full displacement centralizer

For a finite binary representation and a best offender `A`, the concrete
subgroup `displacementCentralizer ρ A = C_A([V,A])` is nontrivial, has the
same weight as `A`, and is therefore a best offender. Its fixed space is
`[V,A] + C_V(A)`. Together with the quadraticity already proved in
`ComponentDisplacement`, these are all clauses of GLS Theorem 26.23(i)
in characteristic two. The proof in fact does not need faithfulness.

The group order formula and the subspace dimension formula show that
intersecting equal-weight subgroups preserves weight and adds their fixed
spaces. Apply this repeatedly to the single-vector centralizers `C_A([v,A])`.
For nontriviality, if an intersection with `C_A([v,A])` were trivial, the
fixed-space formula would express `v` as a vector fixed by the preceding
intersection plus a displacement of `v`. The cyclic-displacement lemma
then forces the preceding intersection to lie in `C_A([v,A])`, a contradiction.
This binary argument replaces the final p-group argument in the source.

Source: Gorenstein–Lyons–Solomon, *The Classification of the Finite Simple
Groups*, vol. 2, Lemma 26.21, Proposition 26.22, and Theorem 26.23(i);
`refs/KGroup/GLS2/ChapterG.tex`, lines 1154–1207.
-/

public section

namespace Representation.BinaryOffender
open scoped IsMulCommutative
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

private theorem rank_inf_add_rank_sup {A B C : Subgroup G}
    (hA : IsElementaryTwo A) (hB : B ≤ A) (hC : C ≤ A) :
    rank (B ⊓ C) + rank (B ⊔ C) = rank B + rank C := by
  let _ : IsElementaryAbelian 2 A := hA.2
  have hcard (D : Subgroup G) (hD : D ≤ A) : Nat.card D = 2 ^ rank D := by
    by_cases h : D = ⊥
    · simp [h]
    · exact (hA.of_le hD h).card_eq_two_pow_rank
  have hn : C ≤ Subgroup.normalizer (B : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact setLike_mul_comm (hB hb) (hC hc)
  have hc := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes B C hn
  rw [hcard B hB, hcard C hC, hcard _ (inf_le_left.trans hB),
    hcard _ (sup_le hB hC), ← pow_add, ← pow_add] at hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hc).symm

/-- Equal-weight subgroups of a best offender are closed under intersection;
the fixed space of their intersection is the sum of their fixed spaces. -/
theorem IsBestOffender.inf_equalWeightLE_fixedSpace {A B C : Subgroup G}
    (hA : IsBestOffender ρ A) (hB : EqualWeightLE ρ B A) (hC : EqualWeightLE ρ C A) :
    EqualWeightLE ρ (B ⊓ C) A ∧
      fixedSpace ρ (B ⊓ C) = fixedSpace ρ B ⊔ fixedSpace ρ C := by
  have hr := rank_inf_add_rank_sup hA.1 hB.1 hC.1
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ B) (fixedSpace ρ C)
  have hs : fixedSpace ρ (B ⊔ C) = fixedSpace ρ B ⊓ fixedSpace ρ C :=
    ρ.invariants_comp_sup B C
  have hle : fixedSpace ρ B ⊔ fixedSpace ρ C ≤ fixedSpace ρ (B ⊓ C) :=
    sup_le (fixedSpace_antitone ρ inf_le_left) (fixedSpace_antitone ρ inf_le_right)
  have hm := Submodule.finrank_mono hle
  have hi := hA.2 (B ⊓ C) (inf_le_left.trans hB.1)
  have hj := hA.2 (B ⊔ C) (sup_le hB.1 hC.1)
  have hb := hB.2
  have hc := hC.2
  simp only [weight] at hi hj hb hc
  rw [hs] at hj
  have heqdim : Module.finrank (ZMod 2) ↥(fixedSpace ρ B ⊔ fixedSpace ρ C) =
      Module.finrank (ZMod 2) (fixedSpace ρ (B ⊓ C)) := by omega
  refine ⟨⟨inf_le_left.trans hB.1, ?_⟩,
    (Submodule.eq_of_le_of_finrank_eq hle heqdim).symm⟩
  unfold weight
  omega

/-- Equality in the single-vector replacement bound identifies its entire fixed space. -/
theorem IsBestOffender.fixedSpace_replacement {A : Subgroup G}
    (hA : IsBestOffender ρ A) (v : V) :
    fixedSpace ρ (replacementSubgroup ρ A v) =
      displacementSpan ρ A v ⊔ fixedSpace ρ A := by
  have hle : displacementSpan ρ A v ⊔ fixedSpace ρ A ≤
      fixedSpace ρ (replacementSubgroup ρ A v) :=
    sup_le (displacementSpan_le_fixedSpace_replacement ρ A v)
      (fixedSpace_antitone ρ (replacementSubgroup_le ρ A v))
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hb := replacement_rank_bound ρ hA.1 v
  have he := (hA.replacement_equalWeightLE ρ v).2
  have hm := Submodule.finrank_mono hle
  unfold weight at hb he
  omega

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem displacement_mem_span {A : Subgroup G} (hA : IsElementaryTwo A)
    {b : G} (hb : b ∈ A) (v : V) {w : V} (hw : w ∈ displacementSpan ρ A v) :
    ρ b w - w ∈ displacementSpan ρ A (ρ b v - v) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, ha, rfl⟩ := hw
    rw [displacement_commute ρ hA hb ha]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have he : ρ b (x + y) - (x + y) = (ρ b x - x) + (ρ b y - y) := by
      rw [map_add]; abel
    rw [he]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ c hx

/-- Intersecting an equal-weight best offender with a single-vector replacement
never produces the trivial group. -/
theorem IsBestOffender.inf_replacement_ne_bot {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hB : EqualWeightLE ρ B A) (hne : B ≠ ⊥) (v : V) :
    B ⊓ replacementSubgroup ρ A v ≠ ⊥ := by
  intro hbot
  have hfix := (hA.inf_equalWeightLE_fixedSpace ρ hB
    (hA.replacement_equalWeightLE ρ v)).2
  rw [hbot, fixedSpace_bot, hA.fixedSpace_replacement ρ v] at hfix
  have hv : v ∈ fixedSpace ρ B ⊔ (displacementSpan ρ A v ⊔ fixedSpace ρ A) := by
    rw [← hfix]; trivial
  obtain ⟨x, hx, y, hy, hv⟩ := Submodule.mem_sup.mp hv
  obtain ⟨w, hw, z, hz, hy⟩ := Submodule.mem_sup.mp hy
  have hBR : B ≤ replacementSubgroup ρ A v := by
    intro b hb
    apply (mem_replacementSubgroup_iff_displacement ρ hA.1 (hB.1 hb) v).mpr
    have hbx : ρ b x = x := (Representation.mem_invariants _ _).mp hx ⟨b, hb⟩
    have hbz : ρ b z = z := (Representation.mem_invariants _ _).mp hz ⟨b, hB.1 hb⟩
    have he : ρ b v - v = ρ b w - w := by
      rw [← hv, ← hy, map_add, map_add, hbx, hbz]
      abel
    have hm : ρ b v - v ∈ displacementSpan ρ A (ρ b v - v) :=
      he.symm ▸ displacement_mem_span ρ hA.1 (hB.1 hb) v hw
    exact (mem_displacementSpan_sup_fixedSpace_iff ρ hA.1 (ρ b v - v)).mp
      (Submodule.mem_sup_left hm)
  apply hne
  rw [← hbot, inf_eq_left.mpr hBR]

private theorem finite_replacement_intersection {A : Subgroup G}
    (hA : IsBestOffender ρ A) (s : Finset V) :
    EqualWeightLE ρ (A ⊓ s.inf (replacementSubgroup ρ A)) A ∧
      A ⊓ s.inf (replacementSubgroup ρ A) ≠ ⊥ ∧
      fixedSpace ρ (A ⊓ s.inf (replacementSubgroup ρ A)) =
        s.sup (displacementSpan ρ A) ⊔ fixedSpace ρ A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.inf_empty, inf_top_eq, Finset.sup_empty, bot_sup_eq]
    exact ⟨EqualWeightLE.refl ρ A, hA.1.1, True.intro⟩
  | @insert v s hv ih =>
    have he : A ⊓ (insert v s).inf (replacementSubgroup ρ A) =
        (A ⊓ s.inf (replacementSubgroup ρ A)) ⊓ replacementSubgroup ρ A v := by
      rw [Finset.inf_insert]
      ac_rfl
    rw [he]
    obtain ⟨hw, hf⟩ := hA.inf_equalWeightLE_fixedSpace ρ ih.1
      (hA.replacement_equalWeightLE ρ v)
    refine ⟨hw, hA.inf_replacement_ne_bot ρ ih.1 ih.2.1 v, ?_⟩
    rw [hf, ih.2.2, hA.fixedSpace_replacement ρ v, Finset.sup_insert]
    simp only [sup_assoc, sup_comm, sup_left_comm, sup_idem]

/-- Timmesfeld replacement for the actual centralizer of all displacements,
including its full fixed-space formula. The binary argument does not require faithfulness. -/
theorem IsBestOffender.displacementCentralizer_replacement {A : Subgroup G}
    (hA : IsBestOffender ρ A) :
    EqualWeightLE ρ (displacementCentralizer ρ A) A ∧
      displacementCentralizer ρ A ≠ ⊥ ∧
      fixedSpace ρ (displacementCentralizer ρ A) =
        (⨆ v : V, displacementSpan ρ A v) ⊔ fixedSpace ρ A := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  have he : displacementCentralizer ρ A =
      A ⊓ Finset.univ.inf (replacementSubgroup ρ A) := by
    ext c
    simp only [mem_displacementCentralizer, Subgroup.mem_inf, Finset.inf_eq_iInf,
      Subgroup.mem_iInf, Finset.mem_univ, iInf_true, mem_replacementSubgroup_iff]
    constructor
    · rintro ⟨hc, h⟩
      exact ⟨hc, fun v => ⟨hc, fun a ha => h a ha v⟩⟩
    · rintro ⟨hc, h⟩
      exact ⟨hc, fun a ha v => (h v).2 a ha⟩
  rw [he]
  simpa only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_true] using
    finite_replacement_intersection ρ hA Finset.univ

/-- The full displacement centralizer is a nontrivial subgroup of equal weight. -/
theorem IsBestOffender.displacementCentralizer_equalWeightLE {A : Subgroup G}
    (hA : IsBestOffender ρ A) : EqualWeightLE ρ (displacementCentralizer ρ A) A :=
  (hA.displacementCentralizer_replacement ρ).1

/-- Nontriviality in Timmesfeld's replacement theorem. -/
theorem IsBestOffender.displacementCentralizer_ne_bot {A : Subgroup G}
    (hA : IsBestOffender ρ A) : displacementCentralizer ρ A ≠ ⊥ :=
  (hA.displacementCentralizer_replacement ρ).2.1

/-- The precise fixed-space clause of Timmesfeld's replacement theorem. -/
theorem IsBestOffender.fixedSpace_displacementCentralizer {A : Subgroup G}
    (hA : IsBestOffender ρ A) :
    fixedSpace ρ (displacementCentralizer ρ A) =
      (⨆ v : V, displacementSpan ρ A v) ⊔ fixedSpace ρ A :=
  (hA.displacementCentralizer_replacement ρ).2.2

/-- The actual full displacement centralizer is itself a best offender. -/
theorem IsBestOffender.displacementCentralizer_isBestOffender {A : Subgroup G}
    (hA : IsBestOffender ρ A) : IsBestOffender ρ (displacementCentralizer ρ A) :=
  hA.of_equalWeightLE ρ
    (displacementCentralizer_isElementaryTwo ρ hA.1 (hA.displacementCentralizer_ne_bot ρ))
    (hA.displacementCentralizer_equalWeightLE ρ)

/-- The multiplicative weight equality in GLS Theorem 26.23(i). -/
theorem IsBestOffender.displacementCentralizer_cardinality {A : Subgroup G}
    (hA : IsBestOffender ρ A) :
    Nat.card (displacementCentralizer ρ A) *
        Nat.card (fixedSpace ρ (displacementCentralizer ρ A)) =
      Nat.card A * Nat.card (fixedSpace ρ A) := by
  have hC := hA.displacementCentralizer_isBestOffender ρ
  have hcard (B : Subgroup G) : Nat.card (fixedSpace ρ B) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ B) := by
    simp only [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ B),
      Nat.card_eq_fintype_card, ZMod.card]
  rw [hC.1.card_eq_two_pow_rank, hA.1.card_eq_two_pow_rank,
    hcard, hcard, ← pow_add, ← pow_add]
  exact congrArg (fun n : ℕ => 2 ^ n) (hA.displacementCentralizer_equalWeightLE ρ).2

end Representation.BinaryOffender
