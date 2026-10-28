module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Separation

/-!
# The graph centralizer cardinal bound

The chain fixing 48, 191, 877, 65, 0, 1, 2 has orbit bounds
42, 8, 2, 4, 4, 2, 2, and trivial terminal stabilizer.
This is a bound for the full graph-preserving centralizer of the involution.
Source lead: GLS3 Table 5.3p; all concrete inequalities follow from the certificates.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds

open NormalizerGraph.CardBound

private abbrev S0 := ↥graphCentralizer
private abbrev S1 := ↥(MulAction.stabilizer S0 (48 : Fin 2058))
private abbrev S2 := ↥(MulAction.stabilizer S1 (191 : Fin 2058))
private abbrev S3 := ↥(MulAction.stabilizer S2 (877 : Fin 2058))
private abbrev S4 := ↥(MulAction.stabilizer S3 (65 : Fin 2058))
private abbrev S5 := ↥(MulAction.stabilizer S4 (0 : Fin 2058))
private abbrev S6 := ↥(MulAction.stabilizer S5 (1 : Fin 2058))
private abbrev S7 := ↥(MulAction.stabilizer S6 (2 : Fin 2058))

private theorem fixes1 (g : S1) : ∀ b ∈ [48], g.val.val b = b := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  exact g.property

private theorem fixes2 (g : S2) : ∀ b ∈ [48, 191], g.val.val.val b = b := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact g.val.property
  · exact g.property

private theorem fixes3 (g : S3) : ∀ b ∈ [48, 191, 877], g.val.val.val.val b = b := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact g.val.val.property
  · exact g.val.property
  · exact g.property

private theorem fixes4 (g : S4) : ∀ b ∈ [48, 191, 877, 65], g.val.val.val.val.val b = b := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact g.val.val.val.property
  · exact g.val.val.property
  · exact g.val.property
  · exact g.property

private theorem fixes5 (g : S5) : ∀ b ∈ [48, 191, 877, 65, 0], g.val.val.val.val.val.val b = b := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact g.val.val.val.val.property
  · exact g.val.val.val.property
  · exact g.val.val.property
  · exact g.val.property
  · exact g.property

private theorem fixes6 (g : S6) : ∀ b ∈ [48, 191, 877, 65, 0, 1], g.val.val.val.val.val.val.val b = b := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact g.val.val.val.val.val.property
  · exact g.val.val.val.val.property
  · exact g.val.val.val.property
  · exact g.val.val.property
  · exact g.val.property
  · exact g.property

private theorem fixes7 (g : S7) : ∀ b ∈ [48, 191, 877, 65, 0, 1, 2], g.val.val.val.val.val.val.val.val b = b := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact g.val.val.val.val.val.val.property
  · exact g.val.val.val.val.val.property
  · exact g.val.val.val.val.property
  · exact g.val.val.val.property
  · exact g.val.val.property
  · exact g.val.property
  · exact g.property

public theorem graphCentralizer_card_le : Nat.card graphCentralizer ≤ 43008 := by
  have h7 : Nat.card S7 = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, fun g => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact seven_fixed_eq_one _ g.val.val.val.val.val.val.val.property (fixes7 g)
  have h6 : Nat.card S6 ≤ 2 * Nat.card S7 :=
    orbit_upper (2 : Fin 2058) (fun x => weight61 x.val)
      (fun g x => invariant61 _ g.val.val.val.val.val.val.property (fixes6 g) x) cell6_card.le
  have h5 : Nat.card S5 ≤ 2 * Nat.card S6 :=
    orbit_upper (1 : Fin 2058) (fun x => weight51 x.val)
      (fun g x => invariant51 _ g.val.val.val.val.val.property (fixes5 g) x) cell5_card.le
  have h4 : Nat.card S4 ≤ 4 * Nat.card S5 :=
    orbit_upper (0 : Fin 2058) (fun x => weight41 x.val)
      (fun g x => invariant41 _ g.val.val.val.val.property (fixes4 g) x) cell4_card.le
  have h3 : Nat.card S3 ≤ 4 * Nat.card S4 :=
    orbit_upper (65 : Fin 2058) (fun x => weight31 x.val)
      (fun g x => invariant31 _ g.val.val.val.property (fixes3 g) x) cell3_card.le
  have h2 : Nat.card S2 ≤ 2 * Nat.card S3 :=
    orbit_upper (877 : Fin 2058) (fun x => weight21 x.val)
      (fun g x => invariant21 _ g.val.val.property (fixes2 g) x) cell2_card.le
  have h1 : Nat.card S1 ≤ 8 * Nat.card S2 :=
    orbit_upper (191 : Fin 2058) (fun x => weight11 x.val)
      (fun g x => invariant11 _ g.val.property (fixes1 g) x) cell1_card.le
  have h0 : Nat.card S0 ≤ 42 * Nat.card S1 :=
    orbit_upper (48 : Fin 2058) (fun x => weight00 x.val)
      (fun g x => invariant00 _ g.property (by simp) x) cell0_card.le
  change Nat.card S0 ≤ 43008
  omega

end Held.TwoLocalCandidates.CentralInvolutionBounds
