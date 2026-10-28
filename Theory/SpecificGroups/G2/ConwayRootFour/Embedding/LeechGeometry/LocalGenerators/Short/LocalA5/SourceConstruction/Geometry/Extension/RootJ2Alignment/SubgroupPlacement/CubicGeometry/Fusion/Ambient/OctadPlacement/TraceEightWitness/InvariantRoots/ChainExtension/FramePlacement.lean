module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.OrthogonalPair
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.Conditional

/-!
# Marked D₄ placement in the Leech lattice

Every four-vector configuration with the specified scaled D₄ Gram matrix is
carried, with all signs and labels retained, to the standard coordinate frame.
After placing the first orthogonal pair, the Gram equations force a coordinate
of magnitude four in each remaining minimal vector. The even minimal-shell
classification gives its other coordinate; orthogonality separates those two
positions. Golay restriction prescribes their signs while fixing the first
pair, and Mathieu four-transitivity places all four coordinate positions.

The final applications discharge the marked-placement premise of the cubic
chain-extension consumers. The independent normalized six-vector completion
remains explicit in the combined extension theorem.

Source context: Aschbacher, *Sporadic Groups* (1994), Chapter 8, especially
22.13. This marked placement is an additional coordinate argument, using the
checked shell, Golay-restriction and Mathieu-transitivity APIs of the ATLAS port.
-/

open Atlas.Lattices Atlas.Codes Atlas.Conway
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness.ChainExtension
@[expose] public noncomputable section

private theorem sparse_of_marked_four (x : leech) (a b : Omega)
    (hn : integerDot x.val x.val = 32) (ha : x.val a = 0) (hb : x.val b = -4) :
    ∃ c : Omega, c ≠ a ∧ c ≠ b ∧ (x.val c = 4 ∨ x.val c = -4) ∧
      x.val = coordinateVector c (x.val c) - coordinateVector b 4 := by
  classical
  have hp : ∀ i, x.val i % 2 = 0 := by
    rcases leech_coordinate_parity x.val x.prop with h | h
    · exact h
    · have h := h b
      omega
  have hf : x.val ∈ twoFourFamily 0 2 := by
    rcases Finset.mem_union.mp ((even_minimal_shell_iff x.val).mp ⟨x.prop, hp, hn⟩) with h | h
    · exact h
    · obtain ⟨T, _, _, s, _, hs⟩ := minimum_octad_parameterization x h
      have hh := congrFun hs b
      simp only [signedSupport] at hh
      split_ifs at hh <;> omega
  obtain ⟨T, hT, s, hs⟩ := minimum_four_parameterization x hf
  have hbT : b ∈ T := by
    by_contra h
    have hh := congrFun hs b
    simp [signedSupport, h] at hh
    omega
  have herase : (T.erase b).card = 1 := by rw [Finset.card_erase_of_mem hbT, hT]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp herase
  have hcT : c ∈ T := Finset.mem_of_mem_erase (by rw [hc]; simp)
  have hcb : c ≠ b := (Finset.mem_erase.mp (show c ∈ T.erase b by rw [hc]; simp)).1
  have hpair : T = {b,c} := by rw [← Finset.insert_erase hbT, hc]
  have hxc : x.val c = 4 ∨ x.val c = -4 := by
    rw [hs]
    simp only [signedSupport, dif_pos hcT]
    split_ifs <;> norm_num
  have hca : c ≠ a := by rintro rfl; omega
  refine ⟨c, hca, hcb, hxc, ?_⟩
  funext i
  by_cases hic : i = c
  · subst i
    simp [coordinateVector, hcb]
  · by_cases hib : i = b
    · subst i
      simp [coordinateVector, hic, hb]
    · have hiT : i ∉ T := by simp [hpair, hib, hic]
      simp [hs, signedSupport, hiT, coordinateVector, hib, hic]

private theorem marked_dot_sub_right (x y z : IntegerCoordinates) :
    integerDot x (y - z) = integerDot x y - integerDot x z := by
  simp [integerDot, mul_sub, Finset.sum_sub_distrib]

private theorem marked_pair_minus_dot (a b : Omega) (x : IntegerCoordinates) :
    integerDot (minimumPairMinus a b).val x = 4 * (x a - x b) := by
  rw [integerDot_comm]
  change integerDot x (coordinateVector a 4 - coordinateVector b 4) = _
  rw [marked_dot_sub_right, integerDot_coordinateVector, integerDot_coordinateVector]
  ring

private theorem sign_coordinate (s : golay) (a : Omega) (k : ℤ) :
    signChange s.val (coordinateVector a k) =
      coordinateVector a (if s.val a = 0 then k else -k) := by
  classical
  funext i
  by_cases hi : i = a
  · subst i
    simp [signChange, coordinateVector]
  · simp [signChange, coordinateVector, hi]

private theorem sign_pair_fixed (s : golay) (a b : Omega)
    (ha : s.val a = 0) (hb : s.val b = 0) :
    (signIsometry s).val (minimumPairPlus a b) = minimumPairPlus a b ∧
    (signIsometry s).val (minimumPairMinus a b) = minimumPairMinus a b := by
  constructor <;> apply Subtype.ext
  · change signChange s.val (coordinateVector a 4 + coordinateVector b 4) = _
    rw [map_add, sign_coordinate, sign_coordinate, ha, hb]
    rfl
  · change signChange s.val (coordinateVector a 4 - coordinateVector b 4) = _
    rw [map_sub, sign_coordinate, sign_coordinate, ha, hb]
    rfl

private theorem sign_sparse_pair (s : golay) (x : leech) (b c : Omega)
    (hx : x.val = coordinateVector c (x.val c) - coordinateVector b 4)
    (hc : x.val c = 4 ∨ x.val c = -4)
    (hsb : s.val b = 0) (hsc : s.val c = if x.val c = 4 then 0 else 1) :
    (signIsometry s).val x = minimumPairMinus c b := by
  apply Subtype.ext
  change signChange s.val x.val = _
  rw [hx, map_sub, sign_coordinate, sign_coordinate, hsb, hsc]
  rcases hc with hc | hc <;> norm_num [hc, minimumPairMinus]

private theorem marked_signs (a b c d : Omega)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d)
    (u v : Bit) : ∃ s : golay,
      s.val a = 0 ∧ s.val b = 0 ∧ s.val c = u ∧ s.val d = v := by
  classical
  let T : Finset Omega := {a, b, c, d}
  have hT : T.card < 8 := by
    have h₁ := Finset.card_insert_le a ({b,c,d} : Finset Omega)
    have h₂ := Finset.card_insert_le b ({c,d} : Finset Omega)
    have h₃ := Finset.card_insert_le c ({d} : Finset Omega)
    have h₄ : ({d} : Finset Omega).card = 1 := Finset.card_singleton d
    dsimp [T]
    omega
  obtain ⟨s, hs⟩ := golay_small_restriction_surjective T hT
    (fun i => if i.val = c then u else if i.val = d then v else 0)
  have he (i : Omega) (hi : i ∈ T) :
      s.val i = if i = c then u else if i = d then v else 0 := congrFun hs ⟨i, hi⟩
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · simpa [Ne.symm hca, Ne.symm hda] using he a (by simp [T])
  · simpa [Ne.symm hcb, Ne.symm hdb] using he b (by simp [T])
  · simpa using he c (by simp [T])
  · simpa [Ne.symm hcd] using he d (by simp [T])

private theorem marked_permutation (a b c d : Omega)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) :
    ∃ p : Mathieu24CodeModel,
      p.val a = frameCoordinate 0 ∧ p.val b = frameCoordinate 1 ∧
      p.val c = frameCoordinate 2 ∧ p.val d = frameCoordinate 3 := by
  let e : Fin 4 ↪ Omega := ⟨![a,b,c,d], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let f : Fin 4 ↪ Omega := ⟨frameCoordinate, by
    intro i j h
    exact congrArg Prod.snd h⟩
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 4 := by
    let := mathieu24_five_transitive
    exact MulAction.isMultiplyPretransitive_of_le (by decide : 4 ≤ 5)
      (by norm_num [Omega, HexIndex])
  obtain ⟨p, hp⟩ := MulAction.isMultiplyPretransitive_iff.mp ht e f
  exact ⟨p, congrArg (fun e => e 0) hp, congrArg (fun e => e 1) hp,
    congrArg (fun e => e 2) hp, congrArg (fun e => e 3) hp⟩

/-- All four signed roots of a scaled D₄ configuration can be placed exactly
in the first coordinate tetrad of the literal Leech lattice. -/
theorem d4FramePlacement : D4FramePlacement := by
  classical
  intro f
  obtain ⟨g, hg0, hg1⟩ := f.place_first_pair
  let a := frameCoordinate 0
  let b := frameCoordinate 1
  let x := g.val (f.root 2)
  let y := g.val (f.root 3)
  have hab : a ≠ b := by decide
  have hgram (i j : Fin 4) :
      integerDot (g.val (f.root i)).val (g.val (f.root j)).val = 8 * d4Gram i j := by
    rw [g.prop, ← leechIntegralPairing_mul, f.gram]
  have hn (i : Fin 4) : integerDot (g.val (f.root i)).val (g.val (f.root i)).val = 32 := by
    rw [hgram]
    fin_cases i <;> norm_num [d4Gram]
  have hplus (i : Fin 4) :
      4 * ((g.val (f.root i)).val a + (g.val (f.root i)).val b) = 8 * d4Gram 0 i := by
    have h := hgram 0 i
    rw [hg0] at h
    exact (minimumPairPlus_dot a b _).symm.trans h
  have hminus (i : Fin 4) :
      4 * ((g.val (f.root i)).val a - (g.val (f.root i)).val b) = 8 * d4Gram 1 i := by
    have h := hgram 1 i
    rw [hg1] at h
    exact (marked_pair_minus_dot a b _).symm.trans h
  have hx : x.val a = 0 ∧ x.val b = -4 := by
    have h₁ := hplus 2
    have h₂ := hminus 2
    change 4 * (x.val a + x.val b) = -16 at h₁
    change 4 * (x.val a - x.val b) = 16 at h₂
    omega
  have hy : y.val b = 0 ∧ y.val a = -4 := by
    have h₁ := hplus 3
    have h₂ := hminus 3
    change 4 * (y.val a + y.val b) = -16 at h₁
    change 4 * (y.val a - y.val b) = -16 at h₂
    omega
  obtain ⟨c, hca, hcb, hxc, hxs⟩ := sparse_of_marked_four x a b (hn 2) hx.1 hx.2
  obtain ⟨d, hdb, hda, hyd, hys⟩ := sparse_of_marked_four y b a (hn 3) hy.1 hy.2
  have hxy : integerDot y.val x.val = 0 := by
    simpa [x, y, d4Gram] using hgram 3 2
  have hcd : c ≠ d := by
    intro h
    rw [hxs, marked_dot_sub_right, integerDot_coordinateVector,
      integerDot_coordinateVector, hy.1, zero_mul, sub_zero, h] at hxy
    rw [h] at hxc
    rcases hxc with hc | hc <;> rcases hyd with hd | hd <;> nlinarith
  obtain ⟨s, hsa, hsb, hsc, hsd⟩ := marked_signs a b c d hca hcb hda hdb hcd
    (if x.val c = 4 then 0 else 1) (if y.val d = 4 then 0 else 1)
  have hsx := sign_sparse_pair s x b c hxs hxc hsb hsc
  have hsy := sign_sparse_pair s y a d hys hyd hsa hsd
  have hsp := sign_pair_fixed s a b hsa hsb
  obtain ⟨p, hpa, hpb, hpc, hpd⟩ := marked_permutation a b c d hab hca hcb hda hdb hcd
  refine ⟨permutationEmbedding p * signIsometry s * g, ?_⟩
  intro i
  change (permutationEmbedding p).val ((signIsometry s).val (g.val (f.root i))) = _
  fin_cases i
  · change (permutationEmbedding p).val ((signIsometry s).val (g.val (f.root 0))) = standardD4 0
    rw [hg0]
    change (permutationEmbedding p).val ((signIsometry s).val (minimumPairPlus a b)) = _
    rw [hsp.1, (permutation_minimumPair p a b).1, hpa, hpb]
    rfl
  · change (permutationEmbedding p).val ((signIsometry s).val (g.val (f.root 1))) = standardD4 1
    rw [hg1]
    change (permutationEmbedding p).val ((signIsometry s).val (minimumPairMinus a b)) = _
    rw [hsp.2, (permutation_minimumPair p a b).2, hpa, hpb]
    rfl
  · change (permutationEmbedding p).val ((signIsometry s).val x) = _
    rw [hsx, (permutation_minimumPair p c b).2, hpc, hpb]
    rfl
  · change (permutationEmbedding p).val ((signIsometry s).val y) = _
    rw [hsy, (permutation_minimumPair p d a).2, hpd, hpa]
    rfl

/-- The length-two chain-extension consumer, with its marked placement
premise discharged. -/
theorem extend_two {r : LeechIsometryGroup} (c : CubicRootChain r 2)
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) :
    ∃ y : leech, integerDot y.val y.val = 32 ∧
      (∀ i, leechIntegralPairing (c.root i) y = 0) ∧
      ∀ i, leechIntegralPairing (c.root i) (r.val y) =
        if i.val + 1 = 2 then -2 else 0 :=
  c.extend_two_of_d4_placement d4FramePlacement hp

/-- Both chain-extension consumers now require only the independent normalized
six-vector completion. Its proof remains with the chain-extension assembly. -/
theorem cubicChainExtension_of_normalized_completion
    (hcomplete : NormalizedThirdOrbitCompletion) : CubicChainExtension :=
  cubicChainExtension_of_coordinate_geometry d4FramePlacement hcomplete

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness.ChainExtension
