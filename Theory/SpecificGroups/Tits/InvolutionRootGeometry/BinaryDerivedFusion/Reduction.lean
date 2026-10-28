module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.MarkedParabolics
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.BlockProduct
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization
-- Internal specification of the existing layout: only the proof of
-- `positive_blocks` uses the hidden construction. Its body is not re-exposed.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.BinaryCommutation

/-!
# Internal fusion in the derived binary Ree group

The actual binary fixed block coordinates show that the eight relative-root
words generate U. Parrott’s substitutions identify their images modulo the
derived group. In particular u₁ and u₃ lie in the outer coset: otherwise the
whole group U of order 4096 lies in the derived group of order 17971200.

The first word centralizes the marked long involution, which is its square.
Six explicit nonnegative root inner products show that the third word
centralizes the marked short involution. Multiplying an outer conjugator by
one of these centralizers corrects its coset, proving internal fusion for both
representatives without an automorphism-coverage assumption.

Finally `atlas_sylow_map` expresses every outer positive element as u₁ times
a marked Atlas Sylow normal form. Excluding square one in those 2048 words
is retained as an explicit finite-check premise; it is not asserted here.

Source: Parrott (1972), §5, printed p.683; GLS3 Table 2.4 and 2.4.5(d),
`refs/KGroup/GLS3/chapter2.tex`. Application: Aschbacher–Smith 16.1.4,
printed p.1171, with the literal binary Ree and Tits carriers distinguished.
-/

public section
noncomputable section
namespace Tits.InvolutionRootGeometry.BinaryDerivedFusion
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds ReeF4.DerivedTits.Realization
open ReeF4.Parabolics.RadicalCoordinates
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Subgroup

private theorem binary_cases (a : CoefficientField 0) : a = 0 ∨ a = 1 := by
  have h : a * (a - 1) = 0 := by
    have hp := field_pow 0 a
    norm_num at hp
    calc
      a * (a - 1) = a ^ 2 - a := by ring
      _ = 0 := sub_eq_zero.mpr hp
  exact (mul_eq_zero.mp h).imp_right sub_eq_zero.mp

private theorem root_zero (r : Theory.AlgebraicGroup.F4Chevalley.Root) :
    rootGeneratorInGroup 0 r 0 = 1 :=
  Subtype.ext (Theory.AlgebraicGroup.F4Chevalley.rootCurve_zero r)

private theorem root_word_zero (i : Fin 8) : rootWord 0 i 0 = 1 := by
  simp [rootWord, root_zero]

private theorem central_word_zero (i : Fin 8) : centralWord 0 i 0 = 1 := by
  simp [centralWord, root_zero]

private theorem positive_blocks : positiveRootWordLayout.blocks = rootBlocks .positive := by
  rfl

attribute [local irreducible] positiveRootWordLayout

private theorem quartet_solution_mem (K : Subgroup (SplitGroup 0))
    (i : Fin 4) (h : quartetElement i ∈ K) (a c : CoefficientField 0) :
    quartetWord 0 (quartetRoots i) (quartetSolution 0 a c) ∈ K := by
  let L := positiveRootWordLayout
  let j := L.quartetIndex i
  let r := rootWord 0 j 1
  let z := centralWord 0 j 1
  have hB : L.blocks = rootBlocks .positive := positive_blocks
  have hr : r * r = z := by
    simpa [r, z, j, root_word_zero, CharTwo.add_self_eq_zero] using
      MatrixRelations.rootWord_even_mul 0 j (L.quartet_even i) 1 1
  have hz : z * z = 1 := by
    have hc := L.quartet_top_commute 0 (mixedRootCommutation 0) i
      (1 : CoefficientField 0) (1 : CoefficientField 0)
    have hs (s : Theory.AlgebraicGroup.F4Chevalley.Root) :
        rootGeneratorInGroup 0 s 1 * rootGeneratorInGroup 0 s 1 = 1 := by
      rw [← show rootGeneratorInGroup 0 s (1 + 1) = _ from
        (show rootGeneratorInGroup 0 s (1 + 1) =
          rootGeneratorInGroup 0 s 1 * rootGeneratorInGroup 0 s 1 from
          Subtype.ext (Theory.AlgebraicGroup.F4Chevalley.rootCurve_add s (1 : CoefficientField 0) 1))]
      simp [CharTwo.add_self_eq_zero, root_zero]
    dsimp only [z, centralWord]
    simp only [map_one]
    rw [hc.symm.mul_mul_mul_comm, hs, hs, one_mul]
  have hq : quartetElement i = r * z := by
    have hh := L.quartet_factorization 0 (mixedRootCommutation 0) i 1 0
    rw [hB] at hh
    change quartetWord 0 (fun s => ((rootBlocks .positive).roots (.inr (i, s))).val)
      (quartetSolution 0 1 0) = r * z
    simpa only [r, z, j, map_zero, map_one, one_mul, zero_add] using hh
  have hrmem : r ∈ K := by
    have hqr : quartetElement i * r = 1 := by
      rw [hq, ← hr]
      calc
        r * (r * r) * r = (r * r) * (r * r) := by simp only [mul_assoc]
        _ = 1 := by rw [hr, hz]
    have he : r = (quartetElement i)⁻¹ := by
      simpa only [inv_mul_cancel_left, mul_one] using
        congrArg (fun v => (quartetElement i)⁻¹ * v) hqr
    rw [he]
    exact K.inv_mem h
  have hzmem : z ∈ K := hr ▸ K.mul_mem hrmem hrmem
  have hf := L.quartet_factorization 0 (mixedRootCommutation 0) i a c
  rw [hB] at hf
  rw [show quartetWord 0 (quartetRoots i) (quartetSolution 0 a c) = _ from hf]
  apply K.mul_mem
  · rcases binary_cases a with rfl | rfl
    · rw [root_word_zero]; exact K.one_mem
    · exact hrmem
  · rcases binary_cases (titsEnd 0 c + a * titsEnd 0 a) with he | he
    · rw [he, central_word_zero]; exact K.one_mem
    · rw [he]; exact hzmem

/-- The actual eight binary root elements, regarded in the fixed group. -/
@[expose] def fixedU (i : Fin 8) : Model 0 :=
  ⟨u i, (mem_fixedSubgroup 0 _).mpr (u_fixed i)⟩

/-- Positive fixed coordinates generate the binary unipotent subgroup. -/
theorem unipotent_le_of_fixedU_mem (K : Subgroup (Model 0))
    (h : ∀ i, fixedU i ∈ K) : unipotent 0 ≤ K := by
  let J := K.map (toSplitGroup 0)
  have hu (i : Fin 8) : u i ∈ J := ⟨fixedU i, h i, by simp [fixedU, toSplitGroup_apply]⟩
  have hp (i : Fin 4) : pairElement i ∈ J := by
    fin_cases i
    · exact hu 7
    · exact hu 1
    · exact hu 5
    · exact hu 3
  have hq (i : Fin 4) : quartetElement i ∈ J := by
    fin_cases i
    · exact hu 0
    · exact hu 4
    · exact hu 6
    · exact hu 2
  intro x hx
  let B := rootBlocks .positive
  obtain ⟨t, ht⟩ := (wordInSubgroup_bijective 0 B.order).2 ⟨toSplitGroup 0 x, hx⟩
  have hw : word 0 B.order t = toSplitGroup 0 x := congrArg Subtype.val ht
  let p := B.repack 0 t
  have hfixed : blockTwist 0 p = p := by
    apply B.blockWord_injective 0 (wordInSubgroup_bijective 0 B.order)
    rw [← B.twist_blockWord 0 (mixedRootCommutation 0) (b2RootSwap 0)]
    change reeTwist 0 (B.blockWord 0 (B.repack 0 t)) = B.blockWord 0 (B.repack 0 t)
    rw [← B.word_eq_blockWord, hw]
    exact (mem_fixedSubgroup 0 _).mp (by simpa only [toSplitGroup_apply] using x.property)
  have hxJ : toSplitGroup 0 x ∈ J := by
    rw [← hw, B.word_eq_blockWord]
    apply J.mul_mem
    · apply J.list_prod_mem
      intro y hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      have he := (pairTwist_fixed_iff 0 (p.1 i)).mp
        (congrFun (congrArg Prod.fst hfixed) i)
      change pairWord 0 (pairRoots i) (p.1 i) ∈ J
      rw [he]
      rcases binary_cases (p.1 i 0) with ha | ha
      · simp [ha, pairWord, pairSolution, root_zero]
      · simpa only [ha, pairElement] using hp i
    · apply J.list_prod_mem
      intro y hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      have he := (quartetTwist_fixed_iff 0 (p.2 i)).mp
        (congrFun (congrArg Prod.snd hfixed) i)
      change quartetWord 0 (quartetRoots i) (p.2 i) ∈ J
      rw [he]
      exact quartet_solution_mem J i (hq i) _ _
  obtain ⟨y, hy, he⟩ := hxJ
  exact (toSplitGroup_injective 0 he) ▸ hy
open Tits.ExceptionalParabolics.FullRee

private theorem fixed_word_mem (x : Model 0) (i : ParrottGenerator)
    (h : toSplitGroup 0 x = assignment i) : x ∈ commutator (Model 0) := by
  have he : x = atlasEmbedding (atlas1600ParrottAssignment i) :=
    toSplitGroup_injective 0 (h.trans (atlasEmbedding_generator_matrix i).symm)
  rw [he, ← atlasEmbedding_range]
  exact ⟨_, rfl⟩

@[simp] theorem fixedU_matrix (i : Fin 8) : toSplitGroup 0 (fixedU i) = u i := by
  simp [fixedU, toSplitGroup_apply]

/-- The first quartet generator lies outside the derived subgroup. Otherwise
Parrott’s marked words and positive coordinates put all of U in it, contradicting
the proved orders 4096 and 17971200. -/
theorem fixedU_zero_not_mem : fixedU 0 ∉ commutator (Model 0) := by
  intro h0
  have h (i : Fin 8) : fixedU i ∈ commutator (Model 0) := by
    have h3 : fixedU 0 * fixedU 2 ∈ commutator (Model 0) :=
      fixed_word_mem _ .s3 (by simp only [map_mul, fixedU_matrix]; rfl)
    have h5 : fixedU 0 * fixedU 4 ∈ commutator (Model 0) :=
      fixed_word_mem _ .s5 (by simp only [map_mul, fixedU_matrix]; rfl)
    have h7 : fixedU 6 * (fixedU 0)⁻¹ ∈ commutator (Model 0) :=
      fixed_word_mem _ .s7 (by simp only [map_mul, map_inv, fixedU_matrix]; rfl)
    fin_cases i
    · exact h0
    · exact fixed_word_mem _ .s2 (fixedU_matrix 1)
    · exact (mul_mem_cancel_left h0).mp h3
    · exact fixed_word_mem _ .s4 (fixedU_matrix 3)
    · exact (mul_mem_cancel_left h0).mp h5
    · exact fixed_word_mem _ .s6 (fixedU_matrix 5)
    · exact (mul_mem_cancel_right ((commutator (Model 0)).inv_mem h0)).mp h7
    · exact fixed_word_mem _ .s8 (fixedU_matrix 7)
  have hd := Subgroup.card_dvd_of_le (unipotent_le_of_fixedU_mem _ h)
  have hc : Nat.card (commutator (Model 0)) = 17971200 :=
    (Nat.card_congr atlasDerivedEquiv.toEquiv).symm.trans atlas1600Group_card
  rw [sylow_card, hc] at hd
  norm_num at hd

/-- The third relative-root generator represents the same outer coset. -/
theorem fixedU_two_not_mem : fixedU 2 ∉ commutator (Model 0) := by
  intro h2
  apply fixedU_zero_not_mem
  have h3 : fixedU 0 * fixedU 2 ∈ commutator (Model 0) :=
    fixed_word_mem _ .s3 (by simp only [map_mul, fixedU_matrix]; rfl)
  exact (mul_mem_cancel_right h2).mp h3

private theorem fixedU_zero_commutes_long : Commute (fixedU 0) (longRoot : Model 0) := by
  apply toSplitGroup_injective 0
  simp only [map_mul, fixedU_matrix, longRoot_matrix, u, Matrix.cons_val_zero]
  exact (Commute.self_pow (quartetElement 0) 2).eq

private theorem fixedU_two_commutes_short : Commute (fixedU 2) (shortRoot : Model 0) := by
  apply toSplitGroup_injective 0
  simp only [map_mul, fixedU_matrix, shortRoot_matrix, u, Matrix.cons_val_two]
  exact quartet_three_commutes_pair_three.eq

/-- Correct an ambient conjugator by an element of the other coset that
centralizes its source. Both the subgroup and its conjugation are literal. -/
private theorem isConj_of_index_two {G : Type*} [Group G] (H : Subgroup G)
    (hindex : H.index = 2) (r x : H) (c : G) (hc : c ∉ H)
    (hcr : Commute c (r : G)) (h : IsConj (r : G) (x : G)) : IsConj r x := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  by_cases hgH : g ∈ H
  · exact isConj_iff.mpr ⟨⟨g, hgH⟩, Subtype.ext hg⟩
  · have hgc : g * c ∈ H := (H.mul_mem_iff_of_index_two hindex).mpr
      ⟨fun h => (hgH h).elim, fun h => (hc h).elim⟩
    apply isConj_iff.mpr
    refine ⟨⟨g * c, hgc⟩, Subtype.ext ?_⟩
    change (g * c) * (r : G) * (g * c)⁻¹ = (x : G)
    have he : c * (r : G) * c⁻¹ = r := by
      rw [hcr.eq, mul_assoc, mul_inv_cancel, mul_one]
    calc
      (g * c) * (r : G) * (g * c)⁻¹ = g * (c * (r : G) * c⁻¹) * g⁻¹ := by group
      _ = x := by rw [he]; exact hg

/-- Ambient conjugacy to the first marked binary root class is already
conjugacy inside the actual commutator subgroup. -/
theorem longRoot_isConj_iff (x : commutator (Model 0)) :
    IsConj (longRoot : Model 0) (x : Model 0) ↔ IsConj longRoot x := by
  refine ⟨fun h => isConj_of_index_two _ derived_index _ _ (fixedU 0)
    fixedU_zero_not_mem fixedU_zero_commutes_long h, fun h => ?_⟩
  exact (commutator (Model 0)).subtype.map_isConj h

/-- The same internal-fusion assertion for the second marked binary root. -/
theorem shortRoot_isConj_iff (x : commutator (Model 0)) :
    IsConj (shortRoot : Model 0) (x : Model 0) ↔ IsConj shortRoot x := by
  refine ⟨fun h => isConj_of_index_two _ derived_index _ _ (fixedU 2)
    fixedU_two_not_mem fixedU_two_commutes_short h, fun h => ?_⟩
  exact (commutator (Model 0)).subtype.map_isConj h
/-- The distinguished quartet generator belongs to the actual positive subgroup. -/
theorem fixedU_zero_mem_unipotent : fixedU 0 ∈ unipotent 0 := by
  change toSplitGroup 0 (fixedU 0) ∈ splitUnipotent 0
  rw [fixedU_matrix]
  change quartetElement 0 ∈ splitUnipotent 0
  rw [quartetElement_eq]
  have h (i : Fin 4) : rootGeneratorInGroup 0 (quartetRoots 0 i) 1 ∈
      splitUnipotent 0 :=
    Subgroup.subset_closure ⟨_, 1,
      ((rootBlocks .positive).roots (.inr ((0 : Fin 4), i))).property, rfl⟩
  exact (splitUnipotent 0).mul_mem ((splitUnipotent 0).mul_mem (h 0) (h 1)) (h 3)

/-- Every positive element outside the derived subgroup has one of these
2,048 literal root-matrix words. The Atlas map is the fixed marked embedding. -/
theorem outer_unipotent_normalForm (x : Model 0) (hx : x ∈ unipotent 0)
    (houter : x ∉ commutator (Model 0)) :
    ∃ n : Fin 2048, x = fixedU 0 * atlasEmbedding (atlas1600SylowTwoNormalForm n) := by
  have hq : (fixedU 0)⁻¹ ∉ commutator (Model 0) := by
    simpa only [inv_mem_iff] using fixedU_zero_not_mem
  have hyH : (fixedU 0)⁻¹ * x ∈ commutator (Model 0) :=
    ((commutator (Model 0)).mul_mem_iff_of_index_two derived_index).mpr
      ⟨fun h => (hq h).elim, fun h => (houter h).elim⟩
  have hyU : (fixedU 0)⁻¹ * x ∈ unipotent 0 :=
    (unipotent 0).mul_mem ((unipotent 0).inv_mem fixedU_zero_mem_unipotent) hx
  have hy : (fixedU 0)⁻¹ * x ∈ ExceptionalParabolics.S.map atlasEmbedding := by
    rw [atlas_sylow_map]
    exact ⟨hyU, hyH⟩
  obtain ⟨y, hy, he⟩ := hy
  obtain ⟨n, hn⟩ := atlas1600SylowTwoNormalForm_surjective hy
  refine ⟨n, ?_⟩
  rw [hn, he, mul_inv_cancel_left]

/-- The finite outer-coset square check implies the required derived membership,
including the identity. No automorphism coverage or innerness is used. -/
theorem square_one_mem_derived_of_check
    (hcheck : ∀ n : Fin 2048,
      (fixedU 0 * atlasEmbedding (atlas1600SylowTwoNormalForm n)) ^ 2 ≠ 1)
    (x : Model 0) (hx : x ∈ unipotent 0) (hsq : x ^ 2 = 1) :
    x ∈ commutator (Model 0) := by
  by_contra houter
  obtain ⟨n, rfl⟩ := outer_unipotent_normalForm x hx houter
  exact hcheck n hsq

/-- An ambient root alternative lifts to the derived group, with the same
underlying element. Normality supplies membership and the concrete outer
centralizers supply internal conjugators. -/
theorem root_lift (x : Model 0)
    (hroot : IsConj (longRoot : Model 0) x ∨ IsConj (shortRoot : Model 0) x) :
    ∃ y : commutator (Model 0), (y : Model 0) = x ∧
      (IsConj longRoot y ∨ IsConj shortRoot y) := by
  have hm (r : commutator (Model 0)) (h : IsConj (r : Model 0) x) :
      x ∈ commutator (Model 0) := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    exact (inferInstance : (commutator (Model 0)).Normal).conj_mem r r.property g
  let y : commutator (Model 0) := ⟨x, hroot.elim (hm longRoot) (hm shortRoot)⟩
  refine ⟨y, rfl, ?_⟩
  exact hroot.imp ((longRoot_isConj_iff y).mp) ((shortRoot_isConj_iff y).mp)

end Tits.InvolutionRootGeometry.BinaryDerivedFusion
