module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates

/-!
# Detecting the full fixed Ree torus on the linear radical

A fixed root product has parameter one on both leading roots of every B₂
quartet in the linear radical. Its fixedness follows from the actual collected
Ree twist, and every factor belongs to the specified radical root support.
If a full fixed-torus element centralizes this product, diagonal conjugation
and uniqueness of split root coordinates make those root characters trivial.

The quartet roots 0100 and 0010 are the two middle simple roots; 1100 and
0011 add the respective end simple roots. Multiplicativity of characters
under root addition therefore detects all four simple roots. Root addition
and negation extend triviality to every root, which makes the actual diagonal
matrix the identity. The full torus is used via `splitTorus_eq_diagonalTorus`.

Source: the torus part of GLS3, Theorem 2.6.5(e),
`refs/KGroup/GLS3/chapter2.tex`, using the concrete F₄ root partition and
Chevalley torus action. This argument also holds at the binary endpoint.
-/

noncomputable section
namespace ReeF4.SectionGeometry.LinearRadical
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open LargeLocalSeeds Parabolics Subgroup
open RadicalCoordinates FixedCoordinates

private abbrev B := rootBlocks (.radical .linear)
private def testBlocks (m : ℕ) : BlockParameters m (.radical .linear) :=
  (fun _ => pairSolution m 1, fun _ => quartetSolution m 1 0)
private def testParameters (m : ℕ) : Parameters m (.radical .linear) :=
  (B.repack m).symm (testBlocks m)

private theorem test_fixed (m : ℕ) :
    reeTwist m (word m B.order (testParameters m)) = word m B.order (testParameters m) := by
  rw [B.word_eq_blockWord, testParameters, Equiv.apply_symm_apply,
    B.twist_blockWord m (mixedRootCommutation m) (b2RootSwap m)]
  congr 1
  apply Prod.ext
  · funext i
    exact pairSolution_fixed m 1
  · funext i
    exact quartetSolution_fixed m 1 0

private theorem test_at_quartet (m : ℕ) (i : Fin 4) (j : Fin 4) (hj : j = 0 ∨ j = 1) :
    testParameters m (B.roots (.inr (i, j))) = 1 := by
  rcases hj with rfl | rfl <;>
    simp [testParameters, RootBlocks.repack, testBlocks, quartetSolution]

private theorem conjugation_word (m : ℕ) (z : SplitGroup m) (u : TorusParameter m)
    (hu : diagonalTorusHom m u = z.val)
    {k : Support} (e : RootOrder k) (a : Parameters m k) :
    (MulAut.conj z) (word m e a) =
      word m e (fun r => (integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹ r.val :
        CoefficientField m) * a r) := by
  have hr (r : F4Chevalley.Root) (v : CoefficientField m) :
      (MulAut.conj z) (rootGeneratorInGroup m r v) =
        rootGeneratorInGroup m r
          ((integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹ r : CoefficientField m) * v) := by
    apply Subtype.ext
    change z.val * F4Chevalley.rootCurve r v * z.val⁻¹ = _
    rw [← hu]
    simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe]
      using F4Chevalley.rootCurve_torus_conjugation u⁻¹ r v
  simp only [word, map_list_prod, List.map_ofFn, Function.comp_def, hr]

private theorem word_injective (m : ℕ) {k : Support} (e : RootOrder k) :
    Function.Injective (word m e) := by
  intro x y h
  exact (wordInSubgroup_bijective m e).1 (Subtype.ext h)

private theorem quartet_characters (m : ℕ) (t : Model m) (ht : t ∈ fixedTorus m)
    (hc : ∀ q ∈ radical m .linear, t * q * t⁻¹ = q) :
    ∃ u : TorusParameter m, diagonalTorusHom m u = (toSplitGroup m t).val ∧
      ∀ (i : Fin 4) (j : Fin 4), j = 0 ∨ j = 1 →
        integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹
          (B.roots (.inr (i, j))).val = 1 := by
  have hz : toSplitGroup m t ∈ diagonalTorus m := by
    rw [← splitTorus_eq_diagonalTorus]
    exact ht
  obtain ⟨u, hu⟩ := hz
  refine ⟨u, hu, ?_⟩
  let q : Model m := ⟨word m B.order (testParameters m),
    (ReeF4.mem_fixedSubgroup m _).mpr (test_fixed m)⟩
  have hqcoe : toSplitGroup m q = word m B.order (testParameters m) := by
    rw [toSplitGroup_apply]
  have hq : q ∈ radical m .linear := by
    change toSplitGroup m q ∈ splitRadical m .linear
    rw [hqcoe]
    exact word_mem m B.order (testParameters m)
  have he : (MulAut.conj (toSplitGroup m t)) (word m B.order (testParameters m)) =
      word m B.order (testParameters m) := by
    have hh := congrArg (toSplitGroup m) (hc q hq)
    simpa only [map_mul, map_inv, hqcoe, MulAut.conj_apply] using hh
  rw [conjugation_word m _ u hu] at he
  have hp := word_injective m B.order he
  intro i j hj
  have hh := congrFun hp (B.roots (.inr (i, j)))
  rw [test_at_quartet m i j hj, mul_one] at hh
  exact Units.ext hh

private theorem scale_add (m : ℕ) (u : TorusParameter m) (r s v : F4Chevalley.Root)
    (hv : v.val = r.val + s.val) :
    integralChevalleyRootScale (P := typeF4RootPairing) u v =
      integralChevalleyRootScale (P := typeF4RootPairing) u r *
        integralChevalleyRootScale (P := typeF4RootPairing) u s := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ v q =
      typeF4RootPairing.pairingIn ℤ r q + typeF4RootPairing.pairingIn ℤ s q :=
    typeF4RootPairing.pairingIn_eq_add_of_root_eq_add hv
  simp only [integralChevalleyRootScale, hp, zpow_add, Finset.prod_mul_distrib]

private theorem quartet_zero_simple :
    (B.roots (.inr ((0 : Fin 4), 0))).val = typeF4SimpleRootIndex 1 ∧
    (B.roots (.inr ((0 : Fin 4), 1))).val = typeF4SimpleRootIndex 2 := by
  constructor <;> apply Subtype.ext <;> rw [rootBlocks_roots_val]
  all_goals
    ext i
    fin_cases i <;>
      norm_num [RootPartition.index, RootPartition.quartetRow, RootPartition.table,
        typeF4SimpleRootIndex_val, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem quartet_two_sums :
    (B.roots (.inr ((2 : Fin 4), 0))).val.val =
      (typeF4SimpleRootIndex 0).val + (typeF4SimpleRootIndex 1).val ∧
    (B.roots (.inr ((2 : Fin 4), 1))).val.val =
      (typeF4SimpleRootIndex 2).val + (typeF4SimpleRootIndex 3).val := by
  constructor <;> rw [rootBlocks_roots_val]
  all_goals
    ext i
    fin_cases i <;>
      norm_num [RootPartition.index, RootPartition.quartetRow, RootPartition.table,
        typeF4SimpleRootIndex_val, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem diagonal_eq_one_of_quartet_characters (m : ℕ) (u : TorusParameter m)
    (hu : ∀ (i : Fin 4) (j : Fin 4), j = 0 ∨ j = 1 →
      integralChevalleyRootScale (P := typeF4RootPairing) u
        (B.roots (.inr (i, j))).val = 1) : diagonalTorusHom m u = 1 := by
  have h1 : integralChevalleyRootScale (P := typeF4RootPairing) u
      (typeF4SimpleRootIndex 1) = 1 := by
    rw [← quartet_zero_simple.1]
    exact hu 0 0 (Or.inl rfl)
  have h2 : integralChevalleyRootScale (P := typeF4RootPairing) u
      (typeF4SimpleRootIndex 2) = 1 := by
    rw [← quartet_zero_simple.2]
    exact hu 0 1 (Or.inr rfl)
  have h0 : integralChevalleyRootScale (P := typeF4RootPairing) u
      (typeF4SimpleRootIndex 0) = 1 := by
    have hh := hu 2 0 (Or.inl rfl)
    rwa [scale_add m u _ _ _ quartet_two_sums.1, h1, mul_one] at hh
  have h3 : integralChevalleyRootScale (P := typeF4RootPairing) u
      (typeF4SimpleRootIndex 3) = 1 := by
    have hh := hu 2 1 (Or.inr rfl)
    rwa [scale_add m u _ _ _ quartet_two_sums.2, h2, one_mul] at hh
  have hs (r : F4Chevalley.Root) (hr : r ∈ typeF4RootPairing_base.support) :
      integralChevalleyRootScale (P := typeF4RootPairing) u r = 1 := by
    obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective ⟨r, hr⟩
    have he : typeF4SimpleRootIndex i = r := congrArg Subtype.val hi
    rw [← he]
    fin_cases i <;> assumption
  apply F4Chevalley.torusConjugation.kernel_compatibility u |>.mpr
  intro r
  apply typeF4RootPairing_base.induction_add r
  · intro v hv
    simp only [integralChevalleyRootScale,
      RootPairing.pairingIn_reflectionPerm_self_left, zpow_neg, Finset.prod_inv_distrib]
    change (integralChevalleyRootScale (P := typeF4RootPairing) u v)⁻¹ = 1
    rw [hv, inv_one]
  · exact hs
  · intro v w x hx hv hw
    rw [scale_add m u v w x hx, hv, hs w hw, one_mul]

/-- A full fixed-torus element centralizing the specified linear radical is
identity, as detected on an actual fixed product of radical root factors. -/
public theorem fixedTorus_eq_one_of_centralizes_radical (m : ℕ) (t : Model m) (ht : t ∈ fixedTorus m)
    (hc : ∀ q ∈ radical m .linear, t * q * t⁻¹ = q) : t = 1 := by
  obtain ⟨u, hu, hs⟩ := quartet_characters m t ht hc
  have he := diagonal_eq_one_of_quartet_characters m u⁻¹ hs
  rw [map_inv, inv_eq_one] at he
  apply toSplitGroup_injective m
  rw [map_one]
  apply Subtype.ext
  exact hu.symm.trans he

end ReeF4.SectionGeometry.LinearRadical
