module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FixedGeometryTransport

/-!
# Returning conjugates of the central Ree root marker

The central curves y₁(a) and y₇(b), in GLS numbering, lie in the actual
positive fixed subgroup. Four split F₄ exchanges give a correction with
fourth paired coordinate ab. Unique positive coordinates therefore prove
noncommutation when a and b are nonzero. Two fixed relative Weyl words
carry y₁(t) to y₅(t) and y₇(t), preserving the parameter.

The only retained input identifies a central involution of the standard
unipotent Sylow as a nonzero y₅(t). This input is reserved for the independent
UnipotentCenter development. Sylow conjugacy then returns the pair to the original
Sylow of the original marker. The source consumer restricts to m ≥ 1;
the derived binary Ree group is treated separately by the Tits module.

Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex;
Aschbacher--Smith 1.1.5(3)(a) and Proposition 2.2.2, pp.501--503,519--520.
-/

public section
noncomputable section
open Subgroup Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.MarkedStrongClosure
open LargeLocalSeeds
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent
open Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairRigidity.FixedCollection

/-- The exact input reserved for the standard-unipotent center producer.
It makes no assertion about arbitrary involutions or automorphisms. -/
@[expose] def StandardCentralInvolutions (m : ℕ) : Prop :=
  ∀ x : Model m, x ∈ unipotent m → orderOf x = 2 →
    (∀ u ∈ unipotent m, Commute x u) →
    ∃ t : CoefficientField m, t ≠ 0 ∧ x = EvenInvolutionGeometry.longRootElement m t

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (longRoot_isLong i), halfFrobenius]

private theorem main_three (m : ℕ) (t : CoefficientField m) :
    rootWord m 3 t = X m 10 t * X m 11 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change X m 10 t * X m 11 (halfFrobenius m t) * 1 = _
  exact mul_one _
private theorem central_zero_word (m : ℕ) (t : CoefficientField m) :
    centralWord m 0 t = X m 3 t * X m 2 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]; rfl
private theorem central_two (m : ℕ) (t : CoefficientField m) :
    centralWord m 2 t = X m 9 t * X m 8 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]; rfl
private theorem central_four (m : ℕ) (t : CoefficientField m) :
    centralWord m 4 t = X m 15 t * X m 14 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]; rfl
private theorem central_six (m : ℕ) (t : CoefficientField m) :
    centralWord m 6 t = X m 21 t * X m 20 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]; rfl

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)
private theorem main_zero (m : ℕ) (i : Fin 8) : rootWord m i 0 = 1 := by
  simp [rootWord, root_zero]
private theorem central_zero (m : ℕ) (i : Fin 8) : centralWord m i 0 = 1 := by
  simp [centralWord, root_zero]

local macro "geom" : tactic => `(tactic|
  norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three])

private theorem swap_suffix {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) (d : G) : a * (b * d) = b * (a * (c * d)) := by
  simpa only [mul_assoc] using congrArg (fun z => z * d) h
private theorem swap_two_suffix {G : Type*} [Group G] {a b c d : G}
    (h : a * b = b * a * c * d) (e : G) :
    a * (b * e) = b * (a * (c * (d * e))) := by
  simpa only [mul_assoc] using congrArg (fun z => z * e) h

private theorem reverse_b2 (m : ℕ) (a t : CoefficientField m) :
    X m 3 a * X m 20 t =
      X m 20 t * X m 3 a * X m 8 (a * t) * X m 15 (a * t ^ 2) := by
  have h := xb m 3 20 8 15 (by geom) (by geom) (by geom)
    (by ext z; fin_cases z <;> norm_num [V])
    (by ext z; fin_cases z <;> norm_num [V]) a t
  calc
    _ = (X m 20 t * X m 3 a) *
        (X m 8 (a * t) * X m 15 (a * t ^ 2))⁻¹ := by rw [h]; group
    _ = _ := by
      rw [mul_inv_rev, xi, xi, (xc m 15 8 (by geom) _ _).eq]
      simp only [mul_assoc]

-- The four exchanges are (3,21), (2,20), (21,2), and (3,20).
-- Every subsequent swap has nonnegative root inner product.
private theorem collect_zero_six (m : ℕ) (a s b t : CoefficientField m) :
    X m 3 a * X m 2 s * X m 21 b * X m 20 t =
      X m 21 b * X m 20 t * X m 3 a * X m 2 s *
        X m 10 (a * b) * X m 11 (s * t) *
        X m 15 (a * t ^ 2) * X m 14 (b * s) *
        X m 9 (b * s ^ 2) * X m 8 (a * t) := by
  simp only [mul_assoc]
  rw [swap_two_suffix (xb m 21 2 14 9 (by geom) (by geom) (by geom)
    (by ext z; fin_cases z <;> norm_num [V])
    (by ext z; fin_cases z <;> norm_num [V]) b s)]
  rw [swap_suffix (xs m 3 21 10 (by geom) (by geom)
    (by ext z; fin_cases z <;> norm_num [V]) a b)]
  rw [(xc m 10 2 (by geom) (a * b) s).left_comm]
  rw [(xc m 9 20 (by geom) (b * s ^ 2) t).eq]
  rw [(xc m 14 20 (by geom) (b * s) t).left_comm]
  rw [(xc m 10 20 (by geom) (a * b) t).left_comm]
  rw [swap_suffix (xs m 2 20 11 (by geom) (by geom)
    (by ext z; fin_cases z <;> norm_num [V]) s t)]
  rw [swap_two_suffix (reverse_b2 m a t)]
  rw [(xc m 15 2 (by geom) (a * t ^ 2) s).left_comm]
  rw [(xc m 8 2 (by geom) (a * t) s).left_comm]
  rw [(xc m 11 10 (by geom) (s * t) (a * b)).left_comm]
  rw [(xc m 15 10 (by geom) (a * t ^ 2) (a * b)).left_comm]
  rw [(xc m 8 10 (by geom) (a * t) (a * b)).left_comm]
  rw [(xc m 15 11 (by geom) (a * t ^ 2) (s * t)).left_comm]
  rw [(xc m 8 11 (by geom) (a * t) (s * t)).left_comm]
  rw [(xc m 8 15 (by geom) (a * t) (a * t ^ 2)).left_comm]
  rw [(xc m 8 14 (by geom) (a * t) (b * s)).left_comm]
  rw [(xc m 8 9 (by geom) (a * t) (b * s ^ 2)).eq]

private theorem half_mixed (m : ℕ) (a b : CoefficientField m) :
    halfFrobenius m (a * halfFrobenius m b ^ 2) = b * halfFrobenius m a := by
  rw [map_mul, halfFrobenius_sq, halfFrobenius_titsEnd, mul_comm]

private theorem zero_six_exchange (m : ℕ) (a b : CoefficientField m) :
    centralWord m 0 a * centralWord m 6 b =
      centralWord m 6 b * centralWord m 0 a *
        (rootWord m 3 (a * b) *
          centralWord m 4 (a * halfFrobenius m b ^ 2) *
          centralWord m 2 (b * halfFrobenius m a ^ 2)) := by
  rw [central_zero_word, central_six, main_three, central_four, central_two,
    half_mixed, half_mixed, map_mul]
  simpa only [mul_assoc] using
    collect_zero_six m a (halfFrobenius m a) b (halfFrobenius m b)

private def detectionParameters (m : ℕ) (a b c : CoefficientField m) :
    PositiveParameters m := ⟨![0, 0, 0, a], 0, ![0, b, 0, c]⟩
private theorem detection_word (m : ℕ) (a b c : CoefficientField m) :
    positiveWord m (detectionParameters m a b c) =
      rootWord m 3 a * centralWord m 4 b * centralWord m 2 c := by
  simp [positiveWord, detectionParameters, positive_pair_indices, positive_quartet_indices,
    pairCount, quartetCount,
    List.ofFn_succ, main_zero, central_zero, mul_assoc]

private theorem zero_six_not_commute (m : ℕ) (a b : CoefficientField m)
    (ha : a ≠ 0) (hb : b ≠ 0) : ¬Commute (centralWord m 0 a) (centralWord m 6 b) := by
  intro hc
  have he := zero_six_exchange m a b
  rw [hc.eq] at he
  have hz : rootWord m 3 (a * b) *
      centralWord m 4 (a * halfFrobenius m b ^ 2) *
      centralWord m 2 (b * halfFrobenius m a ^ 2) = 1 :=
    (mul_left_cancel ((mul_one (centralWord m 6 b * centralWord m 0 a)).trans he)).symm
  have hp : positiveWord m (detectionParameters m (a * b)
      (a * halfFrobenius m b ^ 2) (b * halfFrobenius m a ^ 2)) =
      positiveWord m (detectionParameters m 0 0 0) := by
    simpa only [detection_word, main_zero, central_zero, one_mul] using hz
  exact mul_ne_zero ha hb
    (congrArg (fun p : PositiveParameters m => p.pair 3) (positiveWord_injective m hp))

private def centralElement (m : ℕ) (i : Fin 8) (t : CoefficientField m) : Model m :=
  ⟨centralWord m i t, by
    simpa only [mem_fixedSubgroup, reeAutomorphism_apply]
      using (positive_words_fixed_mem m i t).2.1⟩
private theorem centralElement_coe (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    toSplitGroup m (centralElement m i t) = centralWord m i t := toSplitGroup_apply m _
private theorem centralElement_mem (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    centralElement m i t ∈ unipotent m := by
  change toSplitGroup m (centralElement m i t) ∈ splitUnipotent m
  rw [centralElement_coe]
  exact (positive_words_fixed_mem m i t).2.2
private theorem centralElement_four (m : ℕ) (t : CoefficientField m) :
    centralElement m 4 t = EvenInvolutionGeometry.longRootElement m t := by
  apply Subtype.ext
  rfl

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]
private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

-- Only three even blocks are needed; no global root-orbit calculation.
private def usedIndex : Fin 3 → Fin 8
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨4, by decide⟩
  | _ => ⟨6, by decide⟩
private def usedLong : Fin 3 → Vec 4 := ![V 0, V 12, V 18]
private def usedShort : Fin 3 → Vec 4 := ![V 1, V 13, V 19]
private theorem used_long_val (i : Fin 3) :
    (longRoot (usedIndex i)).val = usedLong i := by
  rw [longRoot_eq_sum]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [usedIndex, usedLong, V, longRootCoefficients, typeF4SimpleRoot,
      Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk,
      Matrix.cons_val_two, Matrix.cons_val_three]
private theorem used_short_val (i : Fin 3) :
    (shortRoot (usedIndex i)).val = usedShort i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [usedIndex, usedShort, V, shortRoot, longRoot, relativeRotation,
      middleReflection, endReflection, Equiv.Perm.mul_apply, pow_succ,
      WordRelations.exceptionalRootPermutation_simple_reflection,
      exceptionalRootPermutation_simple, Fin.revPerm, Fin.rev,
      reflection_val, reflectedVector, typeF4SimpleRoot,
      Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem used_high_val (i : Fin 3) :
    (highRoot (usedIndex i)).val = (![V 3, V 15, V 21] : Fin 3 → Vec 4) i := by
  rw [highRoot_eq_add_two _ (by fin_cases i <;> decide), used_long_val, used_short_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [usedLong, usedShort, V, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem used_mixed_val (i : Fin 3) :
    (mixedRoot (usedIndex i)).val = (![V 2, V 14, V 20] : Fin 3 → Vec 4) i := by
  rw [mixedRoot_eq_add _ (by fin_cases i <;> decide), used_long_val, used_short_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [usedLong, usedShort, V, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem zero_four_roots :
    wordAction [0, 3, 1, 2, 1, 2, 0, 3] (highRoot 0) = highRoot 4 ∧
    wordAction [0, 3, 1, 2, 1, 2, 0, 3] (mixedRoot 0) = mixedRoot 4 := by
  have h0 : (highRoot 0).val = V 3 := used_high_val 0
  have h4 : (highRoot 4).val = V 15 := used_high_val 1
  have l0 : (mixedRoot 0).val = V 2 := used_mixed_val 0
  have l4 : (mixedRoot 4).val = V 14 := used_mixed_val 1
  constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
    norm_num [wordAction, Equiv.Perm.mul_apply, reflection_val, reflectedVector,
      h0, h4, l0, l4, V, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem zero_six_roots :
    wordAction [0, 3] (highRoot 0) = highRoot 6 ∧
    wordAction [0, 3] (mixedRoot 0) = mixedRoot 6 := by
  have h0 : (highRoot 0).val = V 3 := used_high_val 0
  have h6 : (highRoot 6).val = V 21 := used_high_val 2
  have l0 : (mixedRoot 0).val = V 2 := used_mixed_val 0
  have l6 : (mixedRoot 6).val = V 20 := used_mixed_val 2
  constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
    norm_num [wordAction, Equiv.Perm.mul_apply, reflection_val, reflectedVector,
      h0, h6, l0, l6, V, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem weyl_conjugate_central (m : ℕ) (n : Model m) (w : List (Fin 4))
    (hn : toSplitGroup m n = simpleWord m w) (i j : Fin 8)
    (hh : wordAction w (highRoot i) = highRoot j)
    (hl : wordAction w (mixedRoot i) = mixedRoot j) (t : CoefficientField m) :
    n * centralElement m i t * n⁻¹ = centralElement m j t := by
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, centralElement_coe, hn]
  simp only [centralWord, fieldEnd_half]
  calc
    _ = (simpleWord m w * rootGeneratorInGroup m (highRoot i) t *
          (simpleWord m w)⁻¹) *
        (simpleWord m w * rootGeneratorInGroup m (mixedRoot i) (halfFrobenius m t) *
          (simpleWord m w)⁻¹) := by group
    _ = _ := by rw [simpleWord_conj_root, simpleWord_conj_root, hh, hl]

private theorem marked_pair (m : ℕ) (t : CoefficientField m) (ht : t ≠ 0) :
    ∃ a b : Model m, a ∈ unipotent m ∧ b ∈ unipotent m ∧
      IsConj (EvenInvolutionGeometry.longRootElement m t) a ∧
      IsConj (EvenInvolutionGeometry.longRootElement m t) b ∧ ¬Commute a b := by
  let n : Model m := weylLift m .linear * weylLift m .suzuki * weylLift m .linear
  have hn : toSplitGroup m n = simpleWord m [0, 3, 1, 2, 1, 2, 0, 3] := by
    simp only [n, map_mul, toSplitGroup_weylLift]
    simp [simpleWord, sideWord, mul_assoc]
  have h4 : IsConj (centralElement m 0 t) (centralElement m 4 t) :=
    isConj_iff.mpr ⟨n, weyl_conjugate_central m n _ hn 0 4
      zero_four_roots.1 zero_four_roots.2 t⟩
  have h6 : IsConj (centralElement m 0 t) (centralElement m 6 t) :=
    isConj_iff.mpr ⟨weylLift m .linear,
      weyl_conjugate_central m (weylLift m .linear) _
        (toSplitGroup_weylLift m .linear) 0 6 zero_six_roots.1 zero_six_roots.2 t⟩
  refine ⟨centralElement m 0 t, centralElement m 6 t,
    centralElement_mem m 0 t, centralElement_mem m 6 t, ?_, ?_, ?_⟩
  · simpa only [centralElement_four] using h4.symm
  · simpa only [centralElement_four] using h4.symm.trans h6
  · intro hc
    apply zero_six_not_commute m t t ht ht
    simpa only [centralElement_coe] using hc.map (toSplitGroup m)

/-- The actual marked class has noncommuting returning conjugates. The sole
retained premise is the independent standard-unipotent center identification. -/
theorem sylow_noncommuting_conjugates_of_central_involutions (m : ℕ)
    (hcenter : StandardCentralInvolutions m)
    (R : Sylow 2 (Model m)) (v : Model m)
    (hvR : v ∈ R) (hv : orderOf v = 2) (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : Model m) ∧ IsConj v (b : Model m) ∧ ¬Commute a b := by
  have hindex : Odd (unipotent m).index :=
    Parabolics.OuterLocal.LargeAutomorphisms.unipotent_index_odd_of_standard
      (canonicalLocalBlockInput m)
      (LargeLocalSeeds.FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model m) R (sylowOfOddIndex m hindex)
  let f := MulAut.conj g
  have hm : (R : Subgroup (Model m)).map f.toMonoidHom = unipotent m := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, sylowOfOddIndex_coe] at hh
    exact hh
  have hfv : f v ∈ unipotent m := hm ▸ mem_map_of_mem f.toMonoidHom hvR
  have hfc : ∀ x ∈ unipotent m, Commute (f v) x := by
    intro x hx
    rw [← hm] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (hc y hy).map f.toMonoidHom
  obtain ⟨t, ht, he⟩ := hcenter (f v) hfv (by simpa only [MulEquiv.orderOf_eq] using hv) hfc
  obtain ⟨a0, b0, ha0, hb0, hac, hbc, hab⟩ := marked_pair m t ht
  rw [← he] at hac hbc
  have hback : ∀ x ∈ unipotent m, f.symm x ∈ R := by
    intro x hx
    rw [← hm] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change f.symm (f y) ∈ (R : Subgroup (Model m))
    rw [f.symm_apply_apply]
    exact hy
  let a : R := ⟨f.symm a0, hback a0 ha0⟩
  let b : R := ⟨f.symm b0, hback b0 hb0⟩
  refine ⟨a, b, ?_, ?_, ?_⟩
  · simpa only [a, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      f.symm.toMonoidHom.map_isConj hac
  · simpa only [b, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      f.symm.toMonoidHom.map_isConj hbc
  · intro hh
    apply hab
    change a0 * b0 = b0 * a0
    have hh' : (a : Model m) * (b : Model m) = (b : Model m) * (a : Model m) :=
      congrArg Subtype.val hh.eq
    have hf := congrArg f hh'
    change f (f.symm a0 * f.symm b0) = f (f.symm b0 * f.symm a0) at hf
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hf

end ReeF4.MarkedStrongClosure
