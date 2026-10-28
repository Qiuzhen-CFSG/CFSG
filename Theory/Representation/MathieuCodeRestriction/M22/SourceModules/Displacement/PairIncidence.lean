module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Coordinates
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Representatives
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.PairVectors

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage

/-!
# Pair incidence in involution displacement images

In the actual even-core/Golay cocode, the class of a pair of distinct points
belongs to an involution's displacement image exactly when the involution has
a fixed point and exchanges the pair. Specializing to the marked pair gives
the incidence test for the ten-dimensional M22 quotient.

For the positive direction, the displacement of the pair consisting of a
moved point and a fixed point is the exchanged pair. For exclusion, small
binary matrices annihilate the displacement of each native representative.
Their values on the 24 coordinate vectors distinguish every forbidden pair.
All matrix and coordinate identities are checked by the kernel, and the
proved native M24 conjugacy coverage transports the result to any involution.
No displacement rank is used.

Source: Aschbacher--Smith, H.13.1 and H.14.4(3),(4), combined manuscript
of 1 March 2004, printed pp.395--398. This supplies the pair-line incidence
calculation; the numerical quotient ranks are assembled separately.
-/

public section

open Sporadic.Mathieu MathieuCode.CocodeOctad.Involutions
namespace MathieuCode.M22PairIncidence
noncomputable section

private def bits {n : ℕ} (v : BitVec n) : Fin n → ZMod 2 :=
  fun i => if v.getLsb i then 1 else 0
private def bitColumns {m n : ℕ} (v : Fin n → BitVec m) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bits (v j) i

private def pointCoordinates : Fin 24 → BitVec 11 :=
  ![814,1705,1127,1521,191,756,1986,1307,461,855,1,1658,2,1948,4,8,16,32,64,128,256,512,1024,0]

set_option maxRecDepth 4096 in
private lemma reduce_single : ∀ i : Fin 24,
    reduce (Pi.single i 1) = bits (pointCoordinates i) := by decide +kernel

private def zMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  bitColumns ![396,664,201,325,989,461,396,325,201,989,593]

set_option maxRecDepth 4096 in
private lemma displacementMatrix_z : displacementMatrix z = zMatrix := by decide +kernel


private lemma evenPair_action (g : M24) (i j : Fin 24) :
    coreRepresentation g (m22EvenPair i j) = m22EvenPair (g • i) (g • j) := by
  apply Subtype.ext
  ext k
  change (Pi.single i 1 + Pi.single j 1 : Full) (g.val.symm k) =
    (Pi.single (g.val i) 1 + Pi.single (g.val j) 1 : Full) k
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private lemma pair_action (g : M24) (i j : Fin 24) :
    cocodeRepresentation g (codeInCore.mkQ (m22EvenPair i j)) =
      codeInCore.mkQ (m22EvenPair (g • i) (g • j)) := by
  rw [cocodeRepresentation_mk, evenPair_action]

private lemma pair_mem_of_fixed (g : M24) (i j : Fin 24)
    (hf : ∃ k : Fin 24, g • k = k) (hm : g • i = j) :
    codeInCore.mkQ (m22EvenPair i j) ∈
      LinearMap.range (cocodeRepresentation g - LinearMap.id) := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨codeInCore.mkQ (m22EvenPair i k), ?_⟩
  simp only [LinearMap.sub_apply, LinearMap.id_apply, pair_action, hm, hk]
  rw [← map_sub]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  change (Pi.single j 1 + Pi.single k 1 : Full) -
    (Pi.single i 1 + Pi.single k 1) = Pi.single i 1 + Pi.single j 1
  rw [add_sub_add_right_eq_sub]
  funext x
  exact (CharTwo.sub_eq_add ((Pi.single j 1 : Full) x)
    ((Pi.single i 1 : Full) x)).trans (add_comm _ _)

private lemma annihilator_pair {n : ℕ} (g : M24)
    (N : Matrix (Fin n) (Fin 11) (ZMod 2))
    (hN : N * displacementMatrix g = 0) (i j : Fin 24)
    (h : codeInCore.mkQ (m22EvenPair i j) ∈
      LinearMap.range (cocodeRepresentation g - LinearMap.id)) :
    N.mulVec (reduce (Pi.single i 1)) = N.mulVec (reduce (Pi.single j 1)) := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨w, rfl⟩ := sectionMap_surjective v
  have hw : (displacementMatrix g).mulVec w = reduce (m22EvenPair i j).val := by
    change (displacementMatrix g).mulVecLin w = _
    rw [displacementMatrix_eq]
    exact congrArg coordinates hv
  have hz : N.mulVec (reduce (m22EvenPair i j).val) = 0 := by
    rw [← hw, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  change N.mulVec (reduce (Pi.single i 1 + Pi.single j 1)) = 0 at hz
  rw [map_add, Matrix.mulVec_add] at hz
  ext k
  have hk := congrFun hz k
  simpa only [Pi.add_apply, Pi.zero_apply, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] using hk

private lemma mem_displacement_conj (g c : M24) (v : Cocode) :
    cocodeRepresentation c v ∈
      LinearMap.range (cocodeRepresentation (c * g * c⁻¹) - LinearMap.id) ↔
    v ∈ LinearMap.range (cocodeRepresentation g - LinearMap.id) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨cocodeRepresentation c⁻¹ w, ?_⟩
    have he := congrArg (cocodeRepresentation c⁻¹) hw
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      map_mul, Module.End.mul_apply, Representation.inv_self_apply] using he
  · rintro ⟨w, hw⟩
    refine ⟨cocodeRepresentation c w, ?_⟩
    have he := congrArg (cocodeRepresentation c) hw
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      map_mul, Module.End.mul_apply, Representation.inv_self_apply] using he

private lemma pair_mem_conj (g c : M24) (i j : Fin 24) :
    codeInCore.mkQ (m22EvenPair i j) ∈
      LinearMap.range (cocodeRepresentation (c * g * c⁻¹) - LinearMap.id) ↔
    codeInCore.mkQ (m22EvenPair (c⁻¹ • i) (c⁻¹ • j)) ∈
      LinearMap.range (cocodeRepresentation g - LinearMap.id) := by
  simpa only [pair_action, smul_inv_smul] using
    mem_displacement_conj g c (codeInCore.mkQ (m22EvenPair (c⁻¹ • i) (c⁻¹ • j)))

private def tMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  bitColumns ![1153,1538,1044,1477,1044,465,570,1153,1582,1538,0]

set_option maxRecDepth 4096 in
private lemma displacementMatrix_t : displacementMatrix t = tMatrix := by decide +kernel

private def zAnnihilator : Matrix (Fin 7) (Fin 11) (ZMod 2) :=
  bitColumns ![4,1,16,8,32,2,4,8,16,32,64]
private def tAnnihilator : Matrix (Fin 6) (Fin 11) (ZMod 2) :=
  bitColumns ![36,48,10,11,42,1,2,4,8,16,32]

set_option maxRecDepth 4096 in
private lemma z_annihilates : zAnnihilator * zMatrix = 0 := by decide +kernel
set_option maxRecDepth 4096 in
private lemma t_annihilates : tAnnihilator * tMatrix = 0 := by decide +kernel

private def zLabels : Fin 24 → BitVec 7 :=
  ![43,102,83,122,55,30,125,125,0,1,4,79,1,64,16,8,32,2,4,8,16,32,64,0]
private def tLabels : Fin 24 → BitVec 6 :=
  ![40,26,61,33,58,55,14,29,43,46,36,34,48,23,10,11,42,1,2,4,8,16,32,0]

set_option maxRecDepth 4096 in
private lemma z_labels : ∀ i : Fin 24,
    zAnnihilator.mulVec (bits (pointCoordinates i)) = bits (zLabels i) := by decide +kernel
set_option maxRecDepth 4096 in
private lemma t_labels : ∀ i : Fin 24,
    tAnnihilator.mulVec (bits (pointCoordinates i)) = bits (tLabels i) := by decide +kernel

set_option maxRecDepth 4096 in
private lemma z_labels_separate : ∀ i j : Fin 24,
    bits (zLabels i) = bits (zLabels j) → i = j ∨ z • i = j := by decide +kernel
set_option maxRecDepth 4096 in
private lemma t_labels_separate : ∀ i j : Fin 24,
    bits (tLabels i) = bits (tLabels j) → i = j := by decide +kernel

private lemma z_pair_mem_iff (i j : Fin 24) (hij : i ≠ j) :
    codeInCore.mkQ (m22EvenPair i j) ∈
      LinearMap.range (cocodeRepresentation z - LinearMap.id) ↔ z • i = j := by
  constructor
  · intro h
    have he := annihilator_pair z zAnnihilator
      (by rw [displacementMatrix_z]; exact z_annihilates) i j h
    rw [reduce_single, reduce_single, z_labels, z_labels] at he
    exact (z_labels_separate i j he).resolve_left hij
  · exact pair_mem_of_fixed z i j ⟨0, by decide +kernel⟩

private lemma t_pair_not_mem (i j : Fin 24) (hij : i ≠ j) :
    codeInCore.mkQ (m22EvenPair i j) ∉
      LinearMap.range (cocodeRepresentation t - LinearMap.id) := by
  intro h
  have he := annihilator_pair t tAnnihilator
    (by rw [displacementMatrix_t]; exact t_annihilates) i j h
  rw [reduce_single, reduce_single, t_labels, t_labels] at he
  exact hij (t_labels_separate i j he)

/-- For a native involution, a nonzero pair class lies in the displacement
image exactly when the involution has a fixed point and exchanges that pair. -/
theorem evenPair_mem_displacement_iff (g : M24) (hg : orderOf g = 2)
    (i j : Fin 24) (hij : i ≠ j) :
    codeInCore.mkQ (m22EvenPair i j) ∈
      LinearMap.range (cocodeRepresentation g - LinearMap.id) ↔
    (∃ k : Fin 24, g • k = k) ∧ g • i = j := by
  constructor
  · intro h
    rcases M24InvolutionCentralizers.involution_classes g hg with hz | ht
    · obtain ⟨c, hc⟩ := isConj_iff.mp hz
      change c * z * c⁻¹ = g at hc
      rw [← hc] at h ⊢
      have hne : c⁻¹ • i ≠ c⁻¹ • j := by
        intro he
        apply hij
        simpa only [smul_inv_smul] using congrArg (fun k : Fin 24 => c • k) he
      have hm := (z_pair_mem_iff _ _ hne).mp ((pair_mem_conj z c i j).mp h)
      have h0 : z • (0 : Fin 24) = 0 := by decide +kernel
      refine ⟨⟨c • 0, ?_⟩, ?_⟩
      · simp only [mul_smul, inv_smul_smul, h0]
      · simpa only [mul_smul, smul_inv_smul] using congrArg (fun k : Fin 24 => c • k) hm
    · obtain ⟨c, hc⟩ := isConj_iff.mp ht
      change c * t * c⁻¹ = g at hc
      rw [← hc] at h
      have hne : c⁻¹ • i ≠ c⁻¹ • j := by
        intro he
        apply hij
        simpa only [smul_inv_smul] using congrArg (fun k : Fin 24 => c • k) he
      exact (t_pair_not_mem _ _ hne ((pair_mem_conj t c i j).mp h)).elim
  · rintro ⟨hf, hm⟩
    exact pair_mem_of_fixed g i j hf hm

end
end MathieuCode.M22PairIncidence

namespace MathieuCode
/-- The marked-pair incidence test required when passing from the
 eleven-dimensional cocode to the literal ten-dimensional M22 quotient. -/
theorem m22PairClass_mem_displacement_iff (g : m22PairStabilizer) (hg : orderOf g = 2) :
    m22PairClass ∈ LinearMap.range (cocodeRepresentation g.val - LinearMap.id) ↔
    (∃ i : Fin 24, g.val • i = i) ∧ g.val • (0 : Fin 24) = 9 := by
  exact M22PairIncidence.evenPair_mem_displacement_iff g.val
    ((orderOf_injective m22PairStabilizer.subtype Subtype.val_injective g).trans hg)
    0 9 (by decide)
end MathieuCode
