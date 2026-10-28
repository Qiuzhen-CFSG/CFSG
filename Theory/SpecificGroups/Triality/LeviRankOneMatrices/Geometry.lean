module
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Coordinates
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup
/-!
# D4 root strings in explicit integral coordinates

The ordered roots consist of ±α, eight strings of length two, and six fixed
roots. Direct integral coordinate equalities identify every raising/lowering
edge, show that only −α can be raised twice, and exclude raising three times.
These facts determine the genuine Geck divided-power coefficients.

Source: the common-lattice subsystem construction in GLS3 §2.6,
Proposition 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.Parabolics.RankOneMatrices
noncomputable section

def rootCoords : Fin 24 → Fin 4 → ℤ :=
  ![![1,1,0,0], ![1,-1,0,0], ![-1,1,0,0], ![-1,-1,0,0],
    ![1,0,1,0], ![1,0,-1,0], ![-1,0,1,0], ![-1,0,-1,0],
    ![1,0,0,1], ![1,0,0,-1], ![-1,0,0,1], ![-1,0,0,-1],
    ![0,1,1,0], ![0,1,-1,0], ![0,-1,1,0], ![0,-1,-1,0],
    ![0,1,0,1], ![0,1,0,-1], ![0,-1,0,1], ![0,-1,0,-1],
    ![0,0,1,1], ![0,0,1,-1], ![0,0,-1,1], ![0,0,-1,-1]]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma rootCoords_spec (r : Fin 24) (j : Fin 4) :
    ((typeDRootPairing 2).root (rootEnumeration r) : Vec 4) j = (rootCoords r j : ℝ) := by
  fin_cases r <;> fin_cases j <;>
    norm_num [rootCoords, rootEnumeration, pairEquiv, pairTable, signEquiv,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector, basisVector,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Pi.single_apply] <;>
    norm_num [Fin.ext_iff]

def orderedRoot (i : Fin 4) (r : Fin 24) : TypeDRootIndex 4 :=
  rootEnumeration (rootOrder i r)
def orderedCoords (i : Fin 4) (r : Fin 24) : Fin 4 → ℤ :=
  rootCoords (rootOrderTable i r)

lemma orderedCoords_spec (i : Fin 4) (r : Fin 24) (j : Fin 4) :
    ((typeDRootPairing 2).root (orderedRoot i r) : Vec 4) j =
      (orderedCoords i r j : ℝ) := rootCoords_spec _ _

lemma orderedRoot_zero (i : Fin 4) : orderedRoot i 0 = typeDSimpleRootIndex 2 i := by
  fin_cases i <;> rfl

lemma root_add_iff (i : Fin 4) (r s t : Fin 24) :
    (typeDRootPairing 2).root (orderedRoot i r) =
      (typeDRootPairing 2).root (orderedRoot i s) +
      (typeDRootPairing 2).root (orderedRoot i t) ↔
    orderedCoords i r = orderedCoords i s + orderedCoords i t := by
  rw [Subtype.ext_iff, funext_iff, funext_iff]
  simp only [Submodule.coe_add, Pi.add_apply, orderedCoords_spec, ← Int.cast_add,
    Int.cast_inj]

def raisingEdge (r s : Fin 24) : Prop :=
  2 ≤ s.val ∧ s.val < 18 ∧ s.val % 2 = 1 ∧ r.val + 1 = s.val
instance (r s : Fin 24) : Decidable (raisingEdge r s) := inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma ordered_add (i : Fin 4) (r s : Fin 24) :
    orderedCoords i r = orderedCoords i 0 + orderedCoords i s ↔ raisingEdge r s := by
  revert i r s
  decide +kernel

lemma orderedRoot_injective (i : Fin 4) : Function.Injective (orderedRoot i) :=
  (rootEnumeration.injective).comp (rootOrder i).injective
lemma orderedRoot_surjective (i : Fin 4) : Function.Surjective (orderedRoot i) :=
  (rootEnumeration.surjective).comp (rootOrder i).surjective

lemma root_add_simple_iff (i : Fin 4) (r s : Fin 24) :
    (typeDRootPairing 2).root (orderedRoot i r) =
      (typeDRootPairing 2).root (typeDSimpleRootIndex 2 i) +
      (typeDRootPairing 2).root (orderedRoot i s) ↔ raisingEdge r s := by
  rw [← orderedRoot_zero i, root_add_iff, ordered_add]

lemma root_sub_simple_iff (i : Fin 4) (r s : Fin 24) :
    (typeDRootPairing 2).root (orderedRoot i r) =
      (typeDRootPairing 2).root (orderedRoot i s) -
      (typeDRootPairing 2).root (typeDSimpleRootIndex 2 i) ↔ raisingEdge s r := by
  rw [eq_sub_iff_add_eq, eq_comm, add_comm ((typeDRootPairing 2).root (orderedRoot i r)), root_add_simple_iff]

lemma chainBot_zero (i : Fin 4) (r s : Fin 24) (h : raisingEdge r s) :
    (typeDRootPairing 2).chainBotCoeff (typeDSimpleRootIndex 2 i) (orderedRoot i s) = 0 := by
  apply (typeDRootPairing 2).chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨k, hk⟩
  obtain ⟨k, rfl⟩ := orderedRoot_surjective i k
  have hk := (root_sub_simple_iff i k s).mp hk
  unfold raisingEdge at h hk
  omega

lemma chainTop_zero (i : Fin 4) (r s : Fin 24) (h : raisingEdge s r) :
    (typeDRootPairing 2).chainTopCoeff (typeDSimpleRootIndex 2 i) (orderedRoot i s) = 0 := by
  apply (typeDRootPairing 2).chainTopCoeff_eq_zero_iff.mpr
  right
  rintro ⟨k, hk⟩
  obtain ⟨k, rfl⟩ := orderedRoot_surjective i k
  have hk := (root_add_simple_iff i k s).mp (hk.trans (add_comm _ _))
  unfold raisingEdge at h hk
  omega

lemma root_add_nsmul_iff (i : Fin 4) (r s : Fin 24) (n : ℕ) :
    (typeDRootPairing 2).root (orderedRoot i r) =
      (typeDRootPairing 2).root (orderedRoot i s) +
      n • (typeDRootPairing 2).root (typeDSimpleRootIndex 2 i) ↔
    orderedCoords i r = orderedCoords i s + n • orderedCoords i 0 := by
  rw [← orderedRoot_zero i, Subtype.ext_iff, funext_iff, funext_iff]
  simp only [Submodule.coe_add, Pi.add_apply,
    Submodule.coe_smul_of_tower, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, orderedCoords_spec]
  apply forall_congr'
  intro j
  exact_mod_cast (Int.cast_inj (α := ℝ) (m := orderedCoords i r j)
    (n := orderedCoords i s j + (n : ℤ) * orderedCoords i 0 j))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma ordered_add_two (i : Fin 4) (r s : Fin 24) :
    orderedCoords i r = orderedCoords i s + 2 • orderedCoords i 0 ↔ r = 0 ∧ s = 1 := by
  revert i r s
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma ordered_add_three (i : Fin 4) (r s : Fin 24) :
    orderedCoords i r ≠ orderedCoords i s + 3 • orderedCoords i 0 := by
  revert i r s
  decide +kernel

lemma chainBot_one (i : Fin 4) :
    (typeDRootPairing 2).chainBotCoeff (typeDSimpleRootIndex 2 i) (orderedRoot i 1) = 0 := by
  apply (typeDRootPairing 2).chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨k, hk⟩
  obtain ⟨k, rfl⟩ := orderedRoot_surjective i k
  have hk := (root_sub_simple_iff i k 1).mp hk
  norm_num [raisingEdge] at hk
  omega

lemma chainTop_zero_root (i : Fin 4) :
    (typeDRootPairing 2).chainTopCoeff (typeDSimpleRootIndex 2 i) (orderedRoot i 0) = 0 := by
  apply (typeDRootPairing 2).chainTopCoeff_eq_zero_iff.mpr
  right
  rintro ⟨k, hk⟩
  obtain ⟨k, rfl⟩ := orderedRoot_surjective i k
  have hk := (root_add_simple_iff i k 0).mp (hk.trans (add_comm _ _))
  simp [raisingEdge] at hk

lemma orderedRoot_one (i : Fin 4) :
    orderedRoot i 1 = (typeDRootPairing 2).reflectionPerm
      (typeDSimpleRootIndex 2 i) (typeDSimpleRootIndex 2 i) := by
  apply (typeDRootPairing 2).root.injective
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  apply Subtype.ext
  ext j
  rw [← orderedRoot_zero i]
  simp only [Submodule.coe_neg, Pi.neg_apply, orderedCoords_spec]
  have h : orderedCoords i 1 j = -orderedCoords i 0 j := by
    revert i j
    decide +kernel
  rw [h, Int.cast_neg]

end
end Triality.Standard.Parabolics.RankOneMatrices
