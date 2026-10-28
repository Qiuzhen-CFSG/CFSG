module
public import Theory.Representation.BinaryPermutationEightCover.FixedLine
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.HalfWeight
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Affine coordinates of the four-dimensional eight-point code

A binary four-dimensional subspace of the eight-point augmentation core,
with only weights zero, four and eight, is self-dual for the coordinate dot
product. Thus two coordinate evaluations cannot agree: their difference
would give a weight-two word in the code. If the code contains the constant
word, these eight evaluations are precisely the affine hyperplane of
functionals taking value one on that word.

The dot-product argument reuses the attributed ATLAS half-weight identity;
no enumeration of subspaces or permutations is used.
Source: Aschbacher–Smith Lemma 12.3.3, printed p.808, the augmentation-core
normalizer calculation.
-/

@[expose] public noncomputable section
open Module
namespace BinaryPermutation.EightCore
open Atlas.Order20160A8.HalfWeight Atlas.Codes

private theorem hamming_eq_weight (w : Full (Fin 8)) : hammingNorm w = wordWeight w := by
  rfl

private theorem code_halfWeight_zero (U : Submodule (ZMod 2) (core (Fin 8)))
    (hw : ∀ v ∈ U, v ≠ 0 → v ≠ oneWord → wordWeight v.val = 4)
    (v : U) : binaryHalfWeight v.val.val = 0 := by
  by_cases hz : v.val = 0
  · rw [hz]
    exact binaryHalfWeight_zero
  by_cases h1 : v.val = oneWord
  · rw [h1]
    decide
  · change ((hammingNorm v.val.val / 2 : ℕ) : ZMod 2) = 0
    rw [hamming_eq_weight,hw _ v.property hz h1]
    decide

/-- A code whose nonconstant nonzero words have weight four is
self-orthogonal for the literal coordinate dot product. -/
theorem code_dot_eq_zero (U : Submodule (ZMod 2) (core (Fin 8)))
    (hw : ∀ v ∈ U, v ≠ 0 → v ≠ oneWord → wordWeight v.val = 4)
    (v w : U) : dotProduct v.val.val w.val.val = 0 := by
  have he (v : U) : 2 ∣ hammingNorm v.val.val := by
    rw [hamming_eq_weight]
    rcases weights v.val with h | h | h | h | h <;> rw [h] <;> decide
  have h := binaryHalfWeight_add v.val.val w.val.val (he v) (he w) (he (v+w))
  have hv := code_halfWeight_zero U hw v
  have hw' := code_halfWeight_zero U hw w
  have hs := code_halfWeight_zero U hw (v+w)
  change binaryHalfWeight (v.val.val+w.val.val) = 0 at hs
  rw [hv,hw',hs,zero_add,zero_add] at h
  exact h.symm

/-- At dimension four the full code is its own orthogonal complement.
This is the original eight-coordinate space, retaining its constant line. -/
theorem code_self_dual (U : Submodule (ZMod 2) (core (Fin 8)))
    (hd : finrank (ZMod 2) U = 4)
    (hw : ∀ v ∈ U, v ≠ 0 → v ≠ oneWord → wordWeight v.val = 4) :
    let D := U.map (core (Fin 8)).subtype
    D.map (dotProductEquiv (ZMod 2) (Fin 8)).toLinearMap = D.dualAnnihilator := by
  let D := U.map (core (Fin 8)).subtype
  let d := dotProductEquiv (ZMod 2) (Fin 8)
  have hle : D.map d.toLinearMap ≤ D.dualAnnihilator := by
    rintro _ ⟨v,⟨v,hv,rfl⟩,rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    rintro w ⟨w,hw',rfl⟩
    exact code_dot_eq_zero U hw ⟨v,hv⟩ ⟨w,hw'⟩
  have hdim : finrank (ZMod 2) D = 4 := by
    rw [Submodule.finrank_map_subtype_eq]
    exact hd
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq D
  have hall : finrank (ZMod 2) (Full (Fin 8)) = 8 := by simp [Full]
  rw [hdim,hall] at hann
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [d.finrank_map_eq,hdim]
  change 4 = finrank (ZMod 2) D.dualAnnihilator
  change 4 + finrank (ZMod 2) D.dualAnnihilator = 8 at hann
  omega

/-- Distinct positions induce distinct functionals on a four-dimensional
doubly-even code. Otherwise their weight-two difference lies in its dual. -/
theorem code_evaluation_injective (U : Submodule (ZMod 2) (core (Fin 8)))
    (hd : finrank (ZMod 2) U = 4)
    (hw : ∀ v ∈ U, v ≠ 0 → v ≠ oneWord → wordWeight v.val = 4) :
    Function.Injective (fun i : Fin 8 => fun v : U => v.val.val i) := by
  intro i j hij
  by_contra hn
  let v : Full (Fin 8) := Pi.single i 1 + Pi.single j 1
  have hdott : (dotProductEquiv (ZMod 2) (Fin 8)) v ∈
      (U.map (core (Fin 8)).subtype).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro w ⟨w,hw',rfl⟩
    change dotProduct (Pi.single i 1 + Pi.single j 1) w.val = 0
    rw [add_dotProduct,single_dotProduct,single_dotProduct,one_mul,one_mul]
    have he := congrFun hij (⟨w,hw'⟩ : U)
    change w.val i = w.val j at he
    rw [he,CharTwo.add_self_eq_zero]
  rw [← code_self_dual U hd hw] at hdott
  obtain ⟨v',⟨w,hw',hvw⟩,hv'⟩ := hdott
  have he : w.val = v := hvw.trans ((dotProductEquiv (ZMod 2) (Fin 8)).injective hv')
  have hvwt : wordWeight w.val = 2 := by
    rw [he]
    change (Finset.univ.filter fun k => (Pi.single i 1 + Pi.single j 1 : Full (Fin 8)) k ≠ 0).card = 2
    have hh : (Finset.univ.filter fun k =>
        (Pi.single i 1 + Pi.single j 1 : Full (Fin 8)) k ≠ 0) = {i,j} := by
      ext k
      by_cases hki : k = i
      · subst k; simp [Pi.single_apply,hn]
      by_cases hkj : k = j
      · subst k; simp [Pi.single_apply,Ne.symm hn]
      · simp [Pi.single_apply,hki,hkj]
    rw [hh,Finset.card_pair hn]
  have hw0 : w ≠ 0 := fun h => by
    have h0 := (weight_zero_iff w).mpr h
    omega
  have hw1 : w ≠ oneWord := fun h => by
    have h8 := (weight_eight_iff w).mpr h
    omega
  have hh := hw w hw' hw0 hw1
  omega

/-- Restriction of a literal coordinate evaluation to the code. -/
def codeEvaluation (U : Submodule (ZMod 2) (core (Fin 8))) (i : Fin 8) :
    Module.Dual (ZMod 2) U :=
  (LinearMap.proj i).comp ((core (Fin 8)).subtype.comp U.subtype)

/-- The eight coordinates are exactly the eight functionals taking value
one on the constant word. No arbitrary permutation model is introduced. -/
def codeAffineCoordinates (U : Submodule (ZMod 2) (core (Fin 8)))
    (hd : finrank (ZMod 2) U = 4) (hone : oneWord ∈ U)
    (hw : ∀ v ∈ U, v ≠ 0 → v ≠ oneWord → wordWeight v.val = 4) :
    Fin 8 ≃ {φ : Module.Dual (ZMod 2) U // φ ⟨oneWord,hone⟩ = 1} := by
  classical
  let : Finite (Module.Dual (ZMod 2) U) := Module.finite_of_finite (ZMod 2)
  let z : U := ⟨oneWord,hone⟩
  let ev : Module.Dual (ZMod 2) U →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun φ => φ z
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hsur : Function.Surjective ev := by
    intro c
    exact ⟨c • codeEvaluation U 0,by change c * 1 = c; exact mul_one _⟩
  have hk : finrank (ZMod 2) ev.ker = 3 := by
    have hh := ev.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsur,finrank_top,finrank_self,
      Subspace.dual_finrank_eq,hd] at hh
    omega
  have hcard : Nat.card {φ : Module.Dual (ZMod 2) U // φ z = 1} = 8 := by
    have hh := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective
      (f := ev.toAddMonoidHom) hsur 1)
    change Nat.card {φ : Module.Dual (ZMod 2) U // φ z = 1} = Nat.card ev.ker at hh
    rw [hh]
    change Nat.card ev.ker = 8
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hk]
    decide
  let f : Fin 8 → {φ : Module.Dual (ZMod 2) U // φ z = 1} :=
    fun i => ⟨codeEvaluation U i,rfl⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply code_evaluation_injective U hd hw
    exact funext fun v => LinearMap.congr_fun (congrArg Subtype.val hij) v
  exact Equiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf,by simpa only [Nat.card_fin] using hcard.symm⟩)

end BinaryPermutation.EightCore
