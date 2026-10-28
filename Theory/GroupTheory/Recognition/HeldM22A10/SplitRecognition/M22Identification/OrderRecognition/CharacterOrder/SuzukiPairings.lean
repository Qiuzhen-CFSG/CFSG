module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ModelPairCounts
public import Theory.Character.ClassFunctionSum
public import Theory.GroupTheory.ConjugacyClassSize

/-!
# The five involution-pair scalar products

For the five actual exceptional inductions supplied by `SpecialInductionData`,
class support reduces the ambient scalar product to five conjugacy classes.
The first exceptional row separates those classes. Orbit–stabilizer cancels
the ambient group order, leaving each value weighted by the reciprocal of its
centralizer order. The ambient involution-pair counts then give the five
rational constants in Janko's Suzuki identities.

This proves the pairing calculation from explicit induction data; constructing
that data remains the separate normalizer-character argument.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6–7, pp.11–15,
DOI 10.1016/0021-8693(68)90002-1.
-/

open scoped BigOperators
noncomputable section
attribute [local instance 100] Fintype.ofFinite

/-- Average a class function supported on a separating family of classes.
Grouping by conjugacy class and applying orbit–stabilizer gives the weights. -/
private theorem sum_supported_classes {G R : Type*} [Group G] [Finite G] [Fintype R]
    (f : ClassFunction G) (hf : IsClassFunction f) (a : R → G)
    (hsep : Function.Injective (fun i => ConjClasses.mk (a i)))
    (hsupport : ∀ g, (∀ i, ¬ IsConj g (a i)) → f g = 0) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g =
      ∑ i, f (a i) / (Nat.card (Subgroup.centralizer ({a i} : Set G)) : ℂ) := by
  classical
  let F := toConjClassFunction f hf
  have hfiber (d : ConjClasses G) :
      Fintype.card {g : G // ConjClasses.mk g = d} = Nat.card d.carrier := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight
      (fun _ => ConjClasses.mem_carrier_iff_mk_eq.symm))
  have hsum : ∑ g : G, f g =
      ∑ d : ConjClasses G, (Nat.card d.carrier : ℂ) * F d := by
    have h := Fintype.sum_fiberwise' ConjClasses.mk F
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfiber,
      F, toConjClassFunction_apply] using h.symm
  have hs : ∑ d : ConjClasses G, (Nat.card d.carrier : ℂ) * F d =
      ∑ i, (Nat.card (ConjClasses.mk (a i)).carrier : ℂ) * f (a i) := by
    symm
    apply Fintype.sum_of_injective (fun i => ConjClasses.mk (a i)) hsep
    · intro d hd
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep d
      have hz : f g = 0 := hsupport g (by
        intro i hi
        exact hd ⟨i, ConjClasses.mk_eq_mk_iff_isConj.mpr hi.symm⟩)
      simp only [F, toConjClassFunction_apply, hz, mul_zero]
    · intro i
      rfl
  rw [hsum, hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hG : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hC : (Nat.card (Subgroup.centralizer ({a i} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({a i} : Set G))).ne'
  have hc : (Nat.card (ConjClasses.mk (a i)).carrier : ℂ) *
      (Nat.card (Subgroup.centralizer ({a i} : Set G)) : ℂ) = Nat.card G := by
    exact_mod_cast (show Nat.card (ConjClasses.mk (a i)).carrier *
      Nat.card (Subgroup.centralizer ({a i} : Set G)) = Nat.card G by
        rw [ConjClasses.nat_card_carrier_eq_index_centralizer, Subgroup.index_mul_card])
  apply (eq_div_iff hC).mpr
  calc
    _ = (Nat.card G : ℂ)⁻¹ *
        ((Nat.card (ConjClasses.mk (a i)).carrier : ℂ) *
          (Nat.card (Subgroup.centralizer ({a i} : Set G)) : ℂ)) * f (a i) := by ring
    _ = f (a i) := by rw [hc, inv_mul_cancel₀ hG, one_mul]

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k)

private theorem induced_class (i : Fin 5) : IsClassFunction (I.induced i) :=
  inducedClassFunction_isClassFunction _ _

-- The values 16, 4, -2, -4, 0 in the first row already separate every column.
include I in
private theorem special_classes_injective :
    Function.Injective (fun r => ConjClasses.mk (CaseII.into D k (specialRepresentative r))) := by
  intro r s hrs
  have hv := congrArg (toConjClassFunction (I.induced 0) (induced_class D k I 0)) hrs
  change I.induced 0 (CaseII.into D k (specialRepresentative r)) =
    I.induced 0 (CaseII.into D k (specialRepresentative s)) at hv
  simp only [SpecialInductionData.induced, I.values] at hv
  have hinj : Function.Injective (exceptionalValues 0) := by decide +kernel
  apply hinj
  exact_mod_cast hv

include L in
private theorem special_centralizer_card (r : Fin 5) :
    Nat.card (Subgroup.centralizer ({CaseII.into D k (specialRepresentative r)} : Set G)) =
      (![384, 12, 8, 32, 16] r : ℕ) := by
  fin_cases r
  · change Nat.card (Subgroup.centralizer ({CaseII.into D k (CaseII.z 0)} : Set G)) = 384
    rw [CaseII.into_z_zero]
    exact D.centralizer_card
  · exact L.centralizer_orders 3
  · exact L.centralizer_orders 2
  · exact L.centralizer_orders 0
  · exact L.centralizer_orders 1

include L in
/-- The five actual induced functions have the Suzuki scalar products
`31/12, -1, 91/12, 25/6, -5` against the ambient involution-pair count. -/
public theorem hasSuzukiPairings_of_localAnalysis : HasSuzukiPairings I := by
  intro i
  have hf : IsClassFunction (fun g => I.induced i g *
      (Theory.Character.involutionPairCount g : ℂ)) := by
    intro g x
    dsimp only
    exact congrArg₂ (· * ·) (induced_class D k I i g x)
      (Theory.Character.involutionPairCount_isClassFunction g x)
  have hs := sum_supported_classes
    (fun g => I.induced i g * (Theory.Character.involutionPairCount g : ℂ)) hf
    (fun r => CaseII.into D k (specialRepresentative r)) (special_classes_injective D k I)
    (by
      intro g hg
      change exceptionalInduction D k I.character i g * _ = 0
      rw [I.support i g hg, zero_mul])
  simp only [scalarProduct, star_natCast]
  rw [hs]
  simp only [SpecialInductionData.induced, I.values, ambient_involutionPairCount,
    special_centralizer_card D k L]
  fin_cases i <;> norm_num [exceptionalValues, pairingConstants, Fin.sum_univ_succ]

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
