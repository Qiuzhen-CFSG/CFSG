module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Torus
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.FixedFactors
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.CommutatorGeneration.TorusAction

/-!
# Splitting off the complementary torus in the linear Ree Levi

The paired end-node coroot word lies in the fixed subsystem Levi and has
long simple-root characters `(a², a⁻¹)`. Squaring is bijective on the units
of the finite characteristic-two coefficient field. Thus every element
of the full fixed torus is the product of an internal subsystem torus
element and the actual diagonal element with characters `(1,c)`.

This proves generation of the entire full Levi by the subsystem Levi and
the specified one-dimensional complementary torus. Commutation and trivial
intersection are proved in the representation assembly.

Source: GLS3, Theorem 2.6.5(f), `refs/KGroup/GLS3/chapter2.tex`, and the
linear factor in Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section

namespace ReeF4.ConverseParabolics.FullLeviRepresentation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
open Parabolics LargeLocalSeeds LargeLocalSeeds.LinearCommutators
open LocalBlockInput.PairRigidity BlockParameters BlockParameters.FieldRecovery
open FixedCollection.SeedGeneration
open SectionGeometry.LinearRadical (fullLevi)
variable {m : ℕ}
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def endParameters (a : (CoefficientField m)ˣ) : TorusParameters m :=
  integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv 0) a *
    integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv 3)
      (Units.map (theta m) a)

private theorem endParameters_characters (a : (CoefficientField m)ˣ) :
    rootScale (endParameters a) (typeF4SimpleRootIndex 0) = a ^ 2 ∧
      rootScale (endParameters a) (typeF4SimpleRootIndex 1) = a⁻¹ := by
  have hp (i j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [endParameters, rootScale_mul]
  simp only [rootScale,
    integralChevalleyRootScale_simpleCorootParameter, typeF4RootPairing_baseEquiv_val,
    hp]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private theorem endTorusWord_matrix (a : (CoefficientField m)ˣ) :
    (endTorusWord m a).val = (torusMatrix (endParameters a))⁻¹ := by
  have hθ : Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0) :
      CoefficientField m →* CoefficientField m) a = Units.map (theta m) a := by
    apply Units.ext
    exact rootFieldEnd_simple_zero_eq_theta _
  unfold endTorusWord
  rw [hθ]
  simp only [Subgroup.coe_mul,
    ← typeF4RootPairing_baseEquiv_val, torusWord_simple_coe]
  have hinv (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ) :
      integralChevalleySimpleCorootParameter i u⁻¹ =
        (integralChevalleySimpleCorootParameter i u)⁻¹ := by
    funext q
    simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
    split_ifs <;> simp
  rw [hinv, hinv, ← map_mul, ← mul_inv]
  change diagonalTorusHom m (endParameters a)⁻¹ = _
  rw [map_inv]
  rfl

private theorem endTorusWord_mem_levi (a : (CoefficientField m)ˣ) :
    endTorusWord m a ∈ splitLevi m .linear := by
  have hw (i : Fin 4) (hi : i ∈ leviNodes .linear) (t : CoefficientField m) :
      weylWord m (typeF4SimpleRootIndex i) t ∈ splitLevi m .linear := by
    have hp (v : CoefficientField m) :
        rootGeneratorInGroup m (typeF4SimpleRootIndex i) v ∈ splitLevi m .linear :=
      mem_sup_left (subset_closure ⟨_, _, isSimpleBlockRoot_simple .linear i hi, rfl⟩)
    have hn (v : CoefficientField m) :
        rootGeneratorInGroup m (-typeF4SimpleRootIndex i) v ∈ splitLevi m .linear :=
      mem_sup_right (subset_closure ⟨_, _, isSimpleBlockRoot_neg_simple .linear i hi, rfl⟩)
    exact mul_mem (mul_mem (hp _) (hn _)) (hp _)
  have ht (i : Fin 4) (hi : i ∈ leviNodes .linear) (v : (CoefficientField m)ˣ) :
      torusWord m (typeF4SimpleRootIndex i) v ∈ splitLevi m .linear :=
    mul_mem (hw i hi _) (hw i hi _)
  exact mul_mem (ht 0 (by simp [leviNodes]) _) (ht 3 (by simp [leviNodes]) _)

/-- The internal rank-one torus has long-root characters a² and a⁻¹. -/
theorem internal_torus_mem (a : (CoefficientField m)ˣ) :
    torusElement (a ^ 2) a⁻¹ ∈ (seedLeviHom m).range := by
  let d := canonicalLocalBlockInput m
  let h : SplitGroup m := (endTorusWord m a)⁻¹
  have hh : h.val = torusMatrix (endParameters a) := by
    change (endTorusWord m a).val⁻¹ = _
    rw [endTorusWord_matrix, inv_inv]
  have hf : d.twist h = h := by
    dsimp only [h]
    rw [map_inv, endTorusWord_fixed]
  have hc := compatible_eq_blockTorus (endParameters a)
    (twistCompatible_of_fixed _ h hh hf)
  rw [(endParameters_characters a).1, (endParameters_characters a).2] at hc
  let l : fixedLevi d .linear :=
    ⟨⟨endTorusWord m a, endTorusWord_fixed d a⟩, endTorusWord_mem_levi a⟩
  refine ⟨l, ?_⟩
  apply toSplitGroup_injective m
  apply Subtype.ext
  change (toSplitGroup m (d.modelEquiv l.val)).val = _
  rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe, torusElement_matrix]
  exact (endTorusWord_matrix a).trans (congrArg (fun u => (torusMatrix u)⁻¹) hc)

/-- The complementary torus is the actual diagonal subgroup with trivial end-root character. -/
def complementHom (m : ℕ) : (CoefficientField m)ˣ →* Model m :=
  (torusHom m).comp (MonoidHom.inr _ _)

theorem complementHom_apply (a : (CoefficientField m)ˣ) :
    complementHom m a = torusElement 1 a := rfl

theorem complementHom_injective (m : ℕ) : Function.Injective (complementHom m) := by
  intro a b hab
  exact congrArg Prod.snd (torusHom_injective m hab)

theorem fixedTorus_le_seed_sup_complement (m : ℕ) :
    fixedTorus m ≤ (seedLeviHom m).range ⊔ (complementHom m).range := by
  intro x hx
  obtain ⟨b, c, rfl⟩ := exists_torusElement x hx
  have hs : Function.Surjective (fun a : (CoefficientField m)ˣ => a ^ 2) := by
    apply Finite.surjective_of_injective
    intro a b hab
    apply Units.ext
    exact (frobenius_inj (CoefficientField m) 2) (congrArg Units.val hab)
  obtain ⟨a, rfl⟩ := hs b
  have he : torusElement (a ^ 2) c = torusElement (a ^ 2) a⁻¹ *
      complementHom m (a * c) := by
    change torusHom m (a ^ 2, c) = torusHom m (a ^ 2, a⁻¹) * torusHom m (1, a * c)
    rw [← map_mul]
    congr 1
    ext <;> simp
  rw [he]
  exact mul_mem_sup (internal_torus_mem a) ⟨a * c, rfl⟩

/-- Every full-Levi element lies in the product generated by the fixed subsystem and this complement. -/
theorem fullLevi_eq_seed_sup_complement (m : ℕ) :
    fullLevi m = (seedLeviHom m).range ⊔ (complementHom m).range := by
  rw [fullLevi_eq_seedLevi_sup_torus]
  apply le_antisymm
  · exact sup_le le_sup_left (fixedTorus_le_seed_sup_complement m)
  · apply sup_le le_sup_left
    rintro x ⟨a, rfl⟩
    exact mem_sup_right (torusElement_mem 1 a)

end ReeF4.ConverseParabolics.FullLeviRepresentation
