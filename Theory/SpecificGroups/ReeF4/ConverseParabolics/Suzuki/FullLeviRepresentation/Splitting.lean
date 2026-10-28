module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Torus
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.FullLeviRepresentation.FixedFactors
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer.Torus

/-!
# Splitting the full torus of the Suzuki-side Ree Levi

The paired middle coroot word has long simple-root characters
`a⁻¹` and `a² / θ(a)²`. The identity `θ(θ(c))² = c` shows that the
second character takes the value `c` at `a = c * θ(c)`. Thus the fixed
subsystem torus and the actual complementary torus with characters `(b,1)`
generate the entire fixed torus, and hence the full Levi.

Source: GLS3, Theorem 2.6.5(f), `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section

namespace ReeF4.ConverseParabolics.SuzukiFullLeviRepresentation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
open Parabolics LargeLocalSeeds FullLeviRepresentation
open LocalBlockInput.PairRigidity BlockParameters BlockParameters.FieldRecovery
open FixedCollection.SeedGeneration
open SuzukiLevi (fullLevi)
variable {m : ℕ}
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def middleParameters (a : (CoefficientField m)ˣ) : TorusParameters m :=
  integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv 1) a *
    integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv 2)
      (Units.map (theta m : CoefficientField m →* CoefficientField m) a)

/-- The middle-root character of the fixed subsystem torus. -/
def internalCharacter (a : (CoefficientField m)ˣ) : (CoefficientField m)ˣ :=
  a ^ 2 * (Units.map (theta m : CoefficientField m →* CoefficientField m) a ^ 2)⁻¹

private theorem middleParameters_characters (a : (CoefficientField m)ˣ) :
    rootScale (middleParameters a) (typeF4SimpleRootIndex 0) = a⁻¹ ∧
      rootScale (middleParameters a) (typeF4SimpleRootIndex 1) = internalCharacter a := by
  have hp (i j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [middleParameters, rootScale_mul]
  simp only [rootScale,
    integralChevalleyRootScale_simpleCorootParameter, typeF4RootPairing_baseEquiv_val,
    hp]
  norm_num [typeF4CartanMatrix, Fin.ext_iff, internalCharacter]

private theorem middle_torus_matrix (a : (CoefficientField m)ˣ) :
    (SuzukiNormalizer.torus a (Units.map (theta m : CoefficientField m →* CoefficientField m) a)).val =
      (torusMatrix (middleParameters a))⁻¹ := by
  simp only [SuzukiNormalizer.torus, Subgroup.coe_mul,
    ← typeF4RootPairing_baseEquiv_val, torusWord_simple_coe]
  have hinv (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ) :
      integralChevalleySimpleCorootParameter i u⁻¹ =
        (integralChevalleySimpleCorootParameter i u)⁻¹ := by
    funext q
    simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
    split_ifs <;> simp
  rw [hinv, hinv, ← map_mul, ← mul_inv]
  change diagonalTorusHom m (middleParameters a)⁻¹ = _
  rw [map_inv]
  rfl

private theorem middle_torus_fixed (a : (CoefficientField m)ˣ) :
    (canonicalLocalBlockInput m).twist (SuzukiNormalizer.torus a (Units.map (theta m : CoefficientField m →* CoefficientField m) a)) =
      SuzukiNormalizer.torus a (Units.map (theta m : CoefficientField m →* CoefficientField m) a) := by
  apply (SuzukiNormalizer.torus_fixed_iff _ _ _).mpr
  apply Units.ext
  exact (LocalIndices.SuzukiGaussData.tits_theta _).symm

private theorem middle_torus_mem_levi (a : (CoefficientField m)ˣ) :
    SuzukiNormalizer.torus a (Units.map (theta m : CoefficientField m →* CoefficientField m) a) ∈ splitLevi m .suzuki := by
  have hw (i : Fin 4) (hi : i ∈ leviNodes .suzuki) (t : CoefficientField m) :
      weylWord m (typeF4SimpleRootIndex i) t ∈ splitLevi m .suzuki := by
    have hp (v : CoefficientField m) :
        rootGeneratorInGroup m (typeF4SimpleRootIndex i) v ∈ splitLevi m .suzuki :=
      mem_sup_left (subset_closure ⟨_, _, isSimpleBlockRoot_simple .suzuki i hi, rfl⟩)
    have hn (v : CoefficientField m) :
        rootGeneratorInGroup m (-typeF4SimpleRootIndex i) v ∈ splitLevi m .suzuki :=
      mem_sup_right (subset_closure ⟨_, _, isSimpleBlockRoot_neg_simple .suzuki i hi, rfl⟩)
    exact mul_mem (mul_mem (hp _) (hn _)) (hp _)
  have ht (i : Fin 4) (hi : i ∈ leviNodes .suzuki) (v : (CoefficientField m)ˣ) :
      torusWord m (typeF4SimpleRootIndex i) v ∈ splitLevi m .suzuki :=
    mul_mem (hw i hi _) (hw i hi _)
  exact mul_mem (ht 1 (by simp [leviNodes]) _) (ht 2 (by simp [leviNodes]) _)

/-- The paired middle coroot word realizes the internal fixed torus. -/
theorem internal_torus_mem (a : (CoefficientField m)ˣ) :
    torusElement a⁻¹ (internalCharacter a) ∈ (seedLeviHom m).range := by
  let d := canonicalLocalBlockInput m
  let w := SuzukiNormalizer.torus a (Units.map (theta m : CoefficientField m →* CoefficientField m) a)
  let h : SplitGroup m := w⁻¹
  have hh : h.val = torusMatrix (middleParameters a) := by
    change (SuzukiNormalizer.torus a (Units.map (theta m : CoefficientField m →* CoefficientField m) a)).val⁻¹ = _
    rw [middle_torus_matrix, inv_inv]
  have hf : d.twist h = h := by
    dsimp only [h, w]
    rw [map_inv, middle_torus_fixed]
  have hc := compatible_eq_blockTorus (middleParameters a)
    (twistCompatible_of_fixed _ h hh hf)
  rw [(middleParameters_characters a).1, (middleParameters_characters a).2] at hc
  let l : fixedLevi d .suzuki :=
    ⟨⟨w, middle_torus_fixed a⟩, middle_torus_mem_levi a⟩
  refine ⟨l, ?_⟩
  apply toSplitGroup_injective m
  apply Subtype.ext
  change (toSplitGroup m (d.modelEquiv l.val)).val = _
  rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe, torusElement_matrix]
  exact (middle_torus_matrix a).trans (congrArg (fun u => (torusMatrix u)⁻¹) hc)

/-- Every middle-root character occurs in the actual subsystem torus. -/
theorem internalCharacter_surjective : Function.Surjective (internalCharacter (m := m)) := by
  intro c
  refine ⟨c * Units.map (theta m : CoefficientField m →* CoefficientField m) c, ?_⟩
  have hθ : Units.map (theta m : CoefficientField m →* CoefficientField m) (Units.map (theta m : CoefficientField m →* CoefficientField m) c) ^ 2 = c := by
    apply Units.ext
    change (theta m (theta m c.val)) ^ 2 = c.val
    simp only [theta_apply, ← pow_mul, ← pow_add]
    rw [show 2 ^ (m + m) * 2 = 2 ^ (2 * m + 1) by
      rw [pow_succ]; congr 2; omega]
    exact field_pow m c.val
  simp only [internalCharacter, map_mul, mul_pow, hθ]
  simp [mul_assoc, mul_comm, mul_left_comm, pow_two]

/-- The actual complementary torus has trivial middle-root character. -/
def complementHom (m : ℕ) : (CoefficientField m)ˣ →* Model m :=
  (torusHom m).comp (MonoidHom.inl _ _)

theorem complementHom_apply (a : (CoefficientField m)ˣ) :
    complementHom m a = torusElement a 1 := rfl

theorem complementHom_injective (m : ℕ) : Function.Injective (complementHom m) := by
  intro a b hab
  exact congrArg Prod.fst (torusHom_injective m hab)

theorem fixedTorus_le_seed_sup_complement (m : ℕ) :
    fixedTorus m ≤ (seedLeviHom m).range ⊔ (complementHom m).range := by
  intro x hx
  obtain ⟨b, c, rfl⟩ := exists_torusElement x hx
  obtain ⟨a, rfl⟩ := internalCharacter_surjective c
  have he : torusElement b (internalCharacter a) =
      torusElement a⁻¹ (internalCharacter a) * complementHom m (a * b) := by
    change torusHom m (b, internalCharacter a) =
      torusHom m (a⁻¹, internalCharacter a) * torusHom m (a * b, 1)
    rw [← map_mul]
    congr 1
    ext <;> simp
  rw [he]
  exact mul_mem_sup (internal_torus_mem a) ⟨a * b, rfl⟩

/-- The actual subsystem and complementary torus generate the full fixed Levi. -/
theorem fullLevi_eq_seed_sup_complement (m : ℕ) :
    fullLevi m = (seedLeviHom m).range ⊔ (complementHom m).range := by
  rw [fullLevi_eq_seedLevi_sup_torus]
  apply le_antisymm
  · exact sup_le le_sup_left (fixedTorus_le_seed_sup_complement m)
  · apply sup_le le_sup_left
    rintro x ⟨a, rfl⟩
    exact mem_sup_right (torusElement_mem a 1)

end ReeF4.ConverseParabolics.SuzukiFullLeviRepresentation
