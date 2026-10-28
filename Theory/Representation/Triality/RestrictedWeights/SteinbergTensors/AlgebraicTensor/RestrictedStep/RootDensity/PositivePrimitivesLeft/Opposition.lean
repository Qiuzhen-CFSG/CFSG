module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft.Duality
public import Theory.AlgebraicGroup.Tori.Character.Duality

/-!
# Pinned opposition in algebraic D4 geometry

The cube of the Coxeter word `(0, 1, 2, 3)` acts as root negation. We check
its action in four-reflection blocks and lift it to the actual products of
the supplied Chevalley representatives. In characteristic two their signs
are one, so every pinned root parameter is preserved.

The Chevalley coroot expansion and linear independence of the simple
coroots give `h_{-α}(t) = h_α(t⁻¹)`. Character separation, together with the
supplied fundamental character coordinates, expresses every actual torus
point as a product of simple-coroot values. The same representative
therefore inverts the whole supplied torus. These two equations construct
`Opposition` without a further geometric or representation-theoretic premise.

Sources: GLS3 Chapter 1, §§1.9 and 1.12, especially 1.12.1(e), (h), (i);
Steinberg, *Representations of Algebraic Groups* (1963), equation (6.1),
`refs/KGroup/GLS3/Chapter2St2.tex`. All conjugation formulas retain the raw
GLS convention and the supplied pinning.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft
@[expose] public noncomputable section
universe u
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 1, v 0, v 2, v 3]
  | 1, v => ![v 0, v 2, v 1, v 3]
  | 2, v => ![v 0, v 1, v 3, v 2]
  | 3, v => ![v 0, v 1, -v 3, -v 2]

private theorem reflection_val (i : Fin 4) (r : TypeDRootIndex 4) :
    ((typeDRootPairing 2).root
      ((typeDRootPairing 2).reflectionPerm (typeDSimpleRootIndex 2 i) r) : Vec 4) =
      reflectedVector i ((typeDRootPairing 2).root r) := by
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeDRootPairing_pairing]
  simp only [Submodule.coe_sub, Submodule.coe_smul, typeDRootPairing_simpleRoot_val]
  rw [typeDRootEmbedding_typeDSimpleRootIndex]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [reflectedVector, typeDSimpleRoot, dot, basisVector, Fin.sum_univ_four]

private def simpleRoot (S : D4Geometry K) (i : Fin 4) : S.roots.Root :=
  S.rootEquiv.symm (typeDSimpleRootIndex 2 i)

private def rootWord (S : D4Geometry K) : List (Fin 4) → S.roots.Root → S.roots.Root
  | [], α => α
  | i :: w, α => S.roots.reflect (simpleRoot S i) (rootWord S w α)

private def representativeWord (S : D4Geometry K) : List (Fin 4) → Variety.Point K
  | [] => 1
  | i :: w => representativeWord S w * S.chevalley.n (simpleRoot S i) 1

private def coxeterWord : List (Fin 4) := [0, 1, 2, 3]
private def oppositionWord : List (Fin 4) := coxeterWord ++ coxeterWord ++ coxeterWord

private theorem rootWord_append (S : D4Geometry K) (a b : List (Fin 4))
    (α : S.roots.Root) : rootWord S (a ++ b) α = rootWord S a (rootWord S b α) := by
  induction a with
  | nil => rfl
  | cons i a ih => simp only [List.cons_append, rootWord, ih]

private theorem rootWord_val (S : D4Geometry K) (i : Fin 4) (w : List (Fin 4))
    (α : S.roots.Root) :
    ((typeDRootPairing 2).root (S.rootEquiv (rootWord S (i :: w) α)) : Vec 4) =
      reflectedVector i ((typeDRootPairing 2).root (S.rootEquiv (rootWord S w α))) := by
  simp only [rootWord, S.based.2.1, simpleRoot, Equiv.apply_symm_apply, reflection_val]

private theorem coxeterWord_val (S : D4Geometry K) (α : S.roots.Root) :
    ((typeDRootPairing 2).root (S.rootEquiv (rootWord S coxeterWord α)) : Vec 4) =
      ![-((typeDRootPairing 2).root (S.rootEquiv α) : Vec 4) 2,
        ((typeDRootPairing 2).root (S.rootEquiv α) : Vec 4) 0,
        ((typeDRootPairing 2).root (S.rootEquiv α) : Vec 4) 1,
        -((typeDRootPairing 2).root (S.rootEquiv α) : Vec 4) 3] := by
  simp only [coxeterWord, rootWord_val]
  ext j
  fin_cases j <;> simp [reflectedVector, rootWord, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem rootWord_opposition (S : D4Geometry K) (α : S.roots.Root) :
    rootWord S oppositionWord α = S.roots.neg α := by
  apply S.rootEquiv.injective
  apply (typeDRootPairing 2).root.injective
  apply Subtype.ext
  rw [S.based.2.2.1, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  simp only [oppositionWord, rootWord_append, coxeterWord_val]
  ext j
  fin_cases j <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]

private theorem root_reflection_commute [CharP k 2] (S : D4Geometry K) (α β : S.roots.Root) (t : k) :
    S.chevalley.x α t * S.chevalley.n β 1 =
      S.chevalley.n β 1 * S.chevalley.x (S.roots.reflect β α) t := by
  obtain ⟨sgn, hs, hx, _⟩ := S.chevalley_spec.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsgn : (sgn α β : k) = 1 := by
    rcases hs α β with h | h <;> simp [h, CharTwo.neg_eq]
  have h := hx α β t
  rw [hsgn, one_mul] at h
  exact (inv_mul_eq_iff_eq_mul).1 (by simpa only [← mul_assoc] using h)

private theorem root_word_commute [CharP k 2] (S : D4Geometry K) (w : List (Fin 4))
    (α : S.roots.Root) (t : k) :
    S.chevalley.x α t * representativeWord S w =
      representativeWord S w * S.chevalley.x (rootWord S w α) t := by
  induction w with
  | nil => simp [representativeWord, rootWord]
  | cons i w ih =>
    simp only [representativeWord, rootWord]
    rw [← mul_assoc, ih, mul_assoc, root_reflection_commute, ← mul_assoc]

private theorem coroot_word_commute (S : D4Geometry K) (w : List (Fin 4))
    (α : S.roots.Root) (t : kˣ) :
    S.chevalley.h α t * representativeWord S w =
      representativeWord S w * S.chevalley.h (rootWord S w α) t := by
  obtain ⟨_, _, _, hh, _⟩ := S.chevalley_spec.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc (α β : S.roots.Root) : S.chevalley.h α t * S.chevalley.n β 1 =
      S.chevalley.n β 1 * S.chevalley.h (S.roots.reflect β α) t :=
    (inv_mul_eq_iff_eq_mul).1 (by simpa only [← mul_assoc] using hh α β t)
  induction w with
  | nil => simp [representativeWord, rootWord]
  | cons i w ih =>
    simp only [representativeWord, rootWord]
    rw [← mul_assoc, ih, mul_assoc, hc, ← mul_assoc]

private theorem coroot_neg (S : D4Geometry K) (α : S.roots.Root) (t : kˣ) :
    S.chevalley.h (S.roots.neg α) t = S.chevalley.h α t⁻¹ := by
  classical
  obtain ⟨c, hc, hh⟩ := S.chevalley_spec.2.2.2.2.2.2.2.1
  have hn : (typeDRootPairing 2).coroot (S.rootEquiv (S.roots.neg α)) =
      -(typeDRootPairing 2).coroot (S.rootEquiv α) := by
    rw [S.based.2.2.1, RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self]
  have he : (fun i => (c (S.roots.neg α) i : ℝ)) = (fun i => -(c α i : ℝ)) := by
    apply (typeDRootPairing_base 2).linearIndepOn_coroot.fintypeLinearCombination_injective
    simp only [Fintype.linearCombination_apply, neg_smul, Int.cast_smul_eq_zsmul]
    rw [Finset.sum_neg_distrib]
    exact (hc (S.roots.neg α)).symm.trans (hn.trans (congrArg Neg.neg (hc α)))
  have hcneg (i) : c (S.roots.neg α) i = -c α i := by
    exact_mod_cast congrFun he i
  rw [hh, hh]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hcneg, zpow_neg, inv_zpow]

private def fundamentalCharacter (S : D4Geometry K) (i : Fin 4) : TorusWeight S.torus :=
  S.characters (Multiplicative.ofAdd (Pi.single i 1))

private theorem weight_expand (S : D4Geometry K) (a : D4RestrictedWeight.Weight) :
    S.characters (Multiplicative.ofAdd a) =
      fundamentalCharacter S 0 ^ a 0 * fundamentalCharacter S 1 ^ a 1 *
      fundamentalCharacter S 2 ^ a 2 * fundamentalCharacter S 3 ^ a 3 := by
  unfold fundamentalCharacter
  simp only [← map_zpow S.characters, ← map_mul S.characters]
  congr 1
  change a = a 0 • Pi.single 0 1 + a 1 • Pi.single 1 1 +
    a 2 • Pi.single 2 1 + a 3 • Pi.single 3 1
  funext i
  fin_cases i <;> simp

private theorem torus_point_ext [IsAlgClosed k] (S : D4Geometry K)
    (t v : Variety.Point S.torus.carrierVariety)
    (h : ∀ i, (fundamentalCharacter S i).pointCharacter t =
      (fundamentalCharacter S i).pointCharacter v) : t = v := by
  apply (torusPointEval_bijective S.maximalTorus.1).injective
  apply MonoidHom.ext
  intro χ
  obtain ⟨a, rfl⟩ := S.characters.surjective χ
  change torusPointEval _ t (S.characters (Multiplicative.ofAdd a.toAdd)) =
    torusPointEval _ v (S.characters (Multiplicative.ofAdd a.toAdd))
  rw [weight_expand]
  have h' (i : Fin 4) : torusPointEval _ t (fundamentalCharacter S i) =
      torusPointEval _ v (fundamentalCharacter S i) := Units.ext (h i)
  simp only [map_mul, map_zpow, h']

private theorem weight_coroot (S : D4Geometry K) (a : D4RestrictedWeight.Weight)
    (i : Fin 4) (z : Variety.Point (KMult k)) :
    (S.characters (Multiplicative.ofAdd a)).pointCharacter
      ((S.roots.rootCocharacter (simpleRoot S i)).onPoints z) =
      (dPointEquiv 1 z 0 : k) ^ a i := S.weightEmbedding_coroot a i z

private theorem simple_coroot_decomposition [IsAlgClosed k] (S : D4Geometry K)
    (t : Variety.Point S.torus.carrierVariety) :
    t = (S.roots.rootCocharacter (simpleRoot S 0)).onPoints
          ((fundamentalCharacter S 0).onPoints t) *
        (S.roots.rootCocharacter (simpleRoot S 1)).onPoints
          ((fundamentalCharacter S 1).onPoints t) *
        (S.roots.rootCocharacter (simpleRoot S 2)).onPoints
          ((fundamentalCharacter S 2).onPoints t) *
        (S.roots.rootCocharacter (simpleRoot S 3)).onPoints
          ((fundamentalCharacter S 3).onPoints t) := by
  apply torus_point_ext S
  intro i
  simp only [map_mul, fundamentalCharacter, weight_coroot]
  fin_cases i <;> simp [TorusCharacter.pointCharacter]

private theorem torus_commute_of_coroots [IsAlgClosed k] (S : D4Geometry K)
    (n : Variety.Point K)
    (hn : ∀ α z, S.chevalley.h α z * n = n * S.chevalley.h α z⁻¹)
    (t : Variety.Point S.torus.carrierVariety) :
    S.torus.includePoint t * n = n * S.torus.includePoint t⁻¹ := by
  let f := MulAut.conj n⁻¹
  have hh (α : S.roots.Root) (z : kˣ) : f (S.chevalley.h α z) =
      S.chevalley.h α z⁻¹ := by
    change n⁻¹ * S.chevalley.h α z * (n⁻¹)⁻¹ = _
    rw [inv_inv, mul_assoc, hn, inv_mul_cancel_left]
  have hinc (a b : Variety.Point S.torus.carrierVariety) :
      S.torus.includePoint (a * b) = S.torus.includePoint a * S.torus.includePoint b :=
    map_mul S.torus.inclusion.onPoints a b
  have he : f (S.torus.includePoint t) = S.torus.includePoint t⁻¹ := by
    conv_lhs => rw [simple_coroot_decomposition S t]
    conv_rhs => rw [simple_coroot_decomposition S t⁻¹]
    simp only [hinc, map_mul, S.coroot_spec, hh]
    simp only [map_inv, LeftWeights.dPointEquiv_inverse, Pi.inv_apply]
  exact (inv_mul_eq_iff_eq_mul).1 (by simpa only [f, MulAut.conj_apply, inv_inv,
    ← mul_assoc] using he)

/-- The actual product of twelve pinned simple-reflection representatives. -/
def oppositionPoint (S : D4Geometry K) : Variety.Point K :=
  ([0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3] : List (Fin 4)).foldr
    (fun i n => n * S.chevalley.n (S.rootEquiv.symm (typeDSimpleRootIndex 2 i)) 1) 1

private theorem oppositionPoint_eq_word (S : D4Geometry K) :
    oppositionPoint S = representativeWord S oppositionWord := rfl

/-- Opposition negates every pinned root and preserves its field parameter. -/
theorem oppositionPoint_root_commute [CharP k 2] (S : D4Geometry K)
    (α : S.roots.Root) (t : k) :
    S.chevalley.x α t * oppositionPoint S =
      oppositionPoint S * S.chevalley.x (S.roots.neg α) t := by
  simpa only [oppositionPoint_eq_word, rootWord_opposition] using
    root_word_commute S oppositionWord α t

private theorem oppositionPoint_coroot_commute (S : D4Geometry K)
    (α : S.roots.Root) (t : kˣ) :
    S.chevalley.h α t * oppositionPoint S =
      oppositionPoint S * S.chevalley.h α t⁻¹ := by
  simpa only [oppositionPoint_eq_word, rootWord_opposition, coroot_neg] using
    coroot_word_commute S oppositionWord α t

/-- The same pinned representative inverts every point of the supplied torus. -/
theorem oppositionPoint_torus_commute [IsAlgClosed k] (S : D4Geometry K)
    (t : Variety.Point S.torus.carrierVariety) :
    S.torus.includePoint t * oppositionPoint S =
      oppositionPoint S * S.torus.includePoint t⁻¹ :=
  torus_commute_of_coroots S (oppositionPoint S) (oppositionPoint_coroot_commute S) t

/-- Genuine opposition constructed from the supplied pinning in characteristic two. -/
def opposition [IsAlgClosed k] [CharP k 2] (S : D4Geometry K) : Opposition S where
  point := oppositionPoint S
  root_commute := oppositionPoint_root_commute S
  torus_commute := oppositionPoint_torus_commute S

/-- Every algebraic D4 geometry has pinned opposition in characteristic two. -/
theorem opposition_nonempty [IsAlgClosed k] [CharP k 2] (S : D4Geometry K) :
    Nonempty (Opposition S) := ⟨opposition S⟩

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft
