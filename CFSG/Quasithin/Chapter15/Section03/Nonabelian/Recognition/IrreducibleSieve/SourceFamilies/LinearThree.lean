module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Linear
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.FieldDescent
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.TensorKernel
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.Representation.Quotient
public import CFSG.Quasithin.ClassicalModels

/-!
# Excluding the binary projective linear-three source family

The actual elementary actor embeds in the automorphism group of the normal
irreducible component. The full PSL₃ automorphism-rank theorem bounds its rank
by twice the matrix-field exponent. Inflating along the literal central
projection and applying the exhaustive absolute SL₃ catalogue leaves the
natural, dual-natural and half-field tensor actions; the remaining degree
bound is too large.

Natural-action transitivity contradicts the source invariant nonsingular
binary quadratic form. In the tensor branch the source degree forces the
half-field exponent to be two. Descent on the original carrier factors through
the same projective quotient. Its faithful tensor comparison makes that
projection injective, contradicting the order-three center of SL₃(16).

Source: Aschbacher--Smith, G.9.3(8),(17), printed pp.354,356--357, and the
irreducible branch of 15.3.58, printed p.1149. The conclusion uses only the
source action and component data with the actual PSL₃ model; no additional
module-recognition, involution-placement or model-exclusion premise remains.
-/

public section
open Subgroup Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
open ChapterG.Section09
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Theory.GroupTheory

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

private theorem no_transitive_inflation (h : SourceData ρ X T v s)
    {D M : Type*} [Group D] [AddCommGroup M] [Module (ZMod 2) M]
    (π : D →* K) (τ : Representation (ZMod 2) D M)
    (ht : ∀ x y : M, x ≠ 0 → y ≠ 0 → ∃ g, τ g x = y)
    (e : Representation.Equiv ((ρ.comp K.subtype).comp π) τ) : False := by
  have ht' : ∀ x y : W, x ≠ 0 → y ≠ 0 →
      ∃ g : D, ((ρ.comp K.subtype).comp π) g x = y := by
    intro x y hx hy
    obtain ⟨g, hg⟩ := ht (e x) (e y)
      (fun he => hx (e.toLinearEquiv.map_eq_zero_iff.mp he))
      (fun he => hy (e.toLinearEquiv.map_eq_zero_iff.mp he))
    refine ⟨g, e.toLinearEquiv.injective ?_⟩
    exact (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x).trans hg
  obtain ⟨q, hn, hi⟩ := h.quadratic
  exact not_nondegenerate_quadratic_of_nonzero_transitive _
    (by have := h.six_le_degree; omega) ht' q (fun g w => hi (π g).val w) hn

private theorem inverseTranspose_twice {F : Type*} [Field F] (g : SL(3,F)) :
    Matrix.SpecialLinearGroup.inverseTranspose
      (Matrix.SpecialLinearGroup.inverseTranspose g) = g := by
  change ((Matrix.SpecialLinearGroup.inverseTranspose g)⁻¹).transpose = g
  rw [← map_inv]
  change ((g⁻¹)⁻¹).transpose.transpose = g
  rw [inv_inv]
  apply Subtype.ext
  rfl

private theorem no_twisted_projective_four
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ 4)
    (σ : Representation (ZMod 2) PSL(3,F) W) (hfaith : Function.Injective σ)
    [IsIrreducible (σ.comp (Matrix.PSL3.projection F))]
    (hschur : schurDegree (σ.comp (Matrix.PSL3.projection F)) = 2)
    (hmodel : HasAbsoluteTwistedModel (σ.comp (Matrix.PSL3.projection F)) 2) : False := by
  let π := Matrix.PSL3.projection F
  obtain ⟨a, ha, _, _, S, _, _, scalar, τ, hτ, he, _⟩ :=
    descend_absolute_twisted (σ.comp π) 2 (by decide) hcard hschur hmodel
  let := scalar
  let := ZMod.algebra S 2
  have hker : center SL(3,F) ≤ τ.ker := by
    intro g hg
    change τ g = 1
    ext w
    have hp : π g = 1 := (MonoidHom.mem_ker.mp ((Matrix.PSL3.projection_ker F).symm ▸ hg))
    have hh := congrArg (fun r : Representation (ZMod 2) SL(3,F) W => r g w) hτ
    change τ g w = σ (π g) w at hh
    simpa only [hp, map_one, Module.End.one_apply] using hh
  let τq : Representation S PSL(3,F) W := quotientOfLEKer τ (center SL(3,F)) hker
  have hτq : Function.Injective τq := by
    intro x y hxy
    obtain ⟨g, rfl⟩ := Matrix.PSL3.projection_surjective F x
    obtain ⟨k, rfl⟩ := Matrix.PSL3.projection_surjective F y
    apply hfaith
    ext w
    have hh := congrArg (fun f : Module.End S W => f w) hxy
    change τ g w = τ k w at hh
    have hg := congrArg (fun r : Representation (ZMod 2) SL(3,F) W => r g w) hτ
    have hk := congrArg (fun r : Representation (ZMod 2) SL(3,F) W => r k w) hτ
    exact hg.symm.trans (hh.trans hk)
  have hz : center SL(3,F) = ⊥ := by
    rw [← Matrix.PSL3.projection_ker F]
    exact tensor_cover_kernel_fourth π (by rw [Matrix.PSL3.projection_ker]) τq hτq a
      (by simpa using ha) he
  have hc := (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp hz
  exact hc (by rw [hcard]; decide)

/-- The actual binary PSL₃ family is incompatible with the source irreducible action. -/
theorem SourceData.not_linearThree_source (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {n : ℕ} (hn : 1 ≤ n)
    (hmodel : ClassicalGroup.IsPSL K 3 (2 ^ n)) : False := by
  classical
  obtain ⟨F, field, finite, hcard, ⟨e⟩⟩ := hmodel
  let := field
  let := finite
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  let := ZMod.algebra F 2
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  have hrank : s + 1 ≤ 2 * n := by
    have hm := h.setup.rank_le_automorphisms (L := K)
      (show X ≤ Subgroup.normalizer (K : Set H) by
        rw [Subgroup.normalizer_eq_top_iff.mpr hK.normal]
        exact le_top)
    rw [primeRank_equiv 2 (MulAut.congr e),
      Matrix.PSL3Even.automorphism_two_rank_eq F (by omega) hcard] at hm
    exact hm
  let σ : Representation (ZMod 2) PSL(3,F) W :=
    (ρ.comp K.subtype).comp e.symm.toMonoidHom
  let π := Matrix.PSL3.projection F
  let τ := σ.comp π
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp K.subtype)).mpr hK.irreducible
  let : IsIrreducible τ := (irreducible_comp_surjective_iff π
    (Matrix.PSL3.projection_surjective F) σ).mpr inferInstance
  have hfaith : Function.Injective σ := h.faithful.comp
    (K.subtype_injective.comp e.symm.injective)
  have hnon : ∃ g, τ g ≠ 1 := by
    have hne : Nontrivial K := by
      by_contra hc
      have : Subsingleton K := not_nontrivial_iff_subsingleton.mp hc
      exact hK.nonsolvable inferInstance
    let := hne
    obtain ⟨x, hx⟩ := exists_ne (1 : K)
    obtain ⟨g, hg⟩ := Matrix.PSL3.projection_surjective F (e x)
    refine ⟨g, fun hz => hx ?_⟩
    apply K.subtype_injective
    apply h.faithful
    simpa [τ, σ, hg, π] using hz
  obtain ⟨hpos, hnat | htw | hlarge⟩ :=
    AbsoluteExhaustion.absolute_model_trichotomy τ hnon n (by omega) hcard
  · obtain ⟨hschur, _, habs⟩ := hnat
    have hdesc : Nonempty (Representation.Equiv τ (naturalBinary F)) ∨
        Nonempty (Representation.Equiv τ (dualBinary F)) :=
      descend_absolute_natural τ n hcard hschur habs
    rcases hdesc with hnat | hdual
    · obtain ⟨φ⟩ := hnat
      exact no_transitive_inflation h (e.symm.toMonoidHom.comp π)
        (naturalBinary F) (fun x y hx hy =>
          Matrix.SpecialLinearGroup.exists_mulVec_eq_three x y hx hy) φ
    · obtain ⟨φ⟩ := hdual
      apply no_transitive_inflation h (e.symm.toMonoidHom.comp π) (dualBinary F) ?_ φ
      intro x y hx hy
      obtain ⟨g, hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three x y hx hy
      refine ⟨Matrix.SpecialLinearGroup.inverseTranspose g, ?_⟩
      change naturalBinary F (Matrix.SpecialLinearGroup.inverseTranspose
        (Matrix.SpecialLinearGroup.inverseTranspose g)) x = y
      rw [inverseTranspose_twice]
      exact hg
  · obtain ⟨hfield, hdim, habs⟩ := htw
    have hd := h.dimension
    have hr : schurDegree τ = 2 := by omega
    have hn4 : n = 4 := by omega
    have hcard4 : Nat.card F = 2 ^ 4 := by rwa [hn4] at hcard
    rw [hr] at habs
    exact no_twisted_projective_four hcard4 σ hfaith hr habs
  · have hd := h.dimension
    omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
