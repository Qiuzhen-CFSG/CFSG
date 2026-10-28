module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor.LocalReduction

/-!
# Square-trivial actors in the full nonbinary long G₂ parabolic

Write Q for the five-root radical and L for the long local subgroup. In
coordinates (a,b,c,d,0,f), the square in Q has A and B coordinates
(c + df)d and (c + df)f. Conjugation by a general parabolic element, factored
as a line scalar, a radical element, and an SL₂ block, sends (d,f) through
the corresponding two-dimensional matrix and multiplies c + df by the line
scalar. Comparing three coordinates proves these identities with the entire
radical factor retained.

The square conditions for D(1), C(1)D(1), F(1), and C(1)F(1) then force the
line scalar to be one. This puts each actor in L. The existing subnormal
intersection theorem places X in Q, and two-perfection eliminates X.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526 of `refs/quasithin.pdf`,
using the local structure in F.1.12(I)(3),(II). The explicit octonion model,
root product law, and scalar/vector-stabilizer factorization are from the
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
This proves the nonbinary standard-model actor calculation used by that
source argument.
-/

public section

open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit Atlas.G2.PairStabilizer
open Atlas.G2.LieParabolicSetup
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor
variable {F : Type*} [Field F] [CharP F 2]

private theorem square_coords (t : Fin 6 → F) (ht : t 4 = 0) (h : unipotentProduct t ^ 2 = 1) :
    (t 2 + t 3 * t 5) * t 3 = 0 ∧ (t 2 + t 3 * t 5) * t 5 = 0 := by
  have he : unipotentProductParameters t t = 0 := by
    apply unipotentProduct_injective
    rw [← unipotentProduct_mul, ← pow_two, h, unipotentProduct_zero]
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp only [unipotentProductParameters, ht, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  constructor
  · linear_combination h0 - (t 0 + t 2 * t 3 - 5 * t 3 ^ 2 * t 5) * htwo
  · linear_combination h1 - (t 1 - 2 * t 2 * t 5 + t 3 * t 5 ^ 2) * htwo

-- Comparing the images of the fourth basis vector retains every radical
-- parameter; its contributions cancel in the three displayed identities.
private theorem conjugate_coords (l : Fˣ) (t s u : Fin 6 → F) (M : SL(2,F))
    (ht : t 4 = 0) (hs : s 4 = 0) (hu : u 4 = 0)
    (he : unipotentProduct u * (torus l 1 * (unipotentProduct t * blockHom M)) =
      (torus l 1 * (unipotentProduct t * blockHom M)) * unipotentProduct s) :
    u 3 = M 0 0 * s 3 + M 0 1 * s 5 ∧
    u 5 = (l : F) * (M 1 0 * s 3 + M 1 1 * s 5) ∧
    u 2 + u 3 * u 5 = (l : F) * (s 2 + s 3 * s 5) := by
  have h0 := congrArg (fun g : Model F => g.val (basisVector 3) 0) he
  have h1 := congrArg (fun g : Model F => g.val (basisVector 3) 1) he
  have h2 := congrArg (fun g : Model F => g.val (basisVector 3) 2) he
  simp [unipotentProduct, rootA, rootB, rootC, rootD, rootE, rootF,
    rootAEquiv, rootBEquiv, rootCEquiv, rootDEquiv, rootEEquiv, rootFEquiv,
    rootALinear, rootBLinear, rootCLinear, rootDLinear, rootELinear, rootFLinear,
    rootAApply, rootBApply, rootCApply, rootDApply, rootEApply, rootFApply,
    torus, torusEquiv, torusLinear, torusWeights, blockHom, blockEquiv, blockLinear,
    basisVector, ht, hs, hu, CharTwo.neg_eq, CharTwo.sub_eq_add] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h1
  · linear_combination h2
  · linear_combination h0 - t 3 * h2 - (l : F) * t 5 * h1

private theorem product_inv_square_coords (s u : Fin 6 → F) (hs : s 4 = 0) (hu : u 4 = 0)
    (h : (unipotentProduct s * (unipotentProduct u)⁻¹) ^ 2 = 1) :
    (s 2 + u 2 + (s 3 + u 3) * (s 5 + u 5)) * (s 3 + u 3) = 0 ∧
    (s 2 + u 2 + (s 3 + u 3) * (s 5 + u 5)) * (s 5 + u 5) = 0 := by
  rw [unipotentProduct_inv, unipotentProduct_mul] at h
  have hv : unipotentProductParameters s (unipotentInverseParameters u) 4 = 0 := by
    simp [unipotentProductParameters, unipotentInverseParameters, hs, hu]
  have he := square_coords _ hv h
  simpa [unipotentProductParameters, unipotentInverseParameters, hs, hu,
    CharTwo.sub_eq_add, CharTwo.neg_eq, CharTwo.two_eq_zero, add_comm] using he

variable [Finite F]

private theorem factor_square_constraints (g : parabolic₂ (F := F))
    (l : Fˣ) (t : Fin 6 → F) (M : SL(2,F)) (ht : t 4 = 0)
    (hg : g.val = torus l 1 * (unipotentProduct t * blockHom M))
    (hsq : ∀ q ∈ radical₂ (F := F), ⁅q, g.val⁆ ^ 2 = 1) (c d f : F) :
    let D := M 0 0 * d + M 0 1 * f
    let E := (l : F) * (M 1 0 * d + M 1 1 * f)
    let z := (1 + (l : F)) * (c + d * f) + d * E + D * f
    z * (d + D) = 0 ∧ z * (f + E) = 0 := by
  let s : Fin 6 → F := ![0,0,c,d,0,f]
  have hs : unipotentProduct s ∈ radical₂ := ⟨s, rfl, rfl⟩
  have hu := (Subgroup.mem_normalizer_iff.mp
    (EvenLocal.parabolic₂_le_normalizer_radical₂ g.property) (unipotentProduct s)).mp hs
  obtain ⟨u, hu, he⟩ := hu
  have hconj : unipotentProduct u * g.val = g.val * unipotentProduct s := by
    rw [he]
    group
  have hc := conjugate_coords l t s u M ht rfl hu (hg ▸ hconj)
  have hprod : (unipotentProduct s * (unipotentProduct u)⁻¹) ^ 2 = 1 := by
    have hh := hsq (unipotentProduct s) hs
    rw [he]
    convert hh using 1
    simp [commutatorElement_def, mul_assoc]
  have hcoords := product_inv_square_coords s u rfl hu hprod
  dsimp [s] at hc hcoords
  dsimp
  have hz : c + u 2 + (d + u 3) * (f + u 5) =
      (1 + (l : F)) * (c + d * f) +
        d * ((l : F) * (M 1 0 * d + M 1 1 * f)) +
        (M 0 0 * d + M 0 1 * f) * f := by
    linear_combination hc.2.2 + f * hc.1 + d * hc.2.1
  rw [hz, hc.1, hc.2.1] at hcoords
  exact hcoords

private theorem factor_scalar_eq_one (g : parabolic₂ (F := F))
    (l : Fˣ) (t : Fin 6 → F) (M : SL(2,F)) (ht : t 4 = 0)
    (hg : g.val = torus l 1 * (unipotentProduct t * blockHom M))
    (hsq : ∀ q ∈ radical₂ (F := F), ⁅q, g.val⁆ ^ 2 = 1) : l = 1 := by
  have hD0 := factor_square_constraints g l t M ht hg hsq 0 1 0
  have hD1 := factor_square_constraints g l t M ht hg hsq 1 1 0
  have hF0 := factor_square_constraints g l t M ht hg hsq 0 0 1
  have hF1 := factor_square_constraints g l t M ht hg hsq 1 0 1
  dsimp at hD0 hD1 hF0 hF1
  by_contra hl
  have hl' : (l : F) ≠ 1 := fun he => hl (Units.ext he)
  have hn : 1 + (l : F) ≠ 0 := by
    intro he
    apply hl'
    simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right he)
  have h00 : 1 + M 0 0 = 0 := by
    apply (mul_eq_zero.mp (show (1 + (l : F)) * (1 + M 0 0) = 0 from ?_)).resolve_left hn
    linear_combination hD1.1 - hD0.1
  have h01 : M 0 1 = 0 := by
    apply (mul_eq_zero.mp (show (1 + (l : F)) * M 0 1 = 0 from ?_)).resolve_left hn
    linear_combination hF1.1 - hF0.1
  have h11 : 1 + (l : F) * M 1 1 = 0 := by
    apply (mul_eq_zero.mp (show (1 + (l : F)) * (1 + (l : F) * M 1 1) = 0 from ?_)).resolve_left hn
    linear_combination hF1.2 - hF0.2
  have h00' : M 0 0 = 1 := by
    simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right h00)
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.property
  have h11' : M 1 1 = 1 := by simpa only [h00', h01, one_mul, zero_mul, sub_zero] using hdet
  apply hn
  simpa only [h11', mul_one] using h11

omit [Finite F] in
-- The scalar normalization and opposite-vector stabilizer factorization
-- are the same ones used to compute the full parabolic's two-core.
private theorem full_factor (g : parabolic₂ (F := F)) :
    ∃ (l : Fˣ) (t : Fin 6 → F) (M : SL(2,F)), t 4 = 0 ∧
      g.val = torus l 1 * (unipotentProduct t * blockHom M) := by
  let gp : pointStabilizer (K := F) :=
    ⟨g.val, by rw [← parabolic_eq_pointStabilizer]; exact g.property⟩
  let h : fixingFirstVector (K := F) := normalizePoint gp
  have hl : h.val ∈ local₂ := by rw [local₂_eq_fixingFirstVector]; exact h.property
  rw [← SetLike.mem_coe, local₂_eq_radical₂_mul_fixingPair] at hl
  obtain ⟨u, ⟨t, ht, rfl⟩, m, hm, he⟩ := hl
  refine ⟨lineScalar gp, t, imageSL ⟨m, hm⟩, ht, ?_⟩
  have hb := congrArg Subtype.val (block_imageSL ⟨m, hm⟩)
  change blockHom (imageSL ⟨m, hm⟩) = m at hb
  change unipotentProduct t * m = h.val at he
  rw [hb, he]
  change g.val = torus (lineScalar gp) 1 * ((torus (lineScalar gp) 1)⁻¹ * g.val)
  exact (mul_inv_cancel_left _ _).symm

private theorem square_mem_local (g : parabolic₂ (F := F))
    (hsq : ∀ q ∈ radical₂ (F := F), ⁅q, g.val⁆ ^ 2 = 1) : g.val ∈ local₂ := by
  obtain ⟨l, t, M, ht, hg⟩ := full_factor g
  have hl := factor_scalar_eq_one g l t M ht hg hsq
  have hone : torus (1 : Fˣ) 1 = 1 := (torusHom (K := F)).map_one
  rw [hg, hl, hone, one_mul]
  exact local₂.mul_mem (radical₂_le_local₂ ⟨t, ht, rfl⟩) (block_mem_local₂ M)

open Subgroup

/-- A subnormal two-perfect subgroup of the full nonbinary second parabolic
with square-trivial radical commutators is trivial. -/
theorem full_actor_eq_bot (hq : 2 < Nat.card F)
    (X : Subgroup (parabolic₂ (F := F))) (hX : X.IsSubnormal) (hp : IsPPerfect 2 X)
    (hsq : ∀ q ∈ pCore 2 (parabolic₂ (F := F)), ∀ x ∈ X,
      (⁅q,x⁆ : parabolic₂)^2 = 1) : X = ⊥ := by
  have hlocal (x : parabolic₂ (F := F)) (hx : x ∈ X) : x.val ∈ local₂ := by
    apply square_mem_local x
    intro q hq
    let qP : parabolic₂ (F := F) :=
      ⟨q, local₂_le_parabolic₂ (radical₂_le_local₂ hq)⟩
    have hqP : qP ∈ pCore 2 (parabolic₂ (F := F)) := by
      rw [EvenLocal.parabolic₂_pCore]
      exact hq
    have he := congrArg (parabolic₂ (F := F)).subtype (hsq qP hqP x hx)
    exact he
  have hinter := full_intersection_le_core hq X hX hsq
  have hle : X ≤ pCore 2 (parabolic₂ (F := F)) := by
    intro x hx
    let y : local₂ (F := F) := ⟨x.val, hlocal x hx⟩
    have hy : y ∈ X.comap (Subgroup.inclusion local₂_le_parabolic₂) := hx
    have hc := hinter hy
    rw [local₂_pCore] at hc
    rw [EvenLocal.parabolic₂_pCore]
    exact hc
  have hpX : IsPGroup 2 X := pCore_isPGroup.to_le hle
  have he := hp.hom_eq_one_of_isPGroup hpX (MonoidHom.id X)
  apply X.eq_bot_iff_forall.mpr
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x, hx⟩)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor

end
