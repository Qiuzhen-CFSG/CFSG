module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.CoefficientPowers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Kernel

/-!
# The Borel kernel and inner–coefficient reduction

Once the concrete Borel is the semidirect product of the positive subgroup
and the constructed torus, its normalizer action on a torus subgroup has
trivial inner factor. This is the commutator/disjointness argument from
`EvenActions.Kernel`, applied after the proved coefficient power calculation.
If the Borel is also the normalizer of the positive subgroup, universal
inner–coefficient coverage reduces every positive-subgroup-preserving
automorphism to this situation. Binary parameter transport uses the actual
equality of parameter records, so the coverage premise is on BinaryCarrier.

`BorelGeometry` contains only the precise geometric inputs. They are not
proved here, and the resulting conditional theorems do not establish the
source assertion until this geometry and the source Cartan alignment are
constructed. In particular no inner-action-kernel conclusion is a premise.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, p.511, and A.3.15(5), pp.50–51; GLS3 §§2.3–2.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

noncomputable section
open Subgroup
open scoped IsMulCommutative
open Triality.Standard.Parabolics Triality.Standard.OuterOdd
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions
namespace Triality.Standard.CartanAction

/-- The precise Borel geometry used by the action argument. -/
structure BorelGeometry (P : Parameters) : Prop where
  disjoint : Disjoint (unipotent P) (torus P)
  normalizes : torus P ≤ normalizer (unipotent P)
  product : ∀ d ∈ borel P, ∃ u ∈ unipotent P, ∃ t ∈ torus P, d = u * t
  normalizer_eq : normalizer (unipotent P) = borel P

lemma borel_kernel (P : Parameters) (hp : P.prime = 2) (hG : BorelGeometry P)
    (B : Subgroup (Carrier P)) (hB : B ≤ torus P) :
    borel P ⊓ normalizer B ≤ centralizer (B : Set (Carrier P)) := by
  let _ : IsMulCommutative (torus P) :=
    ⟨⟨fun a b => Subtype.ext (torus_commutes P hp a.property b.property)⟩⟩
  intro d hd
  obtain ⟨u, hu, t, ht, rfl⟩ := hG.product d hd.1
  exact borel_centralizes (unipotent P) (torus P) B hG.disjoint hG.normalizes hB hu ht hd.2

lemma borel_coefficient_power (P : Parameters) (hp : P.prime = 2)
    (hG : BorelGeometry P) (B : Subgroup (Carrier P)) (hB : B ≤ torus P)
    (a : MulAut (Carrier P)) (haB : B.map a.toMonoidHom = B)
    (d : Carrier P) (hd : d ∈ borel P) (σ : CoefficientAut P)
    (ha : a = MulAut.conj d * coefficientAction P σ) :
    ∃ k : ℕ, ∀ b ∈ B, a b = b ^ (2 ^ k) := by
  have hdB : d ∈ normalizer B := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [ha] at haB
    change B.map ((MulAut.conj d).toMonoidHom.comp
      (coefficientAction P σ).toMonoidHom) = B at haB
    rw [← map_map, coefficient_preserves_torus_subgroup P hp σ B hB] at haB
    exact haB
  have hc := borel_kernel P hp hG B hB (show d ∈ borel P ⊓ normalizer B from ⟨hd, hdB⟩)
  obtain ⟨k, hk⟩ := coefficient_torus_power P hp σ
  refine ⟨k, fun b hb => ?_⟩
  have hσb : coefficientAction P σ b ∈ B := by
    rw [hk b (hB hb)]
    exact B.pow_mem hb _
  calc
    a b = d * coefficientAction P σ b * d⁻¹ := by rw [ha]; rfl
    _ = coefficientAction P σ b := by
      rw [← mem_centralizer_iff.mp hc _ hσb, mul_inv_cancel_right]
    _ = b ^ (2 ^ k) := hk b (hB hb)

lemma normalizer_power_of_coverage (P : Parameters) (hp : P.prime = 2)
    (hG : BorelGeometry P)
    (hcover : ∀ a : MulAut (Carrier P), ∃ d : Carrier P, ∃ σ : CoefficientAut P,
      a = MulAut.conj d * coefficientAction P σ)
    (B : Subgroup (Carrier P)) (hB : B ≤ torus P)
    (a : MulAut (Carrier P)) (haB : B.map a.toMonoidHom = B)
    (haU : (unipotent P).map a.toMonoidHom = unipotent P) :
    ∃ k : ℕ, ∀ b ∈ B, a b = b ^ (2 ^ k) := by
  obtain ⟨d, σ, ha⟩ := hcover a
  have hd : d ∈ borel P := by
    rw [← hG.normalizer_eq]
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [ha] at haU
    change (unipotent P).map ((MulAut.conj d).toMonoidHom.comp
      (coefficientAction P σ).toMonoidHom) = unipotent P at haU
    rw [← map_map, coefficient_preserves_unipotent P σ] at haU
    exact haU
  exact borel_coefficient_power P hp hG B hB a haB d hd σ ha

lemma normalizer_power_of_binary_coverage (P : Parameters) (n : ℕ) (hn : 0 < n)
    (hq : P.q = 2 ^ n) (hG : BorelGeometry P)
    (hcover : ∀ a : MulAut (BinaryCarrier n hn), ∃ d : BinaryCarrier n hn,
      ∃ σ : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj d * coefficientAction (binaryParameters n hn) σ)
    (B : Subgroup (Carrier P)) (hB : B ≤ torus P)
    (a : MulAut (Carrier P)) (haB : B.map a.toMonoidHom = B)
    (haU : (unipotent P).map a.toMonoidHom = unipotent P) :
    ∃ k : ℕ, ∀ b ∈ B, a b = b ^ (2 ^ k) := by
  have hP := P.eq_binaryParameters_of_q_eq n hn hq
  subst P
  exact normalizer_power_of_coverage _ rfl hG hcover B hB a haB haU

end Triality.Standard.CartanAction
