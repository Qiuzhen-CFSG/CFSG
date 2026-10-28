module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.SquareFibers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.ActionContract

/-!
# The elementary-quotient step of Suzuki Lemma 14.7

An involution outside T centralizes T modulo M°. The marked torus action
moves its coset to every nonidentity coset, so all elements of S square
into M°. This proves elementary abelianness of the actual image of S in
M/M°. Both the literal involution and source omega formulations are given.

The torus-action contract remains an explicit independently produced input;
these conditional results are not the completed source Lemma 14.7(b).
Source: GLS4, Chapter 2, Lemma 14.7(b), `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The elementary-quotient argument, with its independent torus-action
input explicit. It uses the actual quotient of M, not an abstract copy. -/
public theorem elementaryQuotient_of_torusQuotientAction
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hK : TorusQuotientAction g)
    (hinv : ∃ a ∈ g.S, a ^ 2 = 1 ∧ a ∉ g.T) : ElementaryQuotient d g := by
  obtain ⟨a, ha, ha2, haT⟩ := hinv
  have hsquare (x : G) (hx : x ∈ g.S) : x ^ 2 ∈ closure (Z ∩ (M : Set G)) := by
    by_cases hxT : x ∈ g.T
    · exact d.T_square_mem g hxT
    obtain ⟨k, hk, he⟩ := hK.transitive a ha haT x hx hxT
    let b := MulAut.conj k a
    have hb : b ∈ g.S := (mem_normalizer_iff.mp (hK.normalizes_S hk) a).mp ha
    have hb2 : b ^ 2 = 1 := by
      change (MulAut.conj k a) ^ 2 = 1
      rw [← map_pow, ha2, map_one]
    have hbT : b ∉ g.T := by
      intro hbT
      apply hxT
      have hh := g.T.mul_mem he hbT
      simpa only [b, inv_mul_cancel_right] using hh
    have hh := d.involution_coset_square_mem g s hb hbT hb2 he
    simpa only [b, inv_mul_cancel_right] using hh
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  let H := (g.S.subgroupOf M).map pi
  have hpow (x : H) : x ^ 2 = 1 := by
    obtain ⟨y, hy, he⟩ := x.property
    apply Subtype.ext
    change (x : M ⧸ A.subgroupOf M) ^ 2 = 1
    rw [← he, ← map_pow]
    exact (QuotientGroup.eq_one_iff (y ^ 2)).mpr (hsquare (y : G) hy)
  have hi (x : H) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow x)
  change IsElementaryAbelian 2 H
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
  }
  intro x y
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

/-- The source Ω₁(S) > Ω₁(T) formulation of the elementary-quotient step. -/
public theorem elementaryQuotient_of_omega_lt_of_torusQuotientAction
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hK : TorusQuotientAction g)
    (hOmega : omegaOneAmbient g.T < omegaOneAmbient g.S) : ElementaryQuotient d g :=
  elementaryQuotient_of_torusQuotientAction d g s hK (g.exists_involution_of_omega_lt hOmega)

/-- Source Lemma 14.7(b), with Ω₁(T) written as its proved product M°U,
and only the separately produced torus action still explicit. -/
public theorem elementaryQuotient_of_omega_product_lt_of_torusQuotientAction
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hK : TorusQuotientAction g)
    (hOmega : closure (Z ∩ (M : Set G)) ⊔ g.U < omegaOneAmbient g.S) :
    ElementaryQuotient d g := by
  apply elementaryQuotient_of_omega_lt_of_torusQuotientAction d g s hK
  rwa [g.omega_T_eq]


end BenderSuzuki.ZD.SuzukiExclusion
