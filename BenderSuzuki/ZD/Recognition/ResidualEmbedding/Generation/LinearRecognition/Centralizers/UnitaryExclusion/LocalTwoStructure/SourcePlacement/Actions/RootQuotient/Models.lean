module

public import Theory.SpecificGroups.SU3.BinaryRootFrattini.Images
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.PairNormalization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Actions.RelativeCore

/-!
# Frattini layers and full two-point tori in genuine unitary covers

Simultaneous pair normalization sends the original Sylow and the literal
B ∩ t⁻¹Bt to the matrix root group and full diagonal torus. The intrinsic
coordinate calculation therefore gives irreducibility on the Frattini
quotient in both SU₃ and PSU₃. Actual cover isomorphisms carry the result
back to the original local group; the odd scalar kernel is never discarded
without the checked Sylow isomorphism.

Source: GLS4, Chapter 4, Lemmas 3.2 and 3.5(a,c), applied in Chapter 2,
Lemma 13.4.
-/

public section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement.RootQuotient
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups HermitianForm
open BinaryRootFrattini PFAppendixIII PFchapter1section1

private theorem charTwo {E : Type*} [Field E] [Finite E] {n : ℕ}
    (hcard : Nat.card E = (2 ^ n) ^ 2) : CharP E 2 := by
  let := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
  simpa [Nat.card_eq_fintype_card, pow_mul] using hcard

section Models
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {n : ℕ} (hn : 2 ≤ n)
  (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hJ hn hcard hfixed in
theorem projective_pair_invariant
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : PFAppendixIII.IsInvolution t)
    (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (W : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hW : W ≤ P)
    (hN : twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ≤
      normalizer (W : Set _)) :
    W ≤ (frattini P).map (P : Subgroup _).subtype ∨ W = P := by
  let : CharP E 2 := charTwo hcard
  obtain ⟨g, hP, _, hD⟩ := PairNormalization.projective_pair J hJ hn hcard hfixed P t ht htB
  apply invariant_transport (MulAut.conj g) (P : Subgroup _) _ ?_ W hW hN
  rw [hP, hD]
  exact projective_invariant_subgroup J hJ hcard hfixed
    (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn))

include hJ hn hcard hfixed in
theorem special_pair_invariant (P : Sylow 2 J.specialSubgroup)
    (t : J.specialSubgroup) (ht : PFAppendixIII.IsInvolution t)
    (htB : t ∉ normalizer (P : Set J.specialSubgroup))
    (W : Subgroup J.specialSubgroup) (hW : W ≤ P)
    (hN : twoPoint (normalizer (P : Set J.specialSubgroup)) t ≤ normalizer (W : Set _)) :
    W ≤ (frattini P).map (P : Subgroup _).subtype ∨ W = P := by
  let : CharP E 2 := charTwo hcard
  obtain ⟨g, hP, _, hD⟩ := PairNormalization.special_pair J hJ hn hcard hfixed P t ht htB
  apply invariant_transport (MulAut.conj g) (P : Subgroup _) _ ?_ W hW hN
  rw [hP, hD]
  exact special_invariant_subgroup J hJ hcard hfixed
    (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn))
end Models

section Covers
variable {H : Type*} [Group H] [Finite H] {n : ℕ}

/-- The Frattini layer in every Sylow subgroup of either genuine unitary cover. -/
theorem cover_sylow_structure (hn : 2 ≤ n) (hc : IsUnitaryCentralizerCoverAt n H)
    (P : Sylow 2 H) :
    (∀ x : P, x ∈ frattini P ↔ x ^ 2 = 1) ∧ frattini P ≤ center P := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hc
  · obtain ⟨e⟩ := he
    let : CharP E 2 := charTwo hcard
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    exact equiv_structure J hcard hfixed
      (((P : Subgroup H).equivMapOfInjective e.toMonoidHom e.injective).trans
        (SylowOmega.projectiveSylowEquivCoords J hn hcard hfixed hJ Q))
  · obtain ⟨e⟩ := he
    let : CharP E 2 := charTwo hcard
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    exact equiv_structure J hcard hfixed
      ((((P : Subgroup H).equivMapOfInjective e.toMonoidHom e.injective).trans
        (SylowOmega.specialSylowEquivProjective J Q)).trans
          (SylowOmega.projectiveSylowEquivCoords J hn hcard hfixed hJ _))

omit [Finite H] in
private theorem twoPoint_map_equiv {K : Type*} [Group K]
    (e : H ≃* K) (B : Subgroup H) (t : H) :
    (twoPoint B t).map e.toMonoidHom = twoPoint (B.map e.toMonoidHom) (e t) := by
  rw [twoPoint, twoPoint, Subgroup.map_inf _ _ _ e.injective]
  congr 1
  simp only [rightConjugate, Subgroup.conjBy, Subgroup.map_map]
  congr 1
  ext x
  simp

private theorem cover_pair_transport {K : Type*} [Group K]
    (e : H ≃* K) (P : Sylow 2 H) (t : H) (ht : PFAppendixIII.IsInvolution t)
    (htB : t ∉ normalizer (P : Set H))
    (hmodel : ∀ (Q : Sylow 2 K) (s : K), PFAppendixIII.IsInvolution s →
      s ∉ normalizer (Q : Set K) → ∀ W : Subgroup K, W ≤ Q →
      twoPoint (normalizer (Q : Set K)) s ≤ normalizer (W : Set K) →
      W ≤ (frattini Q).map (Q : Subgroup K).subtype ∨ W = Q)
    (W : Subgroup H) (hW : W ≤ P)
    (hN : twoPoint (normalizer (P : Set H)) t ≤ normalizer (W : Set H)) :
    W ≤ (frattini P).map (P : Subgroup H).subtype ∨ W = P := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hNQ : (normalizer (P : Set H)).map e.toMonoidHom = normalizer (Q : Set K) :=
    map_equiv_normalizer_eq (P : Subgroup H) e
  have hout : e t ∉ normalizer (Q : Set K) := by
    rw [← hNQ, mem_map_equiv]
    simpa only [e.symm_apply_apply] using htB
  apply invariant_transport e (P : Subgroup H) _ ?_ W hW hN
  rw [twoPoint_map_equiv, hNQ]
  exact hmodel Q (e t)
    ⟨fun he => ht.1 (e.injective (he.trans (map_one e).symm)),
      by rw [← map_pow, ht.2, map_one]⟩ hout

/-- Full two-point torus irreducibility in a group with an actual unitary-cover
isomorphism, with the original Sylow and outside involution. -/
theorem cover_pair_invariant (hn : 2 ≤ n) (hc : IsUnitaryCentralizerCoverAt n H)
    (P : Sylow 2 H) (t : H) (ht : PFAppendixIII.IsInvolution t)
    (htB : t ∉ normalizer (P : Set H))
    (W : Subgroup H) (hW : W ≤ P)
    (hN : twoPoint (normalizer (P : Set H)) t ≤ normalizer (W : Set H)) :
    W ≤ (frattini P).map (P : Subgroup H).subtype ∨ W = P := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hc
  · obtain ⟨e⟩ := he
    exact cover_pair_transport e P t ht htB (projective_pair_invariant J hJ hn hcard hfixed)
      W hW hN
  · obtain ⟨e⟩ := he
    exact cover_pair_transport e P t ht htB (special_pair_invariant J hJ hn hcard hfixed)
      W hW hN
end Covers
end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement.RootQuotient
